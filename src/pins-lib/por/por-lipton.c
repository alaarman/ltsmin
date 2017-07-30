#include <hre/config.h>

#include <stdlib.h>

#include <dm/dm.h>
#include <hre/feedback.h>
#include <hre/stringindex.h>
#include <hre/unix.h>
#include <hre/user.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <pins-lib/pins.h>
#include <pins-lib/por/por-ample.h>
#include <pins-lib/por/por-deletion.h>
#include <pins-lib/por/por-lipton.h>
#include <pins-lib/por/por-internal.h>
#include <pins-lib/por/pins2pins-por.h>
#include <pins-lib/pins-util.h>
#include <util-lib/bitmultiset.h>
#include <util-lib/dfs-stack.h>
#include <util-lib/util.h>
#include <z3.h>

/**
 * LIPTON reduction
 */

typedef enum {
    COMMUTE_RGHT = 0,
    COMMUTE_LEFT = 1,
    COMMUTE_COUNT = 2,
} commute_e;

char *comm_name[2] = { "right", "left" };

typedef enum {
    PRE__COMMIT = true,
    POST_COMMIT = false
} phase_e;

#define PROC_BITS 10
#define GROUP_BITS 21

#define GROUP_NONE ((1LL<<GROUP_BITS) - 1)

typedef struct  __attribute__((packed)) stack_data_s {
    uint32_t            group : GROUP_BITS;
    uint32_t            proc  : PROC_BITS;
    phase_e             phase : 1;
    int                 state[];
} stack_data_t;

typedef struct search_s search_t;
struct lipton_ctx_s {
    por_context        *por;
    int                 lipton_group;
    process_t          *procs;
    int                *g2p;
    int                *g2pc;
    size_t              nprocs;
    del_ctx_t          *del;        // deletion context
    ci_list           **g_next;     // group --> group [proc internal] (enabling, inv. of NES)
    ci_list           **p_dis;      // group --> process [proc remote] (disabled, NDS)
    ci_list           **not_accord[2];   // to swap out in POR layer, controlling deletion algorithm
    ci_list           **commute[2];
    bms_t              *visible;
    int                 visible_initialized;

    dfs_stack_t         queue[2];
    dfs_stack_t         commit;
    TransitionCB        ucb;
    void               *uctx;
    stack_data_t       *src;
    size_t              emitted;
    size_t              depth;
    bool                commutes_left;
    bool                commutes_right;
    size_t              max_stack;
    size_t              max_depth;
    size_t              avg_stack;
    size_t              avg_depth;
    size_t              states;

    matrix_t            tc;     // group 2 group enablement
    search_t           *s;
    Z3_ast              stubborn_set;
    Z3_solver           solver;
    Z3_context          z3;
    Z3_ast             *B;
    Z3_ast             *E;
    Z3_ast             *G;
    Z3_ast             *P;
};

static inline void
lipton_init_visibles (lipton_ctx_t* lipton, int* src)
{
    if (lipton->visible_initialized) return;
    lipton->visible_initialized = 1;

    por_context        *por = lipton->por;
    por_init_transitions (por->parent, por, src);
    ci_list            *vis = bms_list (por->visible_labels, 0);
    for (int* l = ci_begin (vis); l != ci_end (vis); l++) {
        for (int* g = ci_begin (por->label_nds[*l]);
                        g != ci_end (por->label_nds[*l]); g++) {
            bms_push_new (lipton->visible, COMMUTE_RGHT, *g);
        }
    }
    for (int* l = ci_begin (vis); l != ci_end (vis); l++) {
        for (int* g = ci_begin (por->label_nes[*l]);
                        g != ci_end (por->label_nes[*l]); g++) {
            bms_push_new (lipton->visible, COMMUTE_LEFT, *g);
        }
    }
    Print1 (infoLong, "LIPTON visible groups: %d (right), %d (left) / %d",
            bms_count(lipton->visible, COMMUTE_RGHT), bms_count(lipton->visible, COMMUTE_LEFT), por->nlabels);
    bms_debug_1 (lipton->visible, COMMUTE_RGHT);
    bms_debug_1 (lipton->visible, COMMUTE_LEFT);
    bms_clear_all (por->visible);
    bms_clear_all (por->visible_labels);
}

static inline bool
lipton_comm_static (lipton_ctx_t* lipton, process_t* proc, int group, commute_e comm)
{
    if (comm == COMMUTE_RGHT) {
        return lipton->commute[comm][group]->count == 0;
    } else {
        for (int *g = ci_begin(proc->en); g != ci_end(proc->en); g++)
            if (lipton->commute[comm][group]->count != 0) return false;
        return true;
    }
}

static inline bool
lipton_check_visibility (lipton_ctx_t *lipton, int *src, process_t *proc,
                         int group, commute_e comm)
{
    if (!SAFETY) return false;

    lipton_init_visibles (lipton, src);

    if (comm == COMMUTE_RGHT) {
        return bms_has(lipton->visible, comm, group);
    } else {
        for (int *g = ci_begin (proc->en); g != ci_end (proc->en); g++) {
            if (bms_has(lipton->visible, comm, *g)) return true;
        }
    }
    return false;
}


static const char L_NEW =  0;
static const char L_VIS =  1;
static const char L_ENA =  2;

struct search_s {
    lipton_ctx_t       *lipton;
    char               *v;
    ci_list            *q;
    process_t          *proc;
};

static inline bool
add_queue (search_t *s, int group)
{
    if (s->v[group] == L_ENA) return false; // oops!
    if (s->lipton->g2p[group] == s->proc->id) return true;

    if (s->v[group] == L_NEW) {
        s->v[group] = L_VIS;
        ci_add (s->q, group);
    }
    return true;
}

static inline bool
add_nes (search_t *s, int d)
{
    lipton_ctx_t       *lipton = s->lipton;
    por_context        *por = lipton->por;

    HREassert (lipton->g2p[d] != s->proc->id && s->v[d] == L_VIS);

    int nes = -1;
    int proc = 0;
    int new = INT32_MAX;

    for (int *ns = ci_begin(por->group_has[d]); ns != ci_end(por->group_has[d]); ns++) {
        if ((*ns < por->nguards && (por->label_status[*ns] == 0))  ||
            (*ns >= por->nguards && (por->label_status[*ns-por->nguards] != 0)) ) {

            int procp = 0;
            int newp = 0;

            for (int *g = ci_begin(por->ns[*ns]); g != ci_end(por->ns[*ns]); g++) {

                if (s->v[*g] == L_ENA) {
                    newp = -1;
                    break;
                }
                procp += lipton->g2p[*g] == s->proc->id;
                newp += s->v[*g] == L_NEW;
            }
            if (newp == -1) continue;

            if (newp < new || (newp == new && procp >= proc)) {
                nes = *ns;
                new = newp;
                proc = procp;
            }
        }
    }
    if (nes == -1) {
        return false;
    }

    for (int *g = ci_begin(por->ns[nes]); g != ci_end(por->ns[nes]); g++) {
        add_queue (s, *g);
    }

    return true;
}

static inline bool
add_queue_all (search_t *s, ci_list *C)
{
    for (int *h = ci_begin (C); h != ci_end (C); h++)
        if (!add_queue(s, *h)) return false;
    return true;
}

static bool
lipton_comm_heur (lipton_ctx_t *lipton, int *src, process_t *proc, int group,
                 commute_e comm)
{
    ci_list            *list;

    model_t             model = lipton->por->parent;
    por_context        *por = lipton->por;
    search_t *s = lipton->s;
    memset (s->v, L_NEW, por->ngroups);
    ci_clear (s->q);
    s->proc = proc;
    GBgetStateLabelsGroup (model, GB_SL_GUARDS, src, por->label_status); //TODO

    for (int g = 0; g < por->ngroups; g++) {
        if (lipton->g2p[g] == proc->id) continue;
        bool enabled = true;
        for (int *u = ci_begin(por->group2guard[g]);
                        enabled && u != ci_end(por->group2guard[g]); u++) {
            enabled &= por->label_status[*u];
        }
        if (enabled) s->v[g] = L_ENA;
    }

    if (comm == COMMUTE_RGHT) {
        if (!add_queue_all(s, lipton->not_accord[comm][group])) {
            return false;
        }
    } else {
        for (int *g = ci_begin(proc->en); g != ci_end(proc->en); g++) {
            if (!add_queue_all(s, lipton->not_accord[comm][*g])) {
                return false;
            }
        }
    }

    while (ci_count(s->q) > 0) {
        int g = ci_pop(s->q);
        if (!add_nes(s, g)) return false;
    }

    return true;
}



static bool
lipton_calc_del (lipton_ctx_t *lipton, process_t *proc, int group, commute_e comm)
{
    por_context        *por = lipton->por;

    por->not_left_accordsn = lipton->not_accord[1 - comm];
    del_por (lipton->del, false);
    int                 c = 0;
    Debugf ("LIPTON: DEL checking proc %d group %d (%s)", proc->id, group, comm==COMMUTE_LEFT?"left":"right");
    if (debug) {
        Debugf (" enabled { ");
        for (int *g = ci_begin(proc->en); g != ci_end(proc->en); g++)
            Debugf ("%d, ", *g);
        Debugf ("}\n");
    }
    Debugf ("LIPTON: DEL found: ");
    for (int *g = ci_begin(por->enabled_list); g != ci_end(por->enabled_list); g++) {
        if (lipton->g2p[*g] != proc->id && del_is_stubborn(lipton->del, *g)) {
            Debugf ("%d(%d), ", *g, lipton->g2p[*g]);
            c += 1;
        }
    }
    Debugf (" %s\n-----------------\n", c == 0 ? "REDUCED" : "");

    return c == 0;
    (void) group;
}

/**
 * Calls the deletion algorithm to figure out whether a dependent action is
 * reachable. Dependent is left-dependent in the post-phase and right-dependent
 * in the pre-phase. However, because we check the pre-phase only after the
 * fact (after the execution of the action), we cannot use the algorithm in
 * the normal way. Instead, for the right-depenency check, we fix the
 * dependents directly in the deletion algorithm (instead of the action itself).
 * For left-commutativity, we need to check that all enabled actions commute in
 * non-stubborn futures. Therefore, we fix all enabled actions of the process in
 * that case.
 * The inclusion takes care that the algorithm does not attempt to delete
 * the process' enabled actions.
 */
static bool
lipton_comm_del (lipton_ctx_t *lipton, int *src, process_t *proc, int group,
                 commute_e comm)
{
    ci_list            *list;

    if (comm == COMMUTE_RGHT) {
        list = lipton->por->not_left_accordsn[group];
    } else {
        list = proc->en;
    }

    por_context        *por = lipton->por;
    por_init_transitions (por->parent, por, src);
    bms_clear_all (por->fix);
    bms_clear_all (por->include);
    for (int *g = ci_begin(proc->en); g != ci_end(proc->en); g++)
        bms_push (por->include, 0, *g);
    for (int *g = ci_begin(list); g != ci_end(list); g++)
        bms_push (por->fix, 0, *g);
    return lipton_calc_del (lipton, proc, group, comm);
}

static bool
lipton_comm_sat (lipton_ctx_t *lipton, int *src, process_t *proc, int group,
                 commute_e comm)
{
    Z3_solver_push(lipton->z3, lipton->solver);

    por_context        *por = lipton->por;
    model_t             model = por->parent;
    GBgetStateLabelsGroup (model, GB_SL_GUARDS, src, por->label_status); //TODO
    size_t              total = por->nguards + lipton->nprocs - 1 + 1;
    Z3_ast              conj[total];
    int                 o = 0;
    for (int u = 0; u < por->nguards; u++) {
        conj[u] = por->label_status[u] ? lipton->G[u] : Z3_mk_not(lipton->z3, lipton->G[u]);
    }

    o += por->nguards;
    for (int i = 0; i < lipton->nprocs; i++) {
        if (i != proc->id) {
            conj[i + o] = Z3_mk_not (lipton->z3, lipton->P[i]);
        } else {
            if (comm == COMMUTE_RGHT) {
                conj[i + o] = lipton->B[group];
            } else {
                conj[i + o] = lipton->P[proc->id];
            }
        }
    }
    Z3_ast              and = Z3_mk_and (lipton->z3, total, conj);

    Z3_solver_assert (lipton->z3, lipton->solver, and);

    Z3_lbool sat = Z3_solver_check(lipton->z3, lipton->solver);

    bool res = sat == Z3_L_TRUE;

    Z3_solver_pop(lipton->z3, lipton->solver, 1);

    return res;
}


static inline bool
lipton_comm (lipton_ctx_t* lipton, process_t* proc, int group, int* src, commute_e comm)
{
    if (lipton_check_visibility(lipton, src, proc, group, comm)) return false;
    if (lipton_comm_static(lipton, proc, group, comm)) return true;

    switch (USE_DEL) {
    case 0:  return false;
    case 1:  return lipton_comm_del (lipton, src, proc, group, comm);
    case 2:  return lipton_comm_heur (lipton, src, proc, group, comm);
    case 3:  return lipton_comm_sat (lipton, src, proc, group, comm);
    default: Abort ("Unimplemented: USE_DEL = %d", USE_DEL); return false;
    }
}

static void
lipton_init_proc_enabled (lipton_ctx_t *lipton, int *src, process_t *proc,
                          int g_prev)
{
    por_context        *por = lipton->por;
    ci_clear (proc->en);
    ci_clear (proc->en_pc);
    model_t             model = lipton->por->parent;
    ci_list            *cands = g_prev == GROUP_NONE ? proc->groups : lipton->g_next[g_prev];
    for (int *n = ci_begin(cands); n != ci_end(cands); n++) {
        int                 pc = lipton->g2pc[*n];
        bool                enabled_pc = GBgetStateLabelLong (model, pc, src) != 0;
        bool                enabled = enabled_pc;
        for (int *u = ci_begin(por->group2guard[*n]);
                        enabled && u != ci_end(por->group2guard[*n]); u++) {
            if (*u == pc) continue;
            enabled &= GBgetStateLabelLong (model, *u, src) != 0;
        }
        ci_add_if (proc->en, *n, enabled);
        ci_add_if (proc->en_pc, *n, !enabled && enabled_pc);
    }
    if (debug && g_prev != GROUP_NONE) {
        int                 count = 0;
        for (int *n = ci_begin(proc->groups); n != ci_end(proc->groups); n++) {
            guard_t            *gs = GBgetGuard (lipton->por->parent, *n);
            HREassert(gs != NULL, "GUARD RETURNED NULL %d", *n);
            int                enabled = 1;
            for (int j = 0; enabled && j < gs->count; j++)
                enabled &= GBgetStateLabelLong (model, gs->guard[j], src) != 0;
            if (enabled) HREassert (*n == proc->en->data[count++]);
        }
        HREassert (count == proc->en->count);
    }
}

static inline stack_data_t *
lipton_stack (lipton_ctx_t *lipton, dfs_stack_t q, int *dst, int proc,
              phase_e phase, int group)
{
    HREassert (group == GROUP_NONE || group < lipton->por->ngroups);
    stack_data_t       *data = (stack_data_t*) dfs_stack_push (q, NULL);
    memcpy (&data->state, dst, sizeof(int[lipton->por->nslots]));
    data->group = group;
    data->proc = proc;
    data->phase = phase;
    return data;
}

static inline void
lipton_cb (void *context, transition_info_t *ti, int *dst, int *cpy)
{
    // TODO: ti->group, cpy, labels (also in leaping)
    lipton_ctx_t       *lipton = (lipton_ctx_t*) context;
    phase_e             phase = lipton->src->phase;
    int                 proc = lipton->src->proc;
    lipton_stack (lipton, lipton->queue[1], dst, proc, phase, ti->group);
    (void) cpy;
}

void
lipton_emit_one (lipton_ctx_t *lipton, int *dst, int group)
{
    group = lipton->depth == 1 ? group : lipton->lipton_group;
    transition_info_t       ti = GB_TI (NULL, group);
    ti.por_proviso = 1; // force proviso true
    lipton->ucb (lipton->uctx, &ti, dst, NULL);
    lipton->emitted += 1;
}

static bool //FIX: return values (N, seen, new)
lipton_gen_succs (lipton_ctx_t *lipton, stack_data_t *state)
{
    por_context        *por = lipton->por;
    int                 group = state->group; // Keep variables off of the recursive stack
    int                 phase = state->phase;
    int                *src = state->state;
    process_t          *proc = &lipton->procs[state->proc];

    if (CHECK_SEEN && lipton->depth != 0 && por_seen(src, group, true)) {
        lipton_emit_one (lipton, src, group);
        return false;
    }

//    int                 seen = fset_find (proc->fset, NULL, src, NULL, true);
//    HREassert (seen != FSET_FULL, "Table full");
//    if (seen) return false;
    lipton_init_proc_enabled (lipton, src, proc, group);

    if (phase == POST_COMMIT || proc->en->count == 0) {  // avoid re-emition of external start state:
        //if (proc->en->count == 0 || fset_find(proc->fset, NULL, state, NULL, true) ) {
        if (lipton->depth != 0) lipton_emit_one (lipton, src, group);
        return false;
    }

    if (lipton->depth != 0 && phase == PRE__COMMIT &&
                                !lipton_comm(lipton, proc, group, src, COMMUTE_RGHT)) {
        phase = state->phase = POST_COMMIT;
    }

    if (proc->en->count == 0) {  // avoid re-emition of external start state:
        if (lipton->depth != 0 && phase == POST_COMMIT) lipton_emit_one (lipton, src, group);
        return false;
    }

    if (phase == POST_COMMIT && !lipton_comm(lipton, proc, group, src, COMMUTE_LEFT)) {
        lipton_emit_one (lipton, src, group);
        return false;
    }

    lipton->src = state;
    for (int *g = ci_begin (proc->en); g != ci_end (proc->en); g++) {
        ci_add (proc->succs, *g);
        GBgetTransitionsLong (por->parent, *g, src, lipton_cb, lipton);
    }

    return true;
}

static void
lipton_bfs (lipton_ctx_t *lipton) // RECURSIVE
{
    void               *s;
    while (dfs_stack_size(lipton->queue[1])) {
        swap (lipton->queue[0], lipton->queue[1]);
        lipton->depth++;
        lipton->max_stack = max (lipton->max_stack, dfs_stack_size(lipton->queue[0]));
        lipton->max_depth = max (lipton->max_depth, lipton->depth);
        while ((s = dfs_stack_pop (lipton->queue[0]))) {
            stack_data_t *state = (stack_data_t *) s;
            process_t          *proc = &lipton->procs[state->proc];
            if (fset_find(proc->fset, NULL, state->state, NULL, true)) {
                if (state->phase == POST_COMMIT) {
                    HREassert (state->group != GROUP_NONE);
                    lipton_emit_one (lipton, state->state, state->group);
                }
            } else {
                lipton_gen_succs (lipton, state);
            }
        }
    }
}

static inline int
lipton_lipton (por_context *por, int *src)
{
    lipton_ctx_t           *lipton = (lipton_ctx_t *) por->alg;
    HREassert (dfs_stack_size(lipton->queue[0]) == 0 &&
               dfs_stack_size(lipton->queue[1]) == 0 &&
               dfs_stack_size(lipton->commit  ) == 0);

    stack_data_t           *state = lipton_stack (lipton, lipton->queue[0], src,
                                                  0, PRE__COMMIT, GROUP_NONE);
    lipton->depth = 0;
    for (size_t i = 0; i < lipton->nprocs; i++) {
        fset_clear (lipton->procs[i].fset);
        state->proc = i;
        ci_clear (lipton->procs[i].succs);
        lipton_gen_succs (lipton, state);
    }
    dfs_stack_pop (lipton->queue[0]);

    lipton->emitted = 0;
    size_t max_stack = lipton->max_stack;
    size_t max_depth = lipton->max_depth;
    lipton->max_stack = 0;
    lipton->max_depth = 0;
    lipton_bfs (lipton);
    lipton->avg_stack += lipton->max_stack;
    lipton->avg_depth += lipton->max_depth;
    lipton->max_stack = max (lipton->max_stack, max_stack);
    lipton->max_depth = max (lipton->max_depth, max_depth);

#ifdef LTSMIN_DEBUG
    for (size_t i = 0; i < lipton->nprocs; i++) {
        Debugf ("Transaction of process %d: ", i);
        process_t          *proc = &lipton->procs[i];
        for (int *g = ci_begin (proc->succs); g != ci_end (proc->succs); g++) {
            Debugf ("%d,", *g);
        }
        Debugf ("\n");
    }
#endif

    return lipton->emitted;
}

static void
lipton_setup (model_t model, por_context *por, TransitionCB ucb, void *uctx)
{
    HREassert (bms_count(por->exclude, 0) == 0, "Not implemented for Lipton reduction.");
//    HREassert (bms_count(por->include, 0) == 0, "Not implemented for Lipton reduction.");

    lipton_ctx_t       *lipton = (lipton_ctx_t *) por->alg;

    lipton->states++;
    lipton->ucb = ucb;
    lipton->uctx = uctx;
    (void) model;
}

int
lipton_por_all (model_t model, int *src, TransitionCB ucb, void *uctx)
{
    por_context *por = ((por_context*)GBgetContext(model));
    lipton_setup (model, por, ucb, uctx);
    return lipton_lipton (por, src);
}

lipton_ctx_t *
lipton_create (por_context *por, model_t pormodel)
{
    HRE_ASSERT (GROUP_BITS + PROC_BITS + 1 == 32);
    HREassert (por->ngroups < (1LL << GROUP_BITS) - 1, // minus GROUP_NONE
               "Lipton reduction does not support more than 2^%d-1 groups", GROUP_BITS);
    HREassert (PINS_LTL == PINS_LTL_AUTO, "LTL currently not supported in Lipton reduction.");

    lipton_ctx_t *lipton = RTmalloc (sizeof(lipton_ctx_t));
    lipton->s = RTmalloc (sizeof(search_t));
    lipton->s->q = ci_create (por->ngroups);
    lipton->s->v = RTmalloc (por->ngroups);
    lipton->s->lipton = lipton;

    // find processes:
    lipton->g2p = RTmallocZero (sizeof(int[por->ngroups]));
    lipton->g2pc = RTmallocZero (sizeof(int[por->ngroups]));
    lipton->procs = identify_procs (por, &lipton->nprocs, lipton->g2p, lipton->g2pc);
    if (lipton->procs == NULL)
        Abort ("Undefined PC identification criteria for current frontend");
    lipton->queue[0] = dfs_stack_create (por->nslots + INT_SIZE(sizeof(stack_data_t)));
    lipton->queue[1] = dfs_stack_create (por->nslots + INT_SIZE(sizeof(stack_data_t)));
    lipton->commit   = dfs_stack_create (por->nslots + INT_SIZE(sizeof(stack_data_t)));
    lipton->por = por;
    for (size_t i = 0; i < lipton->nprocs; i++) {
        //lipton->procs[i].fset = fset_create (sizeof(int[por->nslots]), 0, 4, 10);
    }
    if (USE_DEL) {
        lipton->del = del_create (por);
    }

    leap_add_leap_group (pormodel, por->parent);
    lipton->lipton_group = por->ngroups;
    lipton->max_stack = 0;
    lipton->max_depth = 0;
    lipton->avg_stack = 0;
    lipton->avg_depth = 0;
    lipton->states = 0;

    HREassert (lipton->nprocs < (1ULL << PROC_BITS));
    lipton->visible_initialized = 0;
    lipton->visible = bms_create (por->ngroups, COMMUTE_COUNT);

    matrix_t            tmp;
    dm_create (&tmp, por->ngroups, por->ngroups);
    for (int g = 0; g < por->ngroups; g++) {
        for (int h = 0; h < por->ngroups; h++) {
            if (lipton->g2p[g] == lipton->g2p[h]) continue;
            if (dm_is_set(por->nla, g, h)) {
                dm_set (&tmp, g, h); // self-enablement isn't captured in NES
            }
        }
    }
    lipton->not_accord[COMMUTE_LEFT] = (ci_list **) dm_rows_to_idx_table (&tmp); // not need to remove local transitions
    lipton->not_accord[COMMUTE_RGHT] = (ci_list **) dm_cols_to_idx_table (&tmp); // not need to remove local transitions
    dm_free (&tmp);

    matrix_t            nes;
    dm_create (&nes, por->ngroups, por->ngroups);
    for (int g = 0; g < por->ngroups; g++) {
        int             i = lipton->g2p[g];
        process_t      *p = &lipton->procs[i];
        int             u1 = lipton->g2pc[g];
        for (int *h = ci_begin(p->groups); h != ci_end(p->groups); h++) {
            int             u2 = lipton->g2pc[*h];
            if (dm_is_set(&por->label_nes_matrix, u2, g)) {
                dm_set (&nes, g, *h);
            }
            if (!dm_is_set(&por->gnce_matrix, u1, u2)) {
                dm_set (&nes, g, *h); // self-enablement isn't captured in NES
            }
        }
    }
    lipton->g_next = (ci_list **) dm_rows_to_idx_table (&nes);

    Printf1 (infoLong, "Group --> next:\n");
    for (process_t *p = &lipton->procs[0]; p != &lipton->procs[lipton->nprocs]; p++) {

        p->fset = fset_create (sizeof(int[por->nslots]), 0, 4, 10);

        Printf1 (infoLong, "%3d:\n", p->id);
        for (int *h = ci_begin(p->groups); h != ci_end(p->groups); h++) {
            Printf1 (infoLong, "%3d->", *h);
            for (int *g = ci_begin(lipton->g_next[*h]); g != ci_end(lipton->g_next[*h]); g++) {
                Printf1 (infoLong, "%3d,", *g);
            }
            Printf1 (infoLong, "\n");
        }
        Printf1 (infoLong, "\n\n");
    }


    dm_create (&lipton->tc, por->ngroups, por->ngroups);
    dm_copy (&nes, &lipton->tc);
    dm_tc (&lipton->tc);

    ci_list **tc = (ci_list **) dm_rows_to_idx_table (&lipton->tc);
    Printf1 (infoLong, "Group --> tc:\n");
    for (process_t *p = &lipton->procs[0]; p != &lipton->procs[lipton->nprocs]; p++) {
        Printf1 (infoLong, "%3d:\n", p->id);
        for (int *h = ci_begin(p->groups); h != ci_end(p->groups); h++) {
            Printf1 (infoLong, "%3d->", *h);
            for (int *g = ci_begin(tc[*h]); g != ci_end(tc[*h]); g++) {
                Printf1 (infoLong, "%3d%s,", *g, lipton->g2p[*h] != lipton->g2p[*g] ? "*" : "");
            }
            Printf1 (infoLong, "\n");
        }
        Printf1 (infoLong, "\n\n");
    }
    RTfree(tc);

    ci_list **test = (ci_list **) dm_rows_to_idx_table (&nes);
    for (int i = 0; i < por->ngroups; i++)
        HREassert (test[i]->count <= lipton->procs[lipton->g2p[i]].groups->count);
    RTfree(test);
    dm_free (&nes);

    matrix_t            nds;
    dm_create (&nds, por->ngroups, por->ngroups);
    for (size_t g = 0; g < (size_t) por->ngroups; g++) {
        size_t              i = lipton->g2p[g];
        for (size_t j = 0; j < lipton->nprocs; j++) {
            if (i == j) continue;
            process_t          *o = &lipton->procs[j];
            for (int *h = ci_begin(o->groups); h != ci_end(o->groups); h++) {
                if (guard_of(por, g, &por->label_nds_matrix, *h)) {
                    dm_set (&nds, g, j);
                    break;
                }
            }
        }
    }
    lipton->p_dis = (ci_list **) dm_rows_to_idx_table (&nds);
    dm_free (&nds);

    matrix_t p_left_dep;
    matrix_t p_rght_dep;
    dm_create (&p_left_dep, por->ngroups, por->ngroups);
    dm_create (&p_rght_dep, por->ngroups, por->ngroups);
    for (size_t g = 0; g < (size_t) por->ngroups; g++) {
        size_t              i = lipton->g2p[g];
        for (size_t j = 0; j < lipton->nprocs; j++) {
            if (TR_MODE == 0 && i == j) continue;
            process_t          *o = &lipton->procs[j];
            int                 d = 0;
            for (int *h = ci_begin(o->groups); d != 3 && h != ci_end(o->groups); h++) {
                if (dm_is_set(por->nla, g, *h)) {
                    dm_set (&p_left_dep, g, j); d |= 1;
                }
                if (dm_is_set(por->nla, *h, g)) {
                    dm_set (&p_rght_dep, g, j); d |= 2;
                }
            }
        }
    }
    lipton->commute[COMMUTE_LEFT] = (ci_list**) dm_rows_to_idx_table (&p_left_dep);
    lipton->commute[COMMUTE_RGHT] = (ci_list**) dm_rows_to_idx_table (&p_rght_dep);

    Printf1(infoLong, "Process --> Left Conflict groups:\n");
    for (size_t i = 0; i < lipton->nprocs; i++) {
        Printf1(infoLong, "%3zu: ", i);
        for (int g = 0; g < por->ngroups; g++) {
            for (int *o = ci_begin(lipton->commute[COMMUTE_LEFT][g]);
                      o != ci_end(lipton->commute[COMMUTE_LEFT][g]); o++) {
                if (*o == (int) i) {
                    Printf1(infoLong, "%3d,", g);
                }
            }
        }
        Printf1(infoLong, "\n");
    }
    Printf1(infoLong, "Process --> Right Conflict groups:\n");
    for (size_t i = 0; i < lipton->nprocs; i++) {
        Printf1(infoLong, "%3zu: ", i);
        for (int g = 0; g < por->ngroups; g++) {
            for (int *o = ci_begin(lipton->commute[COMMUTE_RGHT][g]);
                      o != ci_end(lipton->commute[COMMUTE_RGHT][g]); o++) {
                if (*o == (int) i) {
                    Printf1(infoLong, "%3d,", g);
                }
            }
        }
        Printf1(infoLong, "\n");
    }
    dm_free (&p_left_dep);
    dm_free (&p_rght_dep);

    Z3_config cfg  = Z3_mk_config();;
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);

    int             o = 0;
    Z3_ast          *B = lipton->B = RTmalloc (sizeof(Z3_ast[por->ngroups]));
    Z3_ast          *E = lipton->E = RTmalloc (sizeof(Z3_ast[por->ngroups]));
    Z3_ast          *G = lipton->G = RTmalloc (sizeof(Z3_ast[por->nguards]));
    Z3_ast          *P = lipton->P = RTmalloc (sizeof(Z3_ast[lipton->nprocs]));
    for (int g = 0; g < por->ngroups; g++) {
        B[g] = Z3_mk_const(ctx, Z3_mk_int_symbol(ctx, g), bool_sort);
    }
    o += por->ngroups;
    for (int g = 0; g < por->ngroups; g++) {
        E[g] = Z3_mk_const(ctx, Z3_mk_int_symbol(ctx, g + o), bool_sort);
    }
    o += por->ngroups;
    for (int u = 0; u < por->nguards; u++) {
        G[u] = Z3_mk_const (ctx, Z3_mk_int_symbol(ctx, u + o), bool_sort);
    }
    o += por->nguards;
    for (int i = 0; i < lipton->nprocs; i++) {
        P[i] = Z3_mk_const (ctx, Z3_mk_int_symbol(ctx, i + o), bool_sort);
    }
    o += lipton->nprocs;

    o = 0;
    size_t          total = 3 * por->ngroups + 2 * lipton->nprocs;
    Z3_ast          stubborn_set[total];
    for (int g = 0; g < por->ngroups; g++) {
        Z3_ast          conj[por->group2guard[g]->count];
        for (int i = 0; i < por->group2guard[g]->count; i++)
            conj[i] = G[ por->group2guard[g]->data[i] ];
        Z3_ast          and = Z3_mk_and (ctx, por->group2guard[g]->count, conj);
        stubborn_set[g + o] = Z3_mk_iff (ctx, E[g], and);
    }

    o += por->ngroups;
    ci_list **nla = lipton->not_accord[COMMUTE_LEFT];
    for (int g = 0; g < por->ngroups; g++) {
        Z3_ast          two[2] = { E[g], B[g] };
        Z3_ast          and = Z3_mk_and (ctx, 2, two);

        Z3_ast          conj[nla[g]->count];
        for (int i = 0; i < nla[g]->count; i++)
            conj[i] = B[ nla[g]->data[i] ];
        Z3_ast          and2 = Z3_mk_and (ctx, nla[g]->count, conj);
        stubborn_set[g + o] = Z3_mk_implies (ctx, and, and2);
    }

    o += por->ngroups;
    ci_list **ns = por->label_nes;
    for (int g = 0; g < por->ngroups; g++) {
        Z3_ast          not = Z3_mk_not (ctx, E[g]);
        Z3_ast          two[2] = { not, B[g] };
        Z3_ast          and = Z3_mk_and (ctx, 2, two);

        Z3_ast          disj[por->group2guard[g]->count];
        for (int i = 0; i < por->group2guard[g]->count; i++) {
            int             u = por->group2guard[g]->data[i];

            Z3_ast          conj[ ns[u]->count + 1 ];
            for (int j = 0; j < ns[u]->count; j++)
                  conj[j] = B[ ns[u]->data[j] ];
            conj[ns[u]->count] = Z3_mk_not (ctx, G[u]);
            disj[i] = Z3_mk_and (ctx, ns[u]->count + 1, conj);
        }
        Z3_ast          or = Z3_mk_or (ctx, por->group2guard[g]->count, disj);

        stubborn_set[g + o] = Z3_mk_implies (ctx, and, or);
    }

    o += por->ngroups;
    for (int i = 0; i < lipton->nprocs; i++) {
        Z3_ast          not = Z3_mk_not (ctx, P[i]);

        process_t      *proc = &lipton->procs[i];
        Z3_ast          conj[proc->groups->count];
        for (int j = 0; j < proc->groups->count; j++) {
            int             g = proc->groups->data[j];
            Z3_ast          two[2] = { E[g], B[g] };
            Z3_ast          and = Z3_mk_and (ctx, 2, two);
            conj[j] = Z3_mk_not (ctx, and);
        }
        Z3_ast          and = Z3_mk_and (ctx, proc->groups->count, conj);

        stubborn_set[(i << 1) + o] = Z3_mk_implies (ctx, not, and);

        for (int j = 0; j < proc->groups->count; j++) {
            int             g = proc->groups->data[j];
            conj[j] = Z3_mk_implies (ctx, E[g], B[g]);
        }
        Z3_ast          and2 = Z3_mk_and (ctx, proc->groups->count, conj);

        stubborn_set[(i << 1) + o + 1] = Z3_mk_implies (ctx, P[i], and2);
    }
    o += 2 * lipton->nprocs;
    lipton->stubborn_set = Z3_mk_and (ctx, total, stubborn_set);

    lipton->solver = Z3_mk_solver (ctx);
    lipton->z3 = ctx;
    Z3_solver_assert (ctx, lipton->solver, lipton->stubborn_set);

    return lipton;
}

bool
lipton_is_stubborn (por_context *ctx, int group)
{
    HREassert(false, "Unimplemented for Lipton reduction");
    (void) ctx; (void) group;
    return false;
}

void
lipton_stats (model_t model)
{
    por_context        *por = ((por_context*)GBgetContext(model));
    lipton_ctx_t       *lipton = (lipton_ctx_t *) por->alg;
    Warning (info, "LIPTON step size %zu max / %.3f avg, queues %zu max / %.3f avg",
             lipton->max_depth, (float)(lipton->avg_depth / lipton->states),
             lipton->max_stack, (float)(lipton->avg_stack / lipton->states))
}

