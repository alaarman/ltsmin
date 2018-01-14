#include <hre/config.h>

#ifdef __APPLE__
#define _DARWIN_C_SOURCE
#endif

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>

#include <dm/dm.h>
#include <hre/stringindex.h>
#include <hre/user.h>
#include <lts-io/user.h>
#include <pins-lib/pins.h>
#include <pins-lib/pins-impl.h>
#include <pins-lib/pins-util.h>
#include <pins2lts-sym/alg/local.h>
#include <pins2lts-sym/aux/options.h>
#include <pins2lts-sym/aux/output.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <ltsmin-lib/ltsmin-syntax.h>
#include <ltsmin-lib/ltsmin-tl.h>
#include <mc-lib/atomics.h>
#include <mc-lib/bitvector-ll.h>
#include <util-lib/bitset.h>
#include <util-lib/dfs-stack.h>
#include <util-lib/util.h>

static int check_guards = 0;

struct poptOption local_options[] = {
    { "check-guards", 0, POPT_ARG_VAL, &check_guards, 1, "Check guards for absence of MAYBE's.", "" },
    POPT_TABLEEND
};


/**
 * List of "writer groups"
 * Each element in turn is a list of "reader groups", reading from the
 * respective writer group. The slots intersection of the read and write
 * support of the respective groups are also recorded.
 */
typedef struct write_group_s {
    int index;
    int num_readers;
    ci_list    **guard_proj;
    struct reader_group_s {
        int         index; // reader
        ci_list    *slots;
        ci_list    *compl;
        vset_t      w2r;
        vset_t      complement;
    } *readers;
    vset_t      complement;     // to create visited set
} write_group_t;

static write_group_t *writers;

typedef struct reader_group_s reader_t;

static inline write_group_t *
w_bgn()
{
    return &writers[0];
}

static inline write_group_t *
w_end()
{
    return &writers[nGrps];
}

static inline reader_t *
r_bgn(write_group_t *wg)
{
    return &wg->readers[0];
}

static inline reader_t *
r_end(write_group_t *wg)
{
    return &wg->readers[wg->num_readers];
}

static vset_t *V_w;     // visited write
static vset_t *Q_w;     // queue   write
static vset_t *V_r;     // visited read
static vset_t *Q_r;     // queue   read
static vset_t *X_r;     // temp    read
static vset_t *Y_r;     // temp 2  read
static vset_t  X;

static int explored = 0;

typedef struct group_add_s {
    int    group;
    int   *src;
} group_add_t;

ci_list *p_all;

static void
Statef (log_t log, int *state, ci_list *proj)
{
    if (!log_active(log)) return;
    int p = 0;
    for (int l = 0; l < N; l++) {
        if (p < proj->count && proj->data[p] == l) {
            Printf (log, "%2d,", state[p]);
            p++;
        } else {
            Printf (log, " *,");
        }
    }
}

static void
group_add (void *context, transition_info_t *ti, int *dst, int *cpy)
{
    group_add_t        *ctx = (group_add_t *) context;

    vrel_add_cpy (group_next[ctx->group], ctx->src, dst, cpy);
    vset_add (Q_w[ctx->group], dst);
    Statef (debug, ctx->src, r_projs[ctx->group]);
    Printf (debug, " -(%2d)-> ", ctx->group);
    Statef (debug, dst, w_projs[ctx->group]);
    Printf (debug, "\n");
    (void) ti;
}

void
group_add3 (void *context, transition_info_t *ti, int *dst, int *cpy)
{
    group_add_t        *ctx = (group_add_t *) context;

    Statef (debug, ctx->src, p_all);
    Printf (debug, " -(%2d)-> ", ctx->group);
    Statef (debug, dst, p_all);
    Printf (debug, "\n");
    (void) ti; (void) cpy;
}

void
print_state_r (void *context, int *src)
{
    int group = *(int *)context;
    Statef (debug, src, r_projs[group]);
    Printf (debug, " (%d)\n", group);
}

void
print_next_state (void *context, int *src)
{
    group_add_t         ctx;
    ctx.group = *(int *)context;
    ctx.src = src;
    GBgetTransitionsLong (model, ctx.group, src, group_add3, &ctx);
}

static void
explore_cb (void *context, int *src)
{
    group_add_t         ctx;
    ctx.group = *(int *)context;
    ctx.src = src;

    if (check_guards) {
        ci_list *guards = (ci_list *) GBgetGuard (model, ctx.group);
        for (int g = 0; g < ci_count(guards); g++) {
            ci_list *guard_proj = writers[ctx.group].guard_proj[g];

            int src_g[guard_proj->count];
            for (int i = 0; i < guard_proj->count; i++)
                src_g[i] = src[ci_get(guard_proj, i)];
            int eval = GBgetStateLabelShort (model, ci_get(guards, g), src_g);
            HREassert (eval != 2, "ns might be undefined for group %d (guard %d evaluates to MAYBE)", ctx.group, ci_get(guards, g));
        }
    }
    GBgetTransitionsShortR2W (model, ctx.group, src, group_add, &ctx);
    explored++;
}

int
reach_local (vset_t V)
{
    int                 level = 0;
    bool                all_done;

    do {
        level++;
        for (int i = 0; i < nGrps; i++) {
            //write_group_t      *wg = &writers[i];

            vset_clear   (Q_w[i]);
            vset_enum    (Q_r[i], explore_cb, &i);
            vset_union   (V_w[i], Q_w[i]);
            vset_union   (V_r[i], Q_r[i]);
//            if (wg->complement != NULL) {
//                vset_project (wg->complement, V);
//                vset_join    (X, wg->complement, Q_r[i]);
//                vset_clear   (wg->complement);
//                vset_union   (V, X);
//                vset_clear   (X);
//            } else {
//                vset_union   (V, Q_r[i]);
//            }
            vset_clear   (Q_r[i]);
        }

        all_done = true;
        for (int i = 0; i < nGrps; i++) {
            write_group_t *wg = &writers[i];
            for (reader_t *r = r_bgn(wg); r <  r_end(wg); r++) {
                int j = r->index;
                if (r->w2r == NULL) { // writer's domain overlaps reader
                    vset_project (X_r[j], Q_w[i]);
                    vset_minus   (X_r[j], V_r[j]);
                    long n1;
                    long double e1;
                    vset_count_fn (X_r[j], &n1, &e1);
                    if (e1 > 0)
                        Warning (infoLong, "_ X _ === _ --> %.0Lf\t\t%d>%d", e1, i, j);
                    vset_union   (Q_r[j], X_r[j]);
                    vset_clear   (X_r[j]);
                } else {
                    long n1;// n2, n3, n4;
                    long double e1;// e2, e3, e4;
                    vset_project        (r->w2r,        Q_w[i]);
                    vset_count_fn (r->w2r, &n1, &e1);
                    if (e1 != 0) {
                        vset_project        (r->complement, V_r[j]);
                        vset_join   (X_r[j], r->complement, r->w2r);
//                        vset_count_fn (r->tmp, &n1, &e1);
//                        vset_count_fn (r->complement, &n2, &e2);
//                        vset_count_fn (X_r[j], &n3, &e3);
                        vset_minus          (X_r[j],        V_r[j]);
//                        vset_count_fn (X_r[j], &n4, &e4);
//                        if (e4 > 0) {
//                            vset_enum(X_r[j], print_state_r, &j);
//                            Warning (infoLong, "%.0Lf X %.0Lf =%s= %.0Lf --> %.0Lf\t\t%d>%d", e1, e2, e1 * e2 == e3 ? "=" : "!", e3, e4, i, j);
//                        }
                        vset_union          (Q_r[j],        X_r[j]);
                        all_done &= vset_is_empty (X_r[j]);
                        vset_clear (X_r[j]);
                        vset_clear (r->complement);
                    }
                    vset_clear (r->w2r);
                }
            }
        }
        Printf (infoLong, "\n");
        //vset_reorder (domain);

    } while (!all_done);

    return level;
    (void) V;
}

static void
prepare_guards ()
{
    ci_list **guard_r = (ci_list **) dm_rows_to_idx_table (GBgetStateLabelInfo (model));

    // translate guard reads to group read projections
    for (int i = 0; i < nGrps; i++) {
        // all groups i
        write_group_t *wg = &writers[i];
        ci_list *guards = (ci_list*) GBgetGuard (model, i);
        wg->guard_proj = RTmalloc (sizeof(ci_list*[guards->count]));
        for (int *g = ci_begin (guards); g < ci_end (guards); g++) {
            // all g of i
            ci_list* ppg = ci_create (guard_r[*g]->count);
            wg->guard_proj[g - ci_begin (guards)] = ppg;
            Warning (infoLong, "%d", g - ci_begin (guards));
            for (int* s = ci_begin (guard_r[*g]); s < ci_end (guard_r[*g]); s++) {
                // all g dep. slots s
                int index = ci_binary_search (r_projs[i], *s);
                HREassert(index != -1, "Guard %d not included in read projection of group %d.", *g, s);
                ci_add (ppg, index);
            }
        }
    }

    RTfree (guard_r);
}

/**
 * For each group i, this function finds all groups j that read from i's
 * write support. The intersection of read and write support is used
 * as a projection. Together with a projection of the complement
 * (j's read support minus the intersection) this is used to construct
 * all new values for the read inputs using the join call
 * (join is an intersection operation of sets with different projections, that
 *  can also be supported in MDDs).
 */
static void
find_domain_intersections ()
{
    writers = RTmallocZero (sizeof(write_group_t[nGrps]));

    if (check_guards) prepare_guards ();

    /* Collect write group to read group matrix */
    ci_list *(*group_w2r)[nGrps];
    group_w2r = RTmallocZero (sizeof(*group_w2r) * nGrps);
    //ci_list ***group_w2r = RTmallocZero (sizeof(ci_list *[nGrps*nGrps]) + sizeof(ci_list **[nGrps]));

    ci_list **r_cols = (ci_list**) dm_cols_to_idx_table (read_matrix);
    for (int i = 0; i < nGrps; i++) {
        //group_w2r[i] = (ci_list **) &group_w2r[nGrps + i * nGrps];
        // iterate writing slots s for group i
        for (int *s = ci_begin(w_projs[i]); s < ci_end(w_projs[i]); s++) {
            // iterate groups j reading from s
            for (int *j = ci_begin(r_cols[*s]); j < ci_end(r_cols[*s]); j++) {
                ci_list *wt = group_w2r[i][*j];
                if (wt == NULL) {
                    writers[i].num_readers++;
                    group_w2r[i][*j] = wt = ci_create (N);
                }
                ci_add (wt, *s);
            }
        }

        // create read support complement sets (for collecting visited states)
        if (ci_count(r_projs[i]) == 0) {
            writers[i].complement = NULL;
        } else {
            ci_list *compl = ci_create (N - ci_count(r_projs[i]));
//            int *s = ci_begin(r_projs[i]);
            for (int l = 0; l < N; l++) {
//                if (s != ci_end(r_projs[l]) && *s == l) {
//                    s++;
//                } else {
                    ci_add_if (compl, l, ci_binary_search(r_projs[i], l) == -1);
//                }
            }
            writers[i].complement = vset_create (domain, compl->count, compl->data);
            HREassert (ci_count(r_projs[i]) + ci_count(compl) == N);
        }
    }
    RTfree (r_cols);

    /* Collapse matrix into list ( write_group_t[nGrps] ) */
    for (int i = 0; i < nGrps; i++) {
        int c = 0;
        write_group_t *wg = &writers[i];
        wg->index = i;
        wg->readers = RTmallocZero (sizeof(reader_t[wg->num_readers]));
        for (int j = 0; j < nGrps; j++) {
            ci_list *slots = group_w2r[i][j];
            reader_t *r = &wg->readers[c];
            r->index = j;
            if (slots == NULL) continue;
            c++;

            int compl_len = r_projs[j]->count - slots->count;
            HREassert (compl_len >= 0);
            if (compl_len == 0) continue; // writer's domain overlaps reader

            r->slots = slots;
            r->compl = ci_create (compl_len);
            for (int *s = ci_begin(r_projs[j]); s < ci_end(r_projs[j]); s++)
                ci_add_if (r->compl, *s, ci_binary_search(slots, *s) == -1);
            HREassert(ci_count(r->compl) == compl_len);
            r->complement = vset_create (domain, compl_len, r->compl->data);
            r->w2r = vset_create (domain, slots->count, slots->data);
            //ci_free (slots);
        }
        HREassert (c == wg->num_readers);
    }
    RTfree (group_w2r);

    Printf (debug, "\n");
    size_t total = 0;
    for (int j = 0; j < nGrps; j++) {
        for (write_group_t *wg = w_bgn(); wg <  w_end(); wg++) {
            for (reader_t *r = r_bgn(wg); r <  r_end(wg); r++) {
                if (r->index != j) continue;
                if (r->slots == NULL) continue;
                Printf (debug, "%2d X %2d -->\t", wg->index, r->index);
                for (int *s = ci_begin(r->slots); s < ci_end(r->slots); s++) {
                    Printf (debug, "%2d,", *s);
                    total++;
                }
                Printf (debug, "  |  ");
                for (int *s = ci_begin(r->compl); s < ci_end(r->compl); s++) {
                    Printf (debug, "%2d,", *s);
                }
                Printf (debug, "\n");
            }
        }
        Printf (debug, "\n");
    }
    Printf (debug, "\nTotal: %zu\n", total);
}

static void
check_conflict (int i , int j)
{
    //    matrix_t *rw = GBgetDMInfo(model);
    //    int support[nGrps];
    //    int c = 0;
    //    for (int x = 0; x < N; x++) {
    //        support[c] = x;
    //        c += dm_is_set(rw, i, x) || dm_is_set(rw, i, x);
    //    }
    //    vset_t *s = vset_create (domain, c, support);
    //
    matrix_t       *R = GBgetDMInfoRead(model);
    bool            o = false;             // read support of i and j overlap
    for (int *s = ci_begin(r_projs[i]); s < ci_end(r_projs[i]) && !o; s++) {
        o |= dm_is_set (R, j, *s);
    }


    //    reader_t *r;
    //    write_group_t *wg = &writers[i];
    //    for (r = r_bgn(wg); r <  r_end(wg); r++) if (r->index == j) break;
    //

    //    vset_project ();

    vrel_create ();

    vset_

    vrel_set_expand()

    vset_copy (Q_r[i], V_r[i]);
    if (o)
        vset_intersect (Q_r[i], V_r[j]);
    vset_next (Q_w[i], Q_r[i], group_next[i]); // i step

    vset_copy (Q_r[j], V_r[j]);
    vset_intersect (Q_r[j], Q_w[i]);
    vset_next (Q_w[j], Q_r[j], group_next[j]); // j step


    vset_copy (Q_r[j], V_r[j]);
    if (o)
        vset_intersect (Q_r[j], V_r[i]);
    vset_next (V_w[j], Q_r[j], group_next[j]); // i step

    vset_copy (Q_r[i], V_r[i]);
    vset_intersect (Q_r[i], V_w[j]);
    vset_next (V_w[i], Q_r[i], group_next[i]); // j step
}

static void
check_commutativity ()
{
    matrix_t *RW = GBgetDMInfo(model);
    matrix_t dna;
    dm_create (&dna, nGrps, nGrps);
    ci_list **r_cols = (ci_list**) dm_cols_to_idx_table (read_matrix);
    for (int i = 0; i < nGrps; i++) {
        for (int j = i + 1; j < nGrps; j++) {
            for (int *s = ci_begin(w_projs[i]); s < ci_end(w_projs[i]); s++) {
                if (dm_is_set(RW, j, *s)) {
                    if (i == j || check_conflict(i, j)) {
                        dm_set (&dna, i, j);
                        dm_set (&dna, j, i);
                    }
                    break;
                }
            }
        }
    }
}

void
init_local (vset_t I)
{
    if (HREme (HREglobal()) == 0) {
        X = vset_create (domain, -1, NULL);
        Q_r = group_tmp;
        V_r = group_explored;
        V_w = RTmalloc(nGrps * sizeof(vset_t));
        Q_w = RTmalloc(nGrps * sizeof(vset_t));
        X_r = RTmalloc(nGrps * sizeof(vset_t));
        Y_r = RTmalloc(nGrps * sizeof(vset_t));
        for (int i = 0; i < nGrps; i++) {
            V_w[i] = vset_create (domain, w_projs[i]->count, w_projs[i]->data);
            Q_w[i] = vset_create (domain, w_projs[i]->count, w_projs[i]->data);
            X_r[i] = vset_create (domain, r_projs[i]->count, r_projs[i]->data);
            Y_r[i] = vset_create (domain, r_projs[i]->count, r_projs[i]->data);

            vset_project (Q_r[i], I);       // init read queue
            vset_project (V_w[i], I);       // init write visited
        }

        p_all = ci_create (N);
        for (int l = 0; l < N; l++) ci_set (p_all, l, l);

        find_domain_intersections ();
    }

    HREbarrier (HREglobal());
}

void
deinit_local ()
{
    if (HREme (HREglobal()) == 0) {
        vset_destroy (X);
        for (int i = 0; i < nGrps; i++) {
            vset_destroy (V_w[i]);
            vset_destroy (Q_w[i]);
            vset_destroy (X_r[i]);
            vset_destroy (Y_r[i]);
        }
        RTfree (V_w);
        RTfree (Q_w);
        RTfree (X_r);
        RTfree (Y_r);

        ci_free (p_all);

        for (write_group_t *wg = w_bgn(); wg <  w_end(); wg++) {
            for (reader_t *r = r_bgn(wg); r <  r_end(wg); r++) {
                if (r->compl)       ci_free (r->compl);
                if (r->slots)       ci_free (r->slots);
                if (r->complement)  vset_destroy (r->complement);
                if (r->w2r)         vset_destroy (r->w2r);
            }
            RTfree (wg->readers);
            vset_destroy (wg->complement);
        }
        RTfree (writers);

        find_domain_intersections ();
    }
    HREbarrier (HREglobal());
}

void
print_local (vset_t V, int level)
{
    RTprintTimer (info, reach_timer, "Local reach took");
    long int n;
    double e;
    vset_count (V, &n, &e);
    Warning (info, "Local Levels: %d  %.0f", level, e);
}

void
run_local (vset_t I, vset_t V)
{
    Warning (info, "Initiating local component search");

    init_local (I);

    RTstartTimer(reach_timer);
    int level = reach_local (V);
    RTstopTimer(reach_timer);

    print_local (V, level);

    deinit_local ();

    final_final_stats_reporting ();

    RTresetTimer(reach_timer);
}



