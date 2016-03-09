#ifndef TRACE_H
#define TRACE_H

#include <pins-lib/pins.h>

typedef void *(*trc_get_state_f)(void *state, void *arg);
typedef void *(*trc_get_parent_f)(void *state, void *arg);
typedef struct trc_env_s    trc_env_t;

extern trc_env_t *trc_create (model_t model,
                              trc_get_state_f get,
                              trc_get_parent_f get_parent,
                              void *get_state_arg);

extern void trc_write_trace (trc_env_t *env, char *trc_output, void **trace,
                             int level);

extern void trc_find_and_write (trc_env_t *env, char *trc_output, void *dst_idx,
                                int level, void *start_idx, void *ctx);

#endif
