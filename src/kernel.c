/* Variables and kernels. A kernel is an expression the rational-function arithmetic cannot look inside, such as
 * sin(x), exp(x + 1), an undefined f(x), or an irrational number met together with variables (sqrt(2) in
 * sqrt(2)*x). Each kernel is one more generator of the polynomial ring, so 2*sin(x) + sin(x) is 3*sin(x) by
 * ordinary arithmetic, and diff, subs and N look through it to its head and arguments. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

ca_ctx_t am_ca;
fmpz_mpoly_ctx_t am_mp;
const char *am_varnames[AM_MAXVARS];
AmVar am_vars[AM_MAXVARS];
int am_nvars;

void am_init(void) {
    ca_ctx_init(am_ca);
    fmpz_mpoly_ctx_init(am_mp, AM_MAXVARS, ORD_DEGREVLEX);
    static char unused[AM_MAXVARS][8];
    for (int i = 0; i < AM_MAXVARS; i++) { snprintf(unused[i], sizeof unused[i], "_v%d", i); am_varnames[i] = unused[i]; }
    am_load_library();
}

static int find(const char *name, size_t len) {
    for (int i = 0; i < am_nvars; i++) if (strlen(am_varnames[i]) == len && !strncmp(am_varnames[i], name, len)) return i;
    return -1;
}

static int add(const char *name, size_t len) {
    if (am_nvars == AM_MAXVARS) am_fail("more than %d variables and function terms in use", AM_MAXVARS);
    char *s = malloc(len + 1); memcpy(s, name, len); s[len] = 0;
    am_varnames[am_nvars] = s;
    memset(&am_vars[am_nvars], 0, sizeof am_vars[0]);
    am_vars[am_nvars].name = s;
    return am_nvars++;
}

int am_var_index(const char *name, size_t len) {
    int i = find(name, len);
    return i >= 0 ? i : add(name, len);
}

Value *am_gen(int i) {
    Value *g = v_rf();
    fmpz_mpoly_gen(fmpz_mpoly_q_numref(g->rf), i, am_mp);
    fmpz_mpoly_one(fmpz_mpoly_q_denref(g->rf), am_mp);
    return g;
}

/* the generator a value is exactly, or -1 */
int am_gen_of(const Value *v) {
    if (v->kind != V_RF || !fmpz_mpoly_is_one(fmpz_mpoly_q_denref(v->rf), am_mp)) return -1;
    for (int i = 0; i < am_nvars; i++) if (fmpz_mpoly_is_gen(fmpz_mpoly_q_numref(v->rf), i, am_mp)) return i;
    return -1;
}

/* head(args) as a kernel: its generator */
Value *am_kernel_value(const char *head, Value **args, int n) {
    size_t cap = strlen(head) + 4;
    char **s = malloc((size_t)(n ? n : 1) * sizeof *s);
    for (int i = 0; i < n; i++) { s[i] = v_str_of(args[i]); cap += strlen(s[i]) + 2; }
    char *name = malloc(cap);
    char *o = name + sprintf(name, "%s(", head);
    for (int i = 0; i < n; i++) o += sprintf(o, "%s%s", i ? ", " : "", s[i]);
    sprintf(o, ")");
    for (int i = 0; i < n; i++) free(s[i]);
    free(s);
    int k = find(name, strlen(name));
    if (k < 0) {
        k = add(name, strlen(name));
        am_vars[k].kernel = 1;
        am_vars[k].head = strdup(head);
        am_vars[k].nargs = n;
        am_vars[k].args = malloc((size_t)(n ? n : 1) * sizeof(Value *));
        for (int i = 0; i < n; i++) { am_vars[k].args[i] = v_copy(args[i]); am_pool_keep(am_vars[k].args[i]); }
    }
    free(name);
    return am_gen(k);
}

/* an irrational number met together with variables */
Value *am_number_kernel(const Value *num) {
    char *name = v_str_of(num);
    int k = find(name, strlen(name));
    if (k < 0) {
        k = add(name, strlen(name));
        am_vars[k].kernel = 1;
        am_vars[k].numval = v_copy(num);
        am_pool_keep(am_vars[k].numval);
    }
    free(name);
    return am_gen(k);
}
