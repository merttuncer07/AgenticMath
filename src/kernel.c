/* Variables and kernels. A kernel is an expression the rational-function arithmetic cannot look inside, such as
 * sin(x), exp(x + 1), an undefined f(x), or an irrational number met together with variables (sqrt(2) in
 * sqrt(2)*x). Each kernel is one more generator of the polynomial ring, so 2*sin(x) + sin(x) is 3*sin(x) by
 * ordinary arithmetic, and diff, subs and N look through it to its head and arguments. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/qqbar.h>
#include <flint/fmpz_factor.h>
#include <flint/acb.h>

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

static int is_free[AM_MAXVARS];                                /* a slot given back by am_collect_vars */

static int find(const char *name, size_t len) {
    for (int i = 0; i < am_nvars; i++) if (!is_free[i] && strlen(am_varnames[i]) == len && !strncmp(am_varnames[i], name, len)) return i;
    return -1;
}

static int add(const char *name, size_t len) {
    int k = -1;
    for (int i = 0; i < am_nvars && k < 0; i++) if (is_free[i]) k = i;
    if (k < 0) {
        if (am_nvars == AM_MAXVARS) am_fail("more than %d variables and function terms in use in one statement", AM_MAXVARS);
        k = am_nvars++;
    }
    char *s = malloc(len + 1); memcpy(s, name, len); s[len] = 0;
    am_varnames[k] = s;
    memset(&am_vars[k], 0, sizeof am_vars[0]);
    am_vars[k].name = s;
    is_free[k] = 0;
    return k;
}

/* mark the generators a value uses, and through function terms the ones their arguments use */
static void mark(const Value *v, int *live) {
    if (!v) return;
    if (v->kind == V_LIST || v->kind == V_EQ) { for (int i = 0; i < v->n; i++) mark(v->items[i], live); return; }
    if (v->kind != V_RF) return;
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    for (int i = 0; i < am_nvars; i++)
        if (used[i] && !live[i]) {
            live[i] = 1;
            for (int j = 0; j < am_vars[i].nargs; j++) mark(am_vars[i].args[j], live);
        }
}

/* after a statement: give back the slots of variables and function terms that no named value uses */
void am_collect_vars(Value **keep, int nkeep) {
    int live[AM_MAXVARS] = {0};
    for (int i = 0; i < nkeep; i++) mark(keep[i], live);
    for (int i = 0; i < am_nvars; i++) {
        if (live[i] || is_free[i]) continue;
        is_free[i] = 1;
        static char unused[AM_MAXVARS][8];
        snprintf(unused[i], sizeof unused[i], "_v%d", i);
        free(am_vars[i].name);
        free(am_vars[i].head);
        free(am_vars[i].args);                                 /* the argument values themselves stay (kept) */
        memset(&am_vars[i], 0, sizeof am_vars[0]);
        am_varnames[i] = unused[i];
    }
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

/* exp(c*log(b)) is written b^c: the name only, the value is the same */
static char *power_name(Value *u) {
    if (u->kind != V_RF) return NULL;
    int used[AM_MAXVARS] = {0}, lg = -1;
    fmpz_mpoly_q_used_vars(used, u->rf, am_mp);
    for (int i = 0; i < am_nvars; i++)
        if (used[i] && am_vars[i].head && !strcmp(am_vars[i].head, "log") && am_vars[i].nargs == 1) { if (lg >= 0) return NULL; lg = i; }
    if (lg < 0) return NULL;
    Value *c = v_div(u, am_gen(lg));
    if (!am_free_of(c, lg)) return NULL;
    Value *b = am_vars[lg].args[0];
    char *bs = v_str_of(b), *cs = v_str_of(c);
    int bpar = bs[0] == '-' || strchr(bs, '/') || strchr(bs, ' ') || strchr(bs, '*') || strchr(bs, '^');
    int cpar = strchr(cs, ' ') || strchr(cs, '/') || strchr(cs, '*') || cs[0] == '-';
    char *name = malloc(strlen(bs) + strlen(cs) + 8);
    sprintf(name, bpar ? (cpar ? "(%s)^(%s)" : "(%s)^%s") : (cpar ? "%s^(%s)" : "%s^%s"), bs, cs);
    free(bs); free(cs);
    return name;
}

/* an existing function term with this head and these arguments (whatever its display name) */
static int find_term(const char *head, Value **args, int n) {
    for (int i = 0; i < am_nvars; i++) {
        if (!am_vars[i].kernel || !am_vars[i].head || strcmp(am_vars[i].head, head) || am_vars[i].nargs != n) continue;
        int same = 1;
        for (int j = 0; j < n && same; j++) {
            char *a = v_str_of(am_vars[i].args[j]), *b = v_str_of(args[j]);
            same = !strcmp(a, b);
            free(a); free(b);
        }
        if (same) return i;
    }
    return -1;
}

/* head(args) as a kernel: its generator */
Value *am_kernel_value(const char *head, Value **args, int n) {
    { int t = find_term(head, args, n); if (t >= 0) return am_gen(t); }
    if (!strcmp(head, "exp") && n == 1 && args[0]->kind == V_RF) {     /* exp((e + m) log b) = b^m b^e */
        int used[AM_MAXVARS] = {0}, lg = -1, two = 0;
        fmpz_mpoly_q_used_vars(used, args[0]->rf, am_mp);
        for (int i = 0; i < am_nvars; i++)
            if (used[i] && am_vars[i].head && !strcmp(am_vars[i].head, "log") && am_vars[i].nargs == 1) { if (lg >= 0) two = 1; lg = i; }
        if (lg >= 0 && !two) {
            Value *c = v_div(args[0], am_gen(lg));
            if (am_free_of(c, lg) && c->kind == V_RF && fmpz_mpoly_is_fmpz(fmpz_mpoly_q_denref(c->rf), am_mp)) {
                ulong zero[AM_MAXVARS] = {0};
                fmpz_t a, d; fmpz_init(a); fmpz_init(d);
                fmpz_mpoly_get_coeff_fmpz_ui(a, fmpz_mpoly_q_numref(c->rf), zero, am_mp);
                fmpz_mpoly_get_coeff_fmpz_ui(d, fmpz_mpoly_q_denref(c->rf), zero, am_mp);
                fmpz_fdiv_q(a, a, d);
                int shift = !fmpz_is_zero(a);
                fmpz_clear(a); fmpz_clear(d);
                if (shift) return am_power_kernel(am_vars[lg].args[0], c);
            }
        }
    }
    if (!strcmp(head, "exp") && n == 1) {
        char *pn = power_name(args[0]);
        if (pn) {
            int k = find(pn, strlen(pn));
            if (k < 0) {
                k = add(pn, strlen(pn));
                am_vars[k].kernel = 1; am_vars[k].head = strdup("exp"); am_vars[k].nargs = 1;
                am_vars[k].args = malloc(sizeof(Value *));
                am_vars[k].args[0] = v_copy(args[0]); am_pool_keep(am_vars[k].args[0]);
            }
            free(pn);
            return am_gen(k);
        }
    }
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

/* sqrt(D) (D > 1 squarefree) or I as a generator whose square is known */
static Value *square_root_gen(slong D) {
    Value *num = v_num();
    if (D == -1) ca_i(num->num, am_ca);
    else { ca_set_si(num->num, D, am_ca); ca_sqrt(num->num, num->num, am_ca); }
    Value *g = am_number_kernel(num);
    int k = am_gen_of(g);
    am_vars[k].has_square = 1;
    am_vars[k].square = D;
    return g;
}

/* the number Calcium's extension generator stands for */
static int ext_value(ca_t res, ca_ext_ptr e) {
    if (CA_EXT_IS_QQBAR(e)) { ca_set_qqbar(res, CA_EXT_QQBAR(e), am_ca); return 1; }
    slong n = CA_EXT_FUNC_NARGS(e);
    if (n == 0) {
        ca_field_srcptr K = _ca_ctx_get_field_const(am_ca, CA_EXT_HEAD(e));
        _ca_make_field_element(res, K, am_ca);
        fmpz_mpoly_q_gen(CA_MPOLY_Q(res), 0, CA_FIELD_MCTX(K, am_ca));
        return 1;
    }
    if (n == 1) { _ca_function_fx(res, CA_EXT_HEAD(e), CA_EXT_FUNC_ARGS(e), am_ca); return 1; }
    if (n == 2) { _ca_function_fxy(res, CA_EXT_HEAD(e), CA_EXT_FUNC_ARGS(e), CA_EXT_FUNC_ARGS(e) + 1, am_ca); return 1; }
    return 0;
}

/* log(q) for a positive rational q other than a prime: the sum of e log(p) over its prime factors p^e */
static Value *log_of_rational(const ca_t a) {
    fmpq_t q; fmpq_init(q);
    if (!ca_get_fmpq(q, a, am_ca) || fmpq_sgn(q) <= 0 || fmpz_bits(fmpq_numref(q)) > 64 || fmpz_bits(fmpq_denref(q)) > 64) { fmpq_clear(q); return NULL; }
    fmpz_factor_t F[2]; fmpz_factor_init(F[0]); fmpz_factor_init(F[1]);
    fmpz_factor(F[0], fmpq_numref(q)); fmpz_factor(F[1], fmpq_denref(q));
    Value *r = NULL;
    if (!(F[0]->num == 1 && F[0]->exp[0] == 1 && F[1]->num == 0)) {       /* log(p) itself stays */
        r = v_num();
        for (int w = 0; w < 2; w++) for (slong i = 0; i < F[w]->num; i++) {
            Value *lp = v_num(); ca_set_fmpz(lp->num, F[w]->p + i, am_ca); ca_log(lp->num, lp->num, am_ca);
            Value *e = v_num(); ca_set_si(e->num, w ? -(slong)F[w]->exp[i] : (slong)F[w]->exp[i], am_ca);
            r = v_add(r, v_mul(e, am_number_kernel(lp)));
        }
    }
    fmpz_factor_clear(F[0]); fmpz_factor_clear(F[1]); fmpq_clear(q);
    return r;
}

/* a number of a field Q(pi, exp(2), I, ...) as a rational function of its generators, each a generator here:
   2*pi*I is 2 times pi times I, not one opaque term */
Value *am_field_rf(const Value *num) {
    if (CA_IS_SPECIAL(num->num)) return NULL;
    ca_field_srcptr K = CA_FIELD(num->num, am_ca);
    if (!CA_FIELD_IS_GENERIC(K)) return NULL;
    slong len = CA_FIELD_LENGTH(K);
    if (len > 8) return NULL;
    const fmpz_mpoly_ctx_struct *mctx = CA_FIELD_MCTX(K, am_ca);
    const fmpz_mpoly_q_struct *q = CA_MPOLY_Q(num->num);
    if (len == 1 && fmpz_mpoly_is_gen(fmpz_mpoly_q_numref(q), 0, mctx) && fmpz_mpoly_is_one(fmpz_mpoly_q_denref(q), mctx)) {
        ca_ext_ptr e = CA_FIELD_EXT_ELEM(K, 0);
        return CA_EXT_HEAD(e) == CA_Log ? log_of_rational(CA_EXT_FUNC_ARGS(e)) : NULL;
    }
    Value *g[8];
    for (slong i = 0; i < len; i++) {                         /* sin(1) is exp(I) inside Calcium: keep its own form */
        ca_ext_ptr e = CA_FIELD_EXT_ELEM(K, i);
        if (!CA_EXT_IS_QQBAR(e) && CA_EXT_FUNC_NARGS(e) >= 1 && ca_check_is_real(CA_EXT_FUNC_ARGS(e), am_ca) != T_TRUE) return NULL;
    }
    for (slong i = 0; i < len; i++) {
        Value *v = v_num();
        if (!ext_value(v->num, CA_FIELD_EXT_ELEM(K, i))) return NULL;
        ca_ext_ptr e = CA_FIELD_EXT_ELEM(K, i);
        g[i] = CA_EXT_IS_QQBAR(e) ? am_number_rf(v) : NULL;
        if (!g[i] && CA_EXT_HEAD(e) == CA_Log) g[i] = log_of_rational(CA_EXT_FUNC_ARGS(e));
        if (!g[i]) g[i] = am_number_kernel(v);
    }
    Value *part[2];
    for (int w = 0; w < 2; w++) {
        const fmpz_mpoly_struct *p = w ? fmpz_mpoly_q_denref(q) : fmpz_mpoly_q_numref(q);
        Value *s = v_num();
        fmpz_t c; fmpz_init(c);
        ulong ex[8];
        for (slong t = 0; t < fmpz_mpoly_length(p, mctx); t++) {
            fmpz_mpoly_get_term_coeff_fmpz(c, p, t, mctx);
            fmpz_mpoly_get_term_exp_ui(ex, p, t, mctx);
            Value *m = v_num(); ca_set_fmpz(m->num, c, am_ca);
            for (slong i = 0; i < len; i++) for (ulong k = 0; k < ex[i]; k++) m = v_mul(m, g[i]);
            s = v_add(s, m);
        }
        fmpz_clear(c);
        part[w] = s;
    }
    return v_div(part[0], part[1]);
}

/* a quadratic irrational as a + b sqrt(D) (with I for D < 0), so that sqrt(2)*x + sqrt(8)*x is 3*sqrt(2)*x */
Value *am_number_rf(const Value *num) {
    qqbar_t q; qqbar_init(q);
    int alg = ca_get_qqbar(q, num->num, am_ca);
    if (!alg || qqbar_degree(q) != 2) {
        qqbar_clear(q);
        Value *r = alg ? NULL : am_field_rf(num);
        return r ? r : am_number_kernel(num);
    }
    const fmpz *c = QQBAR_COEFFS(q);                         /* c0 + c1 x + c2 x^2 */
    fmpz_t disc, s, D, t; fmpz_init(disc); fmpz_init(s); fmpz_init(D); fmpz_init(t);
    fmpz_mul(disc, c + 1, c + 1);
    fmpz_mul(t, c + 0, c + 2); fmpz_mul_ui(t, t, 4);
    fmpz_sub(disc, disc, t);                                 /* disc = s^2 D, D squarefree */
    fmpz_factor_t F; fmpz_factor_init(F);
    fmpz_factor(F, disc);
    fmpz_one(s); fmpz_set_si(D, fmpz_sgn(disc));
    for (slong i = 0; i < F->num; i++) {
        fmpz_pow_ui(t, F->p + i, F->exp[i] / 2); fmpz_mul(s, s, t);
        if (F->exp[i] & 1) fmpz_mul(D, D, F->p + i);
    }
    fmpz_factor_clear(F);
    Value *r = NULL;
    if (fmpz_cmp_si(D, 1000000000) < 0 && fmpz_cmp_si(D, -1000000000) > 0) {
        slong d = fmpz_get_si(D);
        Value *K = d > 0 ? square_root_gen(d) : (d == -1 ? square_root_gen(-1) : v_mul(square_root_gen(-1), square_root_gen(-d)));
        fmpq_t a, b; fmpq_init(a); fmpq_init(b);
        fmpz_t den; fmpz_init(den); fmpz_mul_ui(den, c + 2, 2);
        fmpz_neg(t, c + 1); fmpq_set_fmpz_frac(a, t, den);    /* (-c1 +- s sqrt(D)) / (2 c2) */
        fmpq_set_fmpz_frac(b, s, den);
        for (int sign = 1; sign >= -1 && !r; sign -= 2) {
            Value *A = v_num(), *B = v_num();
            ca_set_fmpq(A->num, a, am_ca); ca_set_fmpq(B->num, b, am_ca);
            if (sign < 0) ca_neg(B->num, B->num, am_ca);
            Value *cand = v_add(A, v_mul(B, K));
            Value *check = am_reevaluate(cand);              /* the number it stands for, to pick the sign */
            if (check->kind == V_NUM && ca_check_equal(check->num, num->num, am_ca) == T_TRUE) r = cand;
        }
        fmpq_clear(a); fmpq_clear(b); fmpz_clear(den);
    }
    fmpz_clear(disc); fmpz_clear(s); fmpz_clear(D); fmpz_clear(t);
    qqbar_clear(q);
    return r ? r : am_number_kernel(num);
}

/* replace sqrt(D)^2 by D and I^2 by -1 in the numerator and the denominator */
void am_reduce_squares(Value *v) {
    if (v->kind != V_RF) return;
    int used[AM_MAXVARS] = {0}, any = 0;
    fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i] && am_vars[i].has_square) any = 1;
    if (!any) return;
    fmpz_mpoly_t div, Q, R; fmpz_mpoly_init(div, am_mp); fmpz_mpoly_init(Q, am_mp); fmpz_mpoly_init(R, am_mp);
    for (int i = 0; i < am_nvars; i++) {
        if (!used[i] || !am_vars[i].has_square) continue;
        fmpz_mpoly_gen(div, i, am_mp);
        fmpz_mpoly_mul(div, div, div, am_mp);
        fmpz_mpoly_sub_si(div, div, am_vars[i].square, am_mp);   /* k^2 - D */
        for (int part = 0; part < 2; part++) {
            fmpz_mpoly_struct *p = part ? fmpz_mpoly_q_denref(v->rf) : fmpz_mpoly_q_numref(v->rf);
            if (fmpz_mpoly_degree_si(p, i, am_mp) < 2) continue;
            fmpz_mpoly_divrem(Q, R, p, div, am_mp);
            fmpz_mpoly_swap(p, R, am_mp);
        }
    }
    fmpz_mpoly_clear(div, am_mp); fmpz_mpoly_clear(Q, am_mp); fmpz_mpoly_clear(R, am_mp);
    fmpz_mpoly_q_canonicalise(v->rf, am_mp);
}

/* ---------------- a normal form for deciding zero ---------------- */

static int same_args(int i, int j) {
    if (am_vars[i].nargs != am_vars[j].nargs) return 0;
    for (int k = 0; k < am_vars[i].nargs; k++) {
        char *a = v_str_of(am_vars[i].args[k]), *b = v_str_of(am_vars[j].args[k]);
        int eq = !strcmp(a, b);
        free(a); free(b);
        if (!eq) return 0;
    }
    return 1;
}

static int head_is(int i, const char *h) { return am_vars[i].kernel && am_vars[i].head && !strcmp(am_vars[i].head, h) && am_vars[i].nargs == 1; }

/* tan(u) as sin(u)/cos(u), then each sin(u)^2 + cos(u)^2 - 1 reduced away: equal expressions often become equal
 * rational functions. A nonzero result does not prove nonzero (sin(2x) is not reduced to sin(x)). */
Value *am_normal_form(Value *v) {
    if (v->kind != V_RF) return v;
    v = am_expand_angles(v);
    if (v->kind != V_RF) return v;
    int used[AM_MAXVARS] = {0}, tans = 0;
    fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i] && head_is(i, "tan")) tans = 1;
    if (tans) {
        Value *val[AM_MAXVARS];
        for (int i = 0; i < am_nvars; i++) {
            val[i] = am_gen(i);
            if (used[i] && head_is(i, "tan")) {
                Value *a = am_vars[i].args[0];
                val[i] = v_div(am_call("sin", &a, 1), am_call("cos", &a, 1));
            }
        }
        v = am_subs_rf(v, val);
        if (v->kind != V_RF) return v;
        memset(used, 0, sizeof used);
        fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    }
    Value *r = v_copy(v);
    fmpz_mpoly_t div, Q, R; fmpz_mpoly_init(div, am_mp); fmpz_mpoly_init(Q, am_mp); fmpz_mpoly_init(R, am_mp);
    for (int i = 0; i < am_nvars; i++) {
        if (!used[i] || !head_is(i, "sin")) continue;
        for (int j = 0; j < am_nvars; j++) {
            if (!used[j] || !head_is(j, "cos") || !same_args(i, j)) continue;
            fmpz_mpoly_t g; fmpz_mpoly_init(g, am_mp);
            fmpz_mpoly_gen(div, i, am_mp); fmpz_mpoly_mul(div, div, div, am_mp);
            fmpz_mpoly_gen(g, j, am_mp); fmpz_mpoly_mul(g, g, g, am_mp);
            fmpz_mpoly_add(div, div, g, am_mp);
            fmpz_mpoly_sub_ui(div, div, 1, am_mp);              /* sin(u)^2 + cos(u)^2 - 1 */
            fmpz_mpoly_clear(g, am_mp);
            for (int part = 0; part < 2; part++) {
                fmpz_mpoly_struct *p = part ? fmpz_mpoly_q_denref(r->rf) : fmpz_mpoly_q_numref(r->rf);
                fmpz_mpoly_divrem(Q, R, p, div, am_mp);
                fmpz_mpoly_swap(p, R, am_mp);
            }
            if (fmpz_mpoly_is_zero(fmpz_mpoly_q_denref(r->rf), am_mp)) { fmpz_mpoly_set(fmpz_mpoly_q_numref(r->rf), fmpz_mpoly_q_numref(v->rf), am_mp); fmpz_mpoly_set(fmpz_mpoly_q_denref(r->rf), fmpz_mpoly_q_denref(v->rf), am_mp); }
            fmpz_mpoly_q_canonicalise(r->rf, am_mp);
        }
    }
    for (int i = 0; i < am_nvars; i++) {                      /* sqrt(u)^2 = u, for a polynomial u */
        if (!used[i] || !head_is(i, "sqrt")) continue;
        Value *u = am_vars[i].args[0];
        if (u->kind != V_RF || !fmpz_mpoly_is_one(fmpz_mpoly_q_denref(u->rf), am_mp)) continue;
        fmpz_mpoly_gen(div, i, am_mp); fmpz_mpoly_mul(div, div, div, am_mp);
        fmpz_mpoly_sub(div, div, fmpz_mpoly_q_numref(u->rf), am_mp);
        for (int part = 0; part < 2; part++) {
            fmpz_mpoly_struct *p = part ? fmpz_mpoly_q_denref(r->rf) : fmpz_mpoly_q_numref(r->rf);
            if (fmpz_mpoly_degree_si(p, i, am_mp) < 2) continue;
            fmpz_mpoly_divrem(Q, R, p, div, am_mp);
            if (!fmpz_mpoly_is_zero(R, am_mp) || part == 0) fmpz_mpoly_swap(p, R, am_mp);
        }
        fmpz_mpoly_q_canonicalise(r->rf, am_mp);
    }
    fmpz_mpoly_clear(div, am_mp); fmpz_mpoly_clear(Q, am_mp); fmpz_mpoly_clear(R, am_mp);
    return r;
}

/* is v zero? 1 proved, 0 proved not (a point where it is not 0), 2 zero at random points (not a proof), -1 undecided */
int am_zero_test(Value *v, char *witness, size_t wlen) {
    if (witness && wlen) witness[0] = 0;
    v = am_reevaluate(v);
    if (v->kind == V_NUM) { truth_t t = ca_check_is_zero(v->num, am_ca); return t == T_TRUE ? 1 : t == T_FALSE ? 0 : -1; }
    if (v->kind != V_RF) return -1;
    if (fmpz_mpoly_q_is_zero(v->rf, am_mp)) return 1;
    Value *nf = am_normal_form(v);
    if (nf->kind == V_NUM) { truth_t t = ca_check_is_zero(nf->num, am_ca); if (t == T_TRUE) return 1; }
    else if (nf->kind == V_RF && fmpz_mpoly_q_is_zero(nf->rf, am_mp)) return 1;
    /* random points: certified evaluation */
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    int zeros = 0;
    static const int nums[] = {37, 113, -71, 59, 211, -29, 97};
    for (int k = 0; k < 5; k++) {
        Value *val[AM_MAXVARS];
        char where[256] = "";
        for (int i = 0; i < am_nvars; i++) {
            val[i] = am_gen(i);
            if (!am_vars[i].kernel) {
                Value *q = v_num();
                fmpq_t r; fmpq_init(r);
                fmpq_set_si(r, nums[(k + i) % 7], 100 + 13 * k);
                ca_set_fmpq(q->num, r, am_ca);
                if (!am_free_of(v, i) && strlen(where) < 200) { char *s = fmpq_get_str(NULL, 10, r); snprintf(where + strlen(where), sizeof where - strlen(where), "%s%s = %s", where[0] ? ", " : "", am_varnames[i], s); flint_free(s); }
                fmpq_clear(r);
                val[i] = q;
            }
        }
        int n0 = am_nvars;
        for (int i = 0; i < n0; i++) {                         /* function terms at that point */
            if (!am_vars[i].kernel) continue;
            if (am_vars[i].numval) { val[i] = am_vars[i].numval; continue; }
            const char *hd = am_vars[i].head;
            if (used[i] && hd && (!strcmp(hd, "integrate") || !strcmp(hd, "diff") || !strcmp(hd, "sum") || !strcmp(hd, "limit") || !strcmp(hd, "series")))
                return -1;                                     /* a bound variable inside: no value at a point */
            if (!used[i] && hd && (!strcmp(hd, "integrate") || !strcmp(hd, "diff") || !strcmp(hd, "sum") || !strcmp(hd, "limit") || !strcmp(hd, "series"))) continue;
            Value **ka = malloc((size_t)(am_vars[i].nargs ? am_vars[i].nargs : 1) * sizeof *ka);
            for (int j = 0; j < am_vars[i].nargs; j++) ka[j] = am_reevaluate(am_subs_rf(am_vars[i].args[j], val));
            val[i] = am_call(am_vars[i].head, ka, am_vars[i].nargs);
            free(ka);
        }
        Value *x = am_reevaluate(am_subs_rf(v, val));
        if (x->kind != V_NUM) return -1;
        acb_t z; acb_init(z);
        ca_get_acb(z, x->num, 256, am_ca);
        int contains = acb_contains_zero(z);
        acb_clear(z);
        if (!contains) { if (witness) snprintf(witness, wlen, "%s", where); return 0; }
        zeros++;
    }
    return zeros == 5 ? 2 : -1;
}

/* base^e for a symbolic exponent: exp(e*log(base)) as a value, named base^e */
Value *am_power_kernel(Value *base, Value *e) {
    if (e->kind == V_RF && fmpz_mpoly_is_fmpz(fmpz_mpoly_q_denref(e->rf), am_mp)) {   /* b^(e + m) = b^m b^e, m whole */
        ulong zero[AM_MAXVARS] = {0};
        fmpz_t c, m; fmpz_init(c); fmpz_init(m);
        fmpz_mpoly_get_coeff_fmpz_ui(c, fmpz_mpoly_q_numref(e->rf), zero, am_mp);
        fmpz_mpoly_get_coeff_fmpz_ui(m, fmpz_mpoly_q_denref(e->rf), zero, am_mp);
        fmpz_fdiv_q(m, c, m);
        if (!fmpz_is_zero(m) && fmpz_cmp_si(m, 1000) <= 0 && fmpz_cmp_si(m, -1000) >= 0) {
            Value *mv = v_num(); ca_set_fmpz(mv->num, m, am_ca);
            fmpz_clear(c); fmpz_clear(m);
            return v_mul(v_pow(base, mv), am_power_kernel(base, v_sub(e, mv)));
        }
        fmpz_clear(c); fmpz_clear(m);
    }
    Value *b = base;
    Value *l = base->kind == V_NUM ? am_kernel_value("log", &b, 1) : am_call("log", &b, 1);   /* log(2) kept symbolic, so 2^x 2^x is 2^(2x) */
    Value *arg = v_mul(e, l);
    char *bs = v_str_of(base), *es = v_str_of(e);
    int bpar = bs[0] == '-' || strchr(bs, '/') || strchr(bs, ' ') || strchr(bs, '*') || strchr(bs, '^');
    int epar = strchr(es, ' ') || strchr(es, '/') || strchr(es, '*') || es[0] == '-';
    char *name = malloc(strlen(bs) + strlen(es) + 8);
    sprintf(name, bpar ? (epar ? "(%s)^(%s)" : "(%s)^%s") : (epar ? "%s^(%s)" : "%s^%s"), bs, es);
    free(bs); free(es);
    int k = find_term("exp", &arg, 1);
    if (k >= 0) { free(name); return am_gen(k); }
    k = find(name, strlen(name));
    if (k < 0) {
        k = add(name, strlen(name));
        am_vars[k].kernel = 1; am_vars[k].head = strdup("exp"); am_vars[k].nargs = 1;
        am_vars[k].args = malloc(sizeof(Value *));
        am_vars[k].args[0] = v_copy(arg); am_pool_keep(am_vars[k].args[0]);
    }
    free(name);
    return am_gen(k);
}

/* exp(u) exp(v) -> exp(u + v), exp(u)^k -> exp(k u), exp(u) below the line -> exp(-u) above: one exp per term */
static int normalizing;
Value *am_normalize_exp(Value *v) {
    if (normalizing || v->kind != V_RF) return v;
    int used[AM_MAXVARS] = {0}, nexp = 0, need = 0;
    fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    const fmpz_mpoly_struct *N = fmpz_mpoly_q_numref(v->rf), *Dn = fmpz_mpoly_q_denref(v->rf);
    for (int i = 0; i < am_nvars; i++) {
        if (!used[i] || !am_vars[i].head || strcmp(am_vars[i].head, "exp") || am_vars[i].nargs != 1) continue;
        nexp++;
        if (fmpz_mpoly_degree_si(Dn, i, am_mp) > 0 || fmpz_mpoly_degree_si(N, i, am_mp) > 1) need = 1;
    }
    if (!nexp) return v;
    if (nexp >= 2) {                                               /* two exps in one term? */
        ulong ex[AM_MAXVARS];
        for (slong t = 0; t < fmpz_mpoly_length(N, am_mp) && !need; t++) {
            fmpz_mpoly_get_term_exp_ui(ex, N, t, am_mp);
            int c = 0;
            for (int i = 0; i < am_nvars; i++) if (ex[i] && am_vars[i].head && !strcmp(am_vars[i].head, "exp")) c++;
            if (c >= 2) need = 1;
        }
    }
    if (!need) return v;
    normalizing = 1;
    /* rebuild: each term of N/Dn as coefficient * (non-exp part) * exp(sum k_i u_i - sum m_i u_i) / (Dn without exps) */
    Value *dsum = v_num();                                         /* the exponent from the denominator's exps */
    fmpz_mpoly_t D0; fmpz_mpoly_init(D0, am_mp);
    fmpz_mpoly_set(D0, Dn, am_mp);
    if (fmpz_mpoly_length(Dn, am_mp) == 1) {                       /* a monomial denominator: its exps move up */
        ulong ex[AM_MAXVARS]; fmpz_t c; fmpz_init(c);
        fmpz_mpoly_get_term_exp_ui(ex, Dn, 0, am_mp);
        fmpz_mpoly_get_term_coeff_fmpz(c, Dn, 0, am_mp);
        fmpz_mpoly_zero(D0, am_mp);
        ulong ex0[AM_MAXVARS];
        for (int i = 0; i < am_nvars; i++) {
            ex0[i] = ex[i];
            if (ex[i] && am_vars[i].head && !strcmp(am_vars[i].head, "exp") && am_vars[i].nargs == 1) {
                Value *k = v_num(); ca_set_ui(k->num, ex[i], am_ca);
                dsum = v_add(dsum, v_mul(k, am_vars[i].args[0]));
                ex0[i] = 0;
            }
        }
        for (int i = am_nvars; i < AM_MAXVARS; i++) ex0[i] = 0;
        fmpz_mpoly_set_coeff_fmpz_ui(D0, c, ex0, am_mp);
        fmpz_clear(c);
    }
    Value *sum = v_num();
    ulong ex[AM_MAXVARS];
    fmpz_t c; fmpz_init(c);
    for (slong t = 0; t < fmpz_mpoly_length(N, am_mp); t++) {
        fmpz_mpoly_get_term_exp_ui(ex, N, t, am_mp);
        fmpz_mpoly_get_term_coeff_fmpz(c, N, t, am_mp);
        Value *term = v_num(); ca_set_fmpz(term->num, c, am_ca);
        Value *e = v_neg(dsum);
        int any = !(dsum->kind == V_NUM && ca_check_is_zero(dsum->num, am_ca) == T_TRUE);
        for (int i = 0; i < am_nvars; i++) {
            if (!ex[i]) continue;
            Value *k = v_num(); ca_set_ui(k->num, ex[i], am_ca);
            if (am_vars[i].head && !strcmp(am_vars[i].head, "exp") && am_vars[i].nargs == 1) { e = v_add(e, v_mul(k, am_vars[i].args[0])); any = 1; }
            else term = v_mul(term, v_pow(am_gen(i), k));
        }
        if (any) {
            Value *ee = am_reevaluate(e);
            if (!(ee->kind == V_NUM && ca_check_is_zero(ee->num, am_ca) == T_TRUE)) term = v_mul(term, am_call("exp", &ee, 1));
        }
        sum = v_add(sum, term);
    }
    fmpz_clear(c);
    Value *den = v_rf();
    fmpz_mpoly_set(fmpz_mpoly_q_numref(den->rf), D0, am_mp);
    fmpz_mpoly_one(fmpz_mpoly_q_denref(den->rf), am_mp);
    fmpz_mpoly_clear(D0, am_mp);
    Value *r = v_div(sum, den);
    normalizing = 0;
    return r;
}

/* the sign of the leading coefficient of a rational function (numerator over denominator), 0 for a number */
int am_lead_sign(const Value *v) {
    if (v->kind != V_RF) return 0;
    const fmpz_mpoly_struct *N = fmpz_mpoly_q_numref(v->rf), *D = fmpz_mpoly_q_denref(v->rf);
    if (fmpz_mpoly_length(N, am_mp) == 0) return 0;
    fmpz_t c; fmpz_init(c);
    fmpz_mpoly_get_term_coeff_fmpz(c, N, 0, am_mp);
    int s = fmpz_sgn(c);
    fmpz_mpoly_get_term_coeff_fmpz(c, D, 0, am_mp);
    s *= fmpz_sgn(c);
    fmpz_clear(c);
    return s;
}

/* sin(k B), cos(k B) for an integer k in terms of s = sin(B), c = cos(B) (Chebyshev recurrences) */
static void multiple_angle(slong k, Value *sB, Value *cB, Value **sk, Value **ck) {
    Value *s0 = v_num(), *c0 = v_num(); ca_one(c0->num, am_ca);
    Value *s1 = sB, *c1 = cB;
    if (k == 0) { *sk = s0; *ck = c0; return; }
    for (slong j = 1; j < k; j++) {                              /* s_{j+1} = s_j c + c_j s, c_{j+1} = c_j c - s_j s */
        Value *s2 = v_add(v_mul(s1, cB), v_mul(c1, sB));
        Value *c2 = v_sub(v_mul(c1, cB), v_mul(s1, sB));
        s1 = s2; c1 = c2;
    }
    *sk = s1; *ck = c1;
}

/* every sin/cos of an integer multiple of a common angle written through sin and cos of that angle */
Value *am_expand_angles(Value *v) {
    if (v->kind != V_RF) return v;
    int used[AM_MAXVARS] = {0}, n0 = am_nvars;
    fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    Value *val[AM_MAXVARS];
    int changed = 0;
    for (int i = 0; i < n0; i++) val[i] = am_gen(i);
    for (int i = 0; i < n0; i++) {
        if (!used[i] || !(head_is(i, "sin") || head_is(i, "cos"))) continue;
        /* the angle A = k * B with B the smallest common angle among the sin/cos terms with the same direction */
        Value *A = am_vars[i].args[0];
        Value *best = NULL; fmpq_t kbest; fmpq_init(kbest);
        for (int j = 0; j < n0; j++) {
            if (!used[j] || !(head_is(j, "sin") || head_is(j, "cos"))) continue;
            Value *ratio = v_div(A, am_vars[j].args[0]);
            fmpq_t q; fmpq_init(q);
            if (v_is_rational(ratio, q) && fmpz_is_one(fmpq_denref(q)) && fmpz_cmp_si(fmpq_numref(q), 1) > 0 && fmpz_cmp_si(fmpq_numref(q), 40) <= 0) {
                if (!best || fmpq_cmp(q, kbest) > 0) { best = am_vars[j].args[0]; fmpq_set(kbest, q); }
            }
            fmpq_clear(q);
        }
        if (best) {
            slong k = fmpz_get_si(fmpq_numref(kbest));
            Value *sB = am_call("sin", &best, 1), *cB = am_call("cos", &best, 1), *sk, *ck;
            multiple_angle(k, sB, cB, &sk, &ck);
            val[i] = head_is(i, "sin") ? sk : ck;
            changed = 1;
        }
        fmpq_clear(kbest);
    }
    return changed ? am_subs_rf(v, val) : v;
}
