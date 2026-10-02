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

/* a quadratic irrational as a + b sqrt(D) (with I for D < 0), so that sqrt(2)*x + sqrt(8)*x is 3*sqrt(2)*x */
Value *am_number_rf(const Value *num) {
    qqbar_t q; qqbar_init(q);
    int alg = ca_get_qqbar(q, num->num, am_ca);
    if (!alg || qqbar_degree(q) != 2) { qqbar_clear(q); return am_number_kernel(num); }
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
