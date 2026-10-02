/* One equation in one unknown, beyond polynomials with number coefficients.
 *
 * e = 0 is factored. Each factor that involves x is
 *   - a polynomial in x: by roots() when its coefficients are numbers, by formula up to degree 2 otherwise;
 *   - a polynomial in one function term u(x) (or in exp(w) for exps whose arguments are rational multiples of one
 *     w): solved for u, then u(x) = c is inverted: exp, log, sqrt, sin, cos, tan, asin, acos, atan. Periodic
 *     inverses bring an integer parameter n1, n2, ...
 * Every candidate is put back into the equation; the ones that do not satisfy it (sqrt and log branches) are
 * dropped. The solutions are complex unless the facts say otherwise; real_solutions lists the real ones. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/fmpz_mpoly_factor.h>

static Value *num_si(slong k) { Value *v = v_num(); ca_set_si(v->num, k, am_ca); return v; }
static Value *pi_v(void) { Value *v = v_num(); ca_pi(v->num, am_ca); return v; }
static Value *i_v(void) { Value *v = v_num(); ca_i(v->num, am_ca); return v; }
static Value *call1(const char *f, Value *a) { return am_call(f, &a, 1); }
static int is_zero_num(const Value *v) { return v->kind == V_NUM && ca_check_is_zero(v->num, am_ca) == T_TRUE; }

static Value *from_mpoly(const fmpz_mpoly_t p) {
    Value *r = v_rf();
    fmpz_mpoly_set(fmpz_mpoly_q_numref(r->rf), p, am_mp);
    fmpz_mpoly_one(fmpz_mpoly_q_denref(r->rf), am_mp);
    return am_reevaluate(r);
}

static int real_only;                  /* abs was inverted: the solutions are the real ones */

/* the integer parameters brought in by periodic inverses */
static int nparams, params[16];
static Value *new_param(void) {
    if (nparams >= 16) am_fail("solve: too many integer parameters");
    char name[16]; snprintf(name, sizeof name, "n%d", nparams + 1);
    int k = am_var_index(name, strlen(name));
    params[nparams++] = k;
    return am_gen(k);
}

/* the candidates: x = items */
typedef struct { Value **v; int n, cap; } Cands;
static void push(Cands *c, Value *v) {
    char *s = v_str_of(v);
    for (int i = 0; i < c->n; i++) { char *t = v_str_of(c->v[i]); int same = !strcmp(s, t); free(t); if (same) { free(s); return; } }
    free(s);
    if (c->n == c->cap) { c->cap = c->cap ? 2 * c->cap : 8; c->v = realloc(c->v, (size_t)c->cap * sizeof *c->v); }
    c->v[c->n++] = v;
}

static void solve_in(Value *e, int x, Cands *out, int depth);

/* the coefficients of p as a polynomial in generator g: c[0..deg] */
static slong coeffs_in(const fmpz_mpoly_t p, int g, Value ***c) {
    slong d = fmpz_mpoly_degree_si(p, g, am_mp);
    *c = calloc((size_t)(d + 1), sizeof(Value *));
    fmpz_mpoly_t t; fmpz_mpoly_init(t, am_mp);
    slong vars[1] = {g};
    for (slong j = 0; j <= d; j++) {
        ulong ex[1] = {(ulong)j};
        fmpz_mpoly_get_coeff_vars_ui(t, p, vars, ex, 1, am_mp);
        (*c)[j] = from_mpoly(t);
    }
    fmpz_mpoly_clear(t, am_mp);
    return d;
}

/* the values of generator g making the polynomial p zero (p has degree >= 1 in g) */
static void poly_roots(const fmpz_mpoly_t p, int g, Cands *vals) {
    int used[AM_MAXVARS] = {0}, others = 0;
    Value *pv = from_mpoly(p);
    if (pv->kind == V_RF) fmpz_mpoly_q_used_vars(used, pv->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i] && i != g) others = 1;
    if (!others && !am_vars[g].kernel) {                          /* number coefficients: every root, exactly */
        Value *a[2] = {pv, am_gen(g)};
        int mute = am_fact_mute; am_fact_mute = 1;
        Value *r = am_call("roots", a, 2);
        am_fact_mute = mute;
        for (int i = 0; i < r->n; i++) push(vals, r->items[i]);
        return;
    }
    Value **c;
    slong d = coeffs_in(p, g, &c);
    if (d == 1) push(vals, v_neg(v_div(c[0], c[1])));
    else if (d == 2) {
        Value *disc = v_sub(v_mul(c[1], c[1]), v_mul(num_si(4), v_mul(c[2], c[0])));
        Value *s = call1("sqrt", disc), *two_a = v_mul(num_si(2), c[2]);
        push(vals, v_div(v_add(v_neg(c[1]), s), two_a));
        if (!is_zero_num(disc)) push(vals, v_div(v_sub(v_neg(c[1]), s), two_a));
    } else if (d >= 3 && !others) {                               /* a kernel with number coefficients: roots in a fresh unknown */
        int t = am_var_index("t_", 2);
        Value **val = malloc(AM_MAXVARS * sizeof(Value *));
        for (int i = 0; i < am_nvars; i++) val[i] = am_gen(i);
        val[g] = am_gen(t);
        Value *q = am_subs_rf(pv, val);
        free(val);
        Value *a[2] = {q, am_gen(t)};
        int mute = am_fact_mute; am_fact_mute = 1;
        Value *r = am_call("roots", a, 2);
        am_fact_mute = mute;
        for (int i = 0; i < r->n; i++) push(vals, r->items[i]);
    } else am_fail("solve: a polynomial of degree %ld in %s with symbolic coefficients (degrees 1 and 2 are solved by formula)", (long)d, am_varnames[g]);
    free(c);
}

/* u = c for the function term u = am_vars[g]: equations in its argument */
static void invert(int g, Value *c, int x, Cands *out, int depth) {
    const char *h = am_vars[g].head;
    if (!h || am_vars[g].nargs != 1) am_fail("solve: cannot invert %s", am_varnames[g]);
    Value *w = am_vars[g].args[0];
    Value *two_pi = v_mul(num_si(2), pi_v());
    if (!strcmp(h, "exp")) {
        if (is_zero_num(c)) return;                               /* exp is never 0 */
        Value *n = new_param();
        solve_in(v_sub(w, v_add(call1("log", c), v_mul(v_mul(two_pi, i_v()), n))), x, out, depth + 1);
    } else if (!strcmp(h, "log")) {
        solve_in(v_sub(w, call1("exp", c)), x, out, depth + 1);
    } else if (!strcmp(h, "sqrt")) {
        solve_in(v_sub(w, v_mul(c, c)), x, out, depth + 1);
    } else if (!strcmp(h, "sin")) {
        Value *n = new_param(), *as = call1("asin", c);
        solve_in(v_sub(w, v_add(as, v_mul(two_pi, n))), x, out, depth + 1);
        solve_in(v_sub(w, v_add(v_sub(pi_v(), as), v_mul(two_pi, n))), x, out, depth + 1);
    } else if (!strcmp(h, "cos")) {
        Value *n = new_param(), *ac = call1("acos", c);
        solve_in(v_sub(w, v_add(ac, v_mul(two_pi, n))), x, out, depth + 1);
        solve_in(v_sub(w, v_add(v_neg(ac), v_mul(two_pi, n))), x, out, depth + 1);
    } else if (!strcmp(h, "tan")) {
        Value *n = new_param();
        solve_in(v_sub(w, v_add(call1("atan", c), v_mul(pi_v(), n))), x, out, depth + 1);
    } else if (!strcmp(h, "abs")) {                               /* |w| = c: w = c or w = -c (real w) */
        real_only = 1;
        Value *z = num_si(0);
        if (c->kind == V_NUM && (ca_check_is_real(c->num, am_ca) != T_TRUE || ca_check_lt(c->num, z->num, am_ca) == T_TRUE)) return;
        solve_in(v_sub(w, c), x, out, depth + 1);
        if (!is_zero_num(c)) solve_in(v_add(w, c), x, out, depth + 1);
    } else if (!strcmp(h, "asin")) solve_in(v_sub(w, call1("sin", c)), x, out, depth + 1);
    else if (!strcmp(h, "acos")) solve_in(v_sub(w, call1("cos", c)), x, out, depth + 1);
    else if (!strcmp(h, "atan")) solve_in(v_sub(w, call1("tan", c)), x, out, depth + 1);
    else am_fail("solve: cannot invert %s", h);
}

static int depends(int g, int x) { return g == x || (am_vars[g].kernel && !am_free_of(am_gen(g), x)); }

/* exps whose arguments are rational multiples of one w: exp(m_i w) = t^m_i */
static int exp_multiples(const fmpz_mpoly_t f, int x, int *ks, int nk, Cands *out, int depth) {
    for (int i = 0; i < nk; i++) if (strcmp(am_vars[ks[i]].head ? am_vars[ks[i]].head : "", "exp")) return 0;
    Value *w0 = am_vars[ks[0]].args[0];
    fmpq_t r[AM_MAXVARS], g; fmpq_init(g);
    int ok = 1;
    for (int i = 0; i < nk; i++) {
        fmpq_init(r[i]);
        Value *q = am_normal_form(v_div(am_vars[ks[i]].args[0], w0));
        if (ok && !v_is_rational(q, r[i])) ok = 0;
    }
    if (ok) {
        /* w = g w0 with g the rational gcd of the r_i: every r_i/g a whole number */
        fmpz_t nn, dd; fmpz_init(nn); fmpz_init(dd);
        fmpz_set(nn, fmpq_numref(r[0])); fmpz_set(dd, fmpq_denref(r[0]));
        for (int i = 1; i < nk; i++) { fmpz_gcd(nn, nn, fmpq_numref(r[i])); fmpz_lcm(dd, dd, fmpq_denref(r[i])); }
        fmpq_set_fmpz_frac(g, nn, dd);
        fmpz_clear(nn); fmpz_clear(dd);
        int t = am_var_index("t_", 2);
        Value **val = malloc(AM_MAXVARS * sizeof(Value *));
        for (int i = 0; i < am_nvars; i++) val[i] = am_gen(i);
        for (int i = 0; i < nk; i++) {
            fmpq_t m; fmpq_init(m); fmpq_div(m, r[i], g);
            Value *mv = v_num(); ca_set_fmpq(mv->num, m, am_ca); fmpq_clear(m);
            val[ks[i]] = v_pow(am_gen(t), mv);
        }
        Value *q = am_subs_rf(from_mpoly(f), val);
        free(val);
        if (q->kind != V_RF) ok = 0;
        else {
            Cands ts = {0};
            poly_roots(fmpz_mpoly_q_numref(q->rf), t, &ts);
            Value *gv = v_num(); ca_set_fmpq(gv->num, g, am_ca);
            Value *arg = v_mul(gv, w0);
            Value *ek = call1("exp", arg);
            int k = am_gen_of(ek);
            for (int i = 0; i < ts.n; i++) {
                if (k >= 0) invert(k, ts.v[i], x, out, depth);
                else {                                            /* exp(g w0) = c directly */
                    if (is_zero_num(ts.v[i])) continue;
                    Value *n = new_param();
                    solve_in(v_sub(arg, v_add(call1("log", ts.v[i]), v_mul(v_mul(v_mul(num_si(2), pi_v()), i_v()), n))), x, out, depth + 1);
                }
            }
            free(ts.v);
        }
    }
    for (int i = 0; i < nk; i++) fmpq_clear(r[i]);
    fmpq_clear(g);
    return ok;
}

static Value *from_mpoly(const fmpz_mpoly_t p);

/* c0 + sum n_i log(u_i) = 0 with whole n_i: exp(c0) prod u_i^n_i = 1 (a superset of the solutions: checked later) */
static int logs_combined(const fmpz_mpoly_t f, int x, Cands *out, int depth) {
    Value *c0 = num_si(0), *prod = num_si(1);
    int any = 0;
    fmpz_mpoly_t term; fmpz_mpoly_init(term, am_mp);
    ulong ex[AM_MAXVARS];
    for (slong t = 0; t < fmpz_mpoly_length(f, am_mp); t++) {
        fmpz_mpoly_get_term(term, f, t, am_mp);
        Value *tv = from_mpoly(term);
        if (am_free_of(tv, x)) { c0 = v_add(c0, tv); continue; }
        fmpz_mpoly_get_term_exp_ui(ex, f, t, am_mp);
        int lg = -1, other = 0;
        for (int i = 0; i < am_nvars; i++) {
            if (!ex[i]) continue;
            if (am_free_of(am_gen(i), x)) { other = 1; continue; }
            if (ex[i] == 1 && am_vars[i].head && !strcmp(am_vars[i].head, "log") && am_vars[i].nargs == 1 && lg < 0) lg = i;
            else { fmpz_mpoly_clear(term, am_mp); return 0; }
        }
        if (lg < 0 || other) { fmpz_mpoly_clear(term, am_mp); return 0; }
        fmpz_t c; fmpz_init(c); fmpz_mpoly_get_term_coeff_fmpz(c, f, t, am_mp);
        if (fmpz_cmp_si(c, 16) > 0 || fmpz_cmp_si(c, -16) < 0) { fmpz_clear(c); fmpz_mpoly_clear(term, am_mp); return 0; }
        Value *cv = v_num(); ca_set_fmpz(cv->num, c, am_ca); fmpz_clear(c);
        prod = v_mul(prod, v_pow(am_vars[lg].args[0], cv));
        any = 1;
    }
    fmpz_mpoly_clear(term, am_mp);
    if (!any) return 0;
    Value *g = v_sub(v_mul(call1("exp", c0), prod), num_si(1));
    solve_in(g, x, out, depth + 1);
    return 1;
}

/* A + B sqrt(u) = 0 (square roots the only function terms of x): A^2 - B^2 u = 0, a superset checked later */
static int sqrt_squared(const fmpz_mpoly_t f, int x, int *ks, int nk, Cands *out, int depth) {
    for (int i = 0; i < nk; i++) if (!am_vars[ks[i]].head || strcmp(am_vars[ks[i]].head, "sqrt") || am_vars[ks[i]].nargs != 1) return 0;
    int s = ks[nk - 1];                                       /* one square root at a time; the others in later rounds */
    Value *u = am_vars[s].args[0];
    if (!am_free_of(u, s)) return 0;
    Value **c;
    slong d = coeffs_in(f, s, &c);
    Value *A = num_si(0), *B = num_si(0), *up = num_si(1);
    for (slong j = 0; j <= d; j++) {                          /* s^j = u^(j/2) or u^((j-1)/2) s */
        if (j & 1) B = v_add(B, v_mul(c[j], up)); else A = v_add(A, v_mul(c[j], up));
        if (j & 1) up = v_mul(up, u);
    }
    free(c);
    solve_in(v_sub(v_mul(A, A), v_mul(v_mul(B, B), u)), x, out, depth + 1);
    return 1;
}

static void solve_in(Value *e, int x, Cands *out, int depth) {
    if (depth > 8) am_fail("solve: nested too deeply");
    e = am_normal_form(am_reevaluate(e));
    if (e->kind == V_NUM) {
        if (is_zero_num(e)) am_fail("solve: every value of %s is a solution", am_varnames[x]);
        return;
    }
    if (e->kind != V_RF) am_fail("solve: expected an equation");
    fmpz_mpoly_factor_t fac; fmpz_mpoly_factor_init(fac, am_mp);
    if (!fmpz_mpoly_factor(fac, fmpz_mpoly_q_numref(e->rf), am_mp)) am_fail("solve: could not factor the equation");
    for (slong i = 0; i < fac->num; i++) {
        const fmpz_mpoly_struct *f = fac->poly + i;
        int used[AM_MAXVARS] = {0}, ks[AM_MAXVARS], nk = 0, bare = 0;
        fmpz_mpoly_used_vars(used, f, am_mp);
        for (int g = 0; g < am_nvars; g++) {
            if (!used[g] || !depends(g, x)) continue;
            if (g == x) bare = 1; else ks[nk++] = g;
        }
        if (!bare && !nk) continue;                               /* free of x */
        if (!nk) { poly_roots(f, x, out); continue; }
        if (!bare && nk == 1) {
            Cands vals = {0};
            poly_roots(f, ks[0], &vals);
            for (int j = 0; j < vals.n; j++) invert(ks[0], vals.v[j], x, out, depth);
            free(vals.v);
            continue;
        }
        if (!bare && exp_multiples(f, x, ks, nk, out, depth)) continue;
        if (logs_combined(f, x, out, depth)) continue;
        if (sqrt_squared(f, x, ks, nk, out, depth)) continue;
        fmpz_mpoly_factor_clear(fac, am_mp);
        am_fail("solve: %s appears both bare and inside function terms (or in several unrelated ones); no exact method yet. nsolve(eq, %s, a, b) gives the certified real roots in [a, b]", am_varnames[x], am_varnames[x]);
    }
    fmpz_mpoly_factor_clear(fac, am_mp);
}

/* the check: the equation at x = c, with each integer parameter at 0 and at 1 */
typedef struct { Value *e, *c; int x; } Check;
static Value *check_at(void *p) {
    Check *k = p;
    Value *a[3] = {k->e, am_gen(k->x), k->c};
    Value *r = am_call("subs", a, 3);
    return am_normal_form(am_reevaluate(r));
}
static int verify(Value *e, int x, Value *c) {      /* 1 proved, 2 probable, 0 fails, -1 undecided */
    int worst = 1;
    for (int pass = 0; pass < (nparams ? 2 : 1); pass++) {
        Value *cc = c;
        for (int j = 0; j < nparams; j++) {
            Value *a[3] = {cc, am_gen(params[j]), num_si(pass)};
            cc = am_call("subs", a, 3);
        }
        Check k = {e, cc, x};
        Value *r;
        if (!am_try(check_at, &k, &r)) return 0;                  /* a denominator 0 there, or worse */
        int z = am_zero_test(r, NULL, 0);
        if (z == 0) return 0;
        if (z == -1) worst = -1;
        else if (z == 2 && worst == 1) worst = 2;
    }
    return worst;
}

Value *am_solve1(Value *e, int x) {
    nparams = 0; real_only = 0;
    Cands c = {0};
    int mute = am_fact_mute;
    solve_in(e, x, &c, 0);
    am_fact_mute = mute;
    am_status_clear();                                            /* the steps' own statuses give way to the check's */
    Value *out = v_list(0);
    out->items = calloc((size_t)(c.n ? c.n : 1), sizeof(Value *));
    int dropped = 0, worst = 1;
    char reals[4096]; size_t rl = 0; int nreal = 0, realknown = 1;
    rl += (size_t)snprintf(reals + rl, sizeof reals - rl, "[");
    for (int i = 0; i < c.n; i++) {
        int v = verify(e, x, c.v[i]);
        if (v == 0) { dropped++; continue; }
        if (v == -1) worst = -1; else if (v == 2 && worst == 1) worst = 2;
        Value *eq = v_list(2); eq->kind = V_EQ; eq->items[0] = am_gen(x); eq->items[1] = c.v[i];
        out->items[out->n++] = eq;
        /* real members: the candidate at parameters 0 and 1 */
        Value *c0 = c.v[i], *c1 = c.v[i];
        for (int j = 0; j < nparams; j++) {
            Value *a0[3] = {c0, am_gen(params[j]), num_si(0)}, *a1[3] = {c1, am_gen(params[j]), num_si(1)};
            c0 = am_call("subs", a0, 3); c1 = am_call("subs", a1, 3);
        }
        c0 = am_reevaluate(c0); c1 = am_reevaluate(c1);
        if (c0->kind != V_NUM || c1->kind != V_NUM) { realknown = 0; continue; }
        truth_t r0 = ca_check_is_real(c0->num, am_ca), r1 = ca_check_is_real(c1->num, am_ca);
        if (r0 == T_UNKNOWN || r1 == T_UNKNOWN) { realknown = 0; continue; }
        if (r0 != T_TRUE) continue;
        char *s = v_str_of(r1 == T_TRUE ? c.v[i] : c0);
        if (rl + strlen(s) + 16 < sizeof reals) rl += (size_t)snprintf(reals + rl, sizeof reals - rl, "%s\"%s = %s\"", nreal ? ", " : "", am_varnames[x], s);
        free(s);
        nreal++;
    }
    snprintf(reals + rl, sizeof reals - rl, "]");
    free(c.v);
    const char *how = "every solution of each factor (by roots, by formula, by inverting the function terms, or by combining logarithms and squaring roots)";
    if (worst == 1) am_status(S_PROVED, "%s; each put back into the equation: it holds exactly%s", how, nparams ? " (integer parameters at 0 and 1; the rest by periodicity)" : "");
    else if (worst == 2) am_status(S_PROBABLE, "%s; each put back into the equation: it holds at random points, or to 150 digits where exact arithmetic could not decide", how);
    else am_status(S_UNKNOWN, "%s; putting some back into the equation was undecided", how);
    if (nparams) {
        char ps[256]; size_t pl = 0;
        for (int j = 0; j < nparams; j++) pl += (size_t)snprintf(ps + pl, sizeof ps - pl, "%s%s", j ? ", " : "", am_varnames[params[j]]);
        am_fact("integer_parameters", "\"%s: any integer\"", ps);
    }
    if (realknown) am_fact("real_solutions", "%s", reals);
    if (dropped) am_fact("dropped", "%d", dropped);
    if (real_only) am_fact("domain", "\"real: abs(w) = c was solved as w = c or w = -c, for real w\"");
    return out;
}

/* ---------------- inequalities: g op 0 over the reals, g a rational function of x ---------------- */

#include <flint/fmpz_poly.h>
#include <flint/qqbar.h>

static int sign_at(const fmpz_poly_t P, const ca_t t) {        /* the exact sign of P(t), t real */
    ca_t s; ca_init(s, am_ca);
    for (slong k = fmpz_poly_degree(P); k >= 0; k--) { ca_mul(s, s, t, am_ca); ca_add_fmpz(s, s, P->coeffs + k, am_ca); }
    Value *z = num_si(0);
    int r = ca_check_gt(s, z->num, am_ca) == T_TRUE ? 1 : ca_check_lt(s, z->num, am_ca) == T_TRUE ? -1 : ca_check_is_zero(s, am_ca) == T_TRUE ? 0 : 2;
    ca_clear(s, am_ca);
    if (r == 2) am_fail("solve: a sign could not be decided");
    return r;
}

static int wants(int sign, const char *op) {
    if (!strcmp(op, "<")) return sign < 0;
    if (!strcmp(op, "<=")) return sign <= 0;
    if (!strcmp(op, ">")) return sign > 0;
    return sign >= 0;
}

Value *am_solve_ineq(Value *g, const char *op, int x) {
    g = am_reevaluate(g);
    fmpz_poly_t N, D, P; fmpz_poly_init(N); fmpz_poly_init(D); fmpz_poly_init(P);
    if (g->kind == V_NUM) {
        if (ca_check_is_real(g->num, am_ca) != T_TRUE) am_fail("solve: the inequality compares a number that is not real");
        fmpz_poly_zero(N);
        Value *z = num_si(0);
        int s = ca_check_gt(g->num, z->num, am_ca) == T_TRUE ? 1 : ca_check_is_zero(g->num, am_ca) == T_TRUE ? 0 : -1;
        am_status(S_PROVED, "a constant comparison");
        return v_str(wants(s, op) ? "every real x" : "no real x");
    }
    int used[AM_MAXVARS] = {0};
    if (g->kind != V_RF) am_fail("solve: expected an inequality");
    fmpz_mpoly_q_used_vars(used, g->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i] && i != x) am_fail("solve: inequalities are solved for rational functions of %s with number coefficients", am_varnames[x]);
    fmpz_mpoly_get_fmpz_poly(N, fmpz_mpoly_q_numref(g->rf), x, am_mp);
    fmpz_mpoly_get_fmpz_poly(D, fmpz_mpoly_q_denref(g->rf), x, am_mp);
    fmpz_poly_mul(P, N, D);                                     /* the sign of N/D where D != 0 */
    /* the real roots of N and D, sorted, each once */
    slong dn = fmpz_poly_degree(N), dd = fmpz_poly_degree(D);
    qqbar_ptr rn = dn > 0 ? _qqbar_vec_init(dn) : NULL, rd = dd > 0 ? _qqbar_vec_init(dd) : NULL;
    if (dn > 0) qqbar_roots_fmpz_poly(rn, N, 0);
    if (dd > 0) qqbar_roots_fmpz_poly(rd, D, 0);
    slong cap = (dn > 0 ? dn : 0) + (dd > 0 ? dd : 0) + 1, np = 0;
    qqbar_ptr pts = _qqbar_vec_init(cap);
    int *pole = calloc((size_t)cap, sizeof(int));
    for (int w = 0; w < 2; w++) {
        qqbar_ptr r = w ? rd : rn; slong d = w ? dd : dn;
        for (slong i = 0; i < d; i++) {
            if (!qqbar_is_real(r + i)) continue;
            slong j; for (j = 0; j < np; j++) if (qqbar_equal(pts + j, r + i)) break;
            if (j == np) { qqbar_set(pts + np, r + i); pole[np] = w; np++; }
            else if (w) pole[j] = 1;
        }
    }
    for (slong i = 1; i < np; i++)                              /* insertion sort */
        for (slong j = i; j > 0 && qqbar_cmp_re(pts + j, pts + j - 1) < 0; j--) { qqbar_swap(pts + j, pts + j - 1); int t = pole[j]; pole[j] = pole[j - 1]; pole[j - 1] = t; }
    /* gap i lies between point i - 1 and point i (gap 0 from -oo, gap np to +oo) */
    int *gap = calloc((size_t)(np + 1), sizeof(int)), *at = calloc((size_t)(np + 1), sizeof(int));
    ca_t t, u; ca_init(t, am_ca); ca_init(u, am_ca);
    for (slong i = 0; i <= np; i++) {
        if (np == 0) ca_zero(t, am_ca);
        else if (i == 0) { ca_set_qqbar(t, pts, am_ca); ca_sub_ui(t, t, 1, am_ca); }
        else if (i == np) { ca_set_qqbar(t, pts + np - 1, am_ca); ca_add_ui(t, t, 1, am_ca); }
        else { ca_set_qqbar(t, pts + i - 1, am_ca); ca_set_qqbar(u, pts + i, am_ca); ca_add(t, t, u, am_ca); ca_div_ui(t, t, 2, am_ca); }
        gap[i] = wants(sign_at(P, t), op);
        if (i < np) at[i] = !pole[i] && wants(0, op);           /* at a root of N: g = 0 */
    }
    ca_clear(t, am_ca); ca_clear(u, am_ca);
    /* the solution set as intervals: runs of satisfied gaps and points */
    char buf[8192]; size_t bl = 0; int nint = 0;
    char js[8192]; size_t jl = 0;
    jl += (size_t)snprintf(js + jl, sizeof js - jl, "[");
    /* walk the sequence gap0, pt0, gap1, pt1, ..., gap_np: element e even is gap e/2, odd is point (e-1)/2 */
    slong ne = 2 * np + 1;
    for (slong e = 0; e < ne; ) {
        int ok = (e & 1) ? at[(e - 1) / 2] : gap[e / 2];
        if (!ok) { e++; continue; }
        slong f = e;
        while (f + 1 < ne && ((f + 1) & 1 ? at[f / 2] : gap[(f + 1) / 2])) f++;
        /* from element e to element f */
        char *lo = NULL, *hi = NULL; int lo_closed = 0, hi_closed = 0;
        if (e & 1) { Value *v = v_num(); ca_set_qqbar(v->num, pts + (e - 1) / 2, am_ca); lo = v_str_of(v); lo_closed = 1; }
        else if (e > 0) { Value *v = v_num(); ca_set_qqbar(v->num, pts + e / 2 - 1, am_ca); lo = v_str_of(v); }
        if (f & 1) { Value *v = v_num(); ca_set_qqbar(v->num, pts + (f - 1) / 2, am_ca); hi = v_str_of(v); hi_closed = 1; }
        else if (f / 2 < np) { Value *v = v_num(); ca_set_qqbar(v->num, pts + f / 2, am_ca); hi = v_str_of(v); }
        const char *X = am_varnames[x];
        char piece[2048];
        if (e == f && (e & 1)) snprintf(piece, sizeof piece, "%s = %s", X, lo);
        else if (!lo && !hi) snprintf(piece, sizeof piece, "every real %s", X);
        else if (!lo) snprintf(piece, sizeof piece, "%s %s %s", X, hi_closed ? "<=" : "<", hi);
        else if (!hi) snprintf(piece, sizeof piece, "%s %s %s", X, lo_closed ? ">=" : ">", lo);
        else snprintf(piece, sizeof piece, "%s %s %s %s %s", lo, lo_closed ? "<=" : "<", X, hi_closed ? "<=" : "<", hi);
        bl += (size_t)snprintf(buf + bl, sizeof buf - bl, "%s%s", nint ? " or " : "", piece);
        char *pj = am_json_str(piece);
        jl += (size_t)snprintf(js + jl, sizeof js - jl, "%s%s", nint ? ", " : "", pj);
        free(pj); free(lo); free(hi);
        nint++;
        e = f + 1;
    }
    snprintf(js + jl, sizeof js - jl, "]");
    if (!nint) snprintf(buf, sizeof buf, "no real %s", am_varnames[x]);
    am_status(S_PROVED, "exact real roots of the numerator and denominator; the sign on each interval between them decided exactly");
    am_fact("intervals", "%s", js);
    free(gap); free(at); free(pole);
    _qqbar_vec_clear(pts, cap);
    if (rn) _qqbar_vec_clear(rn, dn);
    if (rd) _qqbar_vec_clear(rd, dd);
    fmpz_poly_clear(N); fmpz_poly_clear(D); fmpz_poly_clear(P);
    return v_str(buf);
}

/* ---------------- nsolve: certified real roots on an interval ---------------- */

#include <flint/arb_calc.h>

int am_eval_acb(acb_t out, Value *f, int x, const acb_t z, int analytic, slong prec);

typedef struct { Value *f, *df; int x; int failed; } RealFn;

static int real_fn(arb_ptr out, const arb_t inp, void *param, slong order, slong prec) {
    RealFn *F = param;
    acb_t z, v; acb_init(z); acb_init(v);
    acb_set_arb(z, inp);
    for (slong k = 0; k < order && k < 2; k++) {
        if (!am_eval_acb(v, k ? F->df : F->f, F->x, z, 0, prec) || !arb_contains_zero(acb_imagref(v))) { F->failed = 1; arb_indeterminate(out + k); }
        else arb_set(out + k, acb_realref(v));
    }
    acb_clear(z); acb_clear(v);
    return 0;
}

static Value *b_nsolve_impl(Value **a, int n) {
    if (n < 4 || n > 5) am_fail("nsolve(eq, x, a, b[, digits]): the real roots of eq in [a, b]");
    Value *e = a[0]->kind == V_EQ ? v_sub(a[0]->items[0], a[0]->items[1]) : a[0];
    int x = am_gen_of(a[1]);
    if (x < 0 || am_vars[x].kernel) am_fail("nsolve: the second argument must be a variable");
    slong digits = 15;
    if (n == 5) { fmpq_t q; fmpq_init(q); if (!v_is_rational(a[4], q) || !fmpz_is_one(fmpq_denref(q))) am_fail("nsolve: digits must be a whole number"); digits = fmpz_get_si(fmpq_numref(q)); fmpq_clear(q); }
    if (digits < 1 || digits > 1000) am_fail("nsolve: digits between 1 and 1000");
    slong prec = (slong)(digits * 3.33) + 30;
    acb_t A, B; acb_init(A); acb_init(B);
    if (!am_eval_acb(A, a[2], -1, A, 0, prec) || !am_eval_acb(B, a[3], -1, B, 0, prec) || !arb_is_zero(acb_imagref(A)) || !arb_is_zero(acb_imagref(B)))
        am_fail("nsolve: the ends must be real numbers");
    Value *da[2] = {e, am_gen(x)};
    RealFn F = {e, am_call("diff", da, 2), x, 0};
    arf_interval_t block; arf_interval_init(block);
    arf_set_mag(&block->a, arb_radref(acb_realref(A))); arf_sub(&block->a, arb_midref(acb_realref(A)), &block->a, prec, ARF_RND_FLOOR);
    arf_set_mag(&block->b, arb_radref(acb_realref(B))); arf_add(&block->b, arb_midref(acb_realref(B)), &block->b, prec, ARF_RND_CEIL);
    if (arf_cmp(&block->a, &block->b) >= 0) am_fail("nsolve: the interval is empty");
    arf_interval_ptr blocks = NULL; int *flags = NULL;
    slong nb = arb_calc_isolate_roots(&blocks, &flags, real_fn, &F, block, 60, 200000, 1000, 64);
    if (F.failed) am_fail("nsolve: the equation is not real and finite everywhere on the interval");
    Value *out = v_list(0);
    out->items = calloc((size_t)(nb ? nb : 1), sizeof(Value *));
    int unsure = 0;
    fmpq_t last; fmpq_init(last); int have_last = 0;
    for (slong i = 0; i < nb; i++) {
        if (flags[i] != 1) {                                   /* an end of the piece exactly a root (sin(x) at 0)? */
            int found = 0;
            for (int w = 0; w < 2 && !found; w++) {
                fmpq_t q; fmpq_init(q);
                arf_get_fmpq(q, w ? &blocks[i].b : &blocks[i].a);
                if (have_last && fmpq_equal(q, last)) { fmpq_clear(q); found = 1; break; }
                Value *qv = v_num(); ca_set_fmpq(qv->num, q, am_ca);
                Check k = {e, qv, x};
                Value *r;
                if (am_try(check_at, &k, &r) && am_zero_test(r, NULL, 0) == 1) {
                    Value *eq = v_list(2); eq->kind = V_EQ; eq->items[0] = am_gen(x); eq->items[1] = qv;
                    out->items[out->n++] = eq;
                    fmpq_set(last, q); have_last = 1; found = 1;
                }
                fmpq_clear(q);
            }
            if (!found) unsure++;
            continue;
        }
        arf_interval_t r; arf_interval_init(r);
        arb_calc_refine_root_bisect(r, real_fn, &F, blocks + i, (slong)(digits * 3.33) + 20, prec);
        arb_t m; arb_init(m);
        arf_interval_get_arb(m, r, prec);
        char *s = arb_get_str(m, digits, ARB_STR_NO_RADIUS);
        Value *eq = v_list(2); eq->kind = V_EQ; eq->items[0] = am_gen(x); eq->items[1] = v_str(s);
        out->items[out->n++] = eq;
        flint_free(s); arb_clear(m); arf_interval_clear(r);
    }
    fmpq_clear(last);
    _arf_interval_vec_clear(blocks, nb); flint_free(flags);
    arf_interval_clear(block); acb_clear(A); acb_clear(B);
    if (unsure) {
        am_status(S_NUMERIC, "the roots listed are certified (a sign change, the derivative nonzero: exactly one each, digits by bisection); %d piece(s) of the interval could not be decided (a double root, roots too close together, or a singularity)", unsure);
        am_fact("undecided_pieces", "%d", unsure);
    } else am_status(S_CERTIFIED, "every real root in the interval isolated (or found exactly at a dividing point) by ball arithmetic (Arb): a sign change and a nonzero derivative show exactly one in each piece; digits by bisection");
    return out;
}
Value *am_nsolve(Value **a, int n) { return b_nsolve_impl(a, n); }
