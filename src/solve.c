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
        fmpz_mpoly_factor_clear(fac, am_mp);
        am_fail("solve: %s appears both bare and inside function terms (or in several unrelated ones); no exact method yet", am_varnames[x]);
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
    nparams = 0;
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
    const char *how = "every solution of each factor (by roots, by formula, or by inverting the function terms)";
    if (worst == 1) am_status(S_PROVED, "%s; each put back into the equation: it holds exactly%s", how, nparams ? " (integer parameters at 0 and 1; the rest by periodicity)" : "");
    else if (worst == 2) am_status(S_PROBABLE, "%s; each put back into the equation: it holds at random points", how);
    else am_status(S_UNKNOWN, "%s; putting some back into the equation was undecided", how);
    if (nparams) {
        char ps[256]; size_t pl = 0;
        for (int j = 0; j < nparams; j++) pl += (size_t)snprintf(ps + pl, sizeof ps - pl, "%s%s", j ? ", " : "", am_varnames[params[j]]);
        am_fact("integer_parameters", "\"%s: any integer\"", ps);
    }
    if (realknown) am_fact("real_solutions", "%s", reals);
    if (dropped) am_fact("dropped", "%d", dropped);
    return out;
}
