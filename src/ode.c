/* dsolve(eq, y, x[, [conditions]]): ordinary differential equations.
 *
 * The unknown function is written y, its derivatives y', y'', ... (or y(x), diff(y(x), x), ...). Solved:
 *   - linear with constant coefficients, any order: the characteristic roots give exp(r x), x^j exp(r x), and
 *     exp(a x) cos(b x), exp(a x) sin(b x) for complex pairs; a right-hand side by variation of parameters;
 *   - linear of first order: the integrating factor exp(integral of p);
 *   - initial conditions [y(x0) = v0, y'(x0) = v1, ...] fix the constants C1, C2, ...
 * Every solution is put back into the equation and checked to vanish. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/qqbar.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpz_poly_factor.h>

#define MAXORD 12

static Value *num_si(slong k) { Value *v = v_num(); ca_set_si(v->num, k, am_ca); return v; }
static Value *call(const char *f, Value **a, int n) { return am_call(f, a, n); }
static Value *D(Value *f, int x) { Value *a[2] = {f, am_gen(x)}; return call("diff", a, 2); }
static Value *subs_gen(Value *f, int g, Value *val) {
    Value *eq = v_list(2); eq->kind = V_EQ; eq->items[0] = am_gen(g); eq->items[1] = val;
    Value *a[2] = {f, eq};
    return call("subs", a, 2);
}

/* the generator for the k-th derivative y, y', y'', ... (named with apostrophes) */
static int deriv_var(const char *y, int k) {
    char name[128];
    snprintf(name, sizeof name, "%s", y);
    for (int i = 0; i < k && strlen(name) < sizeof name - 2; i++) strcat(name, "'");
    return am_var_index(name, strlen(name));
}

static int uses(Value *v, int g) { return !am_free_of(v, g); }

static int is_zero_val(Value *v) {
    if (v->kind == V_NUM) return ca_check_is_zero(v->num, am_ca) == T_TRUE;
    if (v->kind == V_RF) return fmpz_mpoly_q_is_zero(v->rf, am_mp);
    return 0;
}

/* replace y(x) and diff(y(x), x, k) function terms by the generators y, y', ... */
static Value *to_prime_form(Value *E, const char *y, int x) {
    if (E->kind != V_RF) return E;
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, E->rf, am_mp);
    Value *val[AM_MAXVARS];
    int changed = 0;
    for (int i = 0; i < am_nvars; i++) {
        val[i] = am_gen(i);
        if (!used[i] || !am_vars[i].kernel || !am_vars[i].head) continue;
        if (!strcmp(am_vars[i].head, y) && am_vars[i].nargs == 1 && am_gen_of(am_vars[i].args[0]) == x) { val[i] = am_gen(deriv_var(y, 0)); changed = 1; }
        else if (!strcmp(am_vars[i].head, "diff") && am_vars[i].nargs == 2) {
            /* diff(...(y(x))..., x) nested: count the depth */
            int k = 1; Value *in = am_vars[i].args[0];
            int g;
            while ((g = am_gen_of(in)) >= 0 && am_vars[g].head && !strcmp(am_vars[g].head, "diff") && am_vars[g].nargs == 2) { k++; in = am_vars[g].args[0]; }
            g = am_gen_of(in);
            if (g >= 0 && am_vars[g].head && !strcmp(am_vars[g].head, y)) { val[i] = am_gen(deriv_var(y, k)); changed = 1; }
        }
    }
    return changed ? am_subs_rf(E, val) : E;
}

/* the solution y(x) substituted for y, y', ...: E must vanish */
static int check(Value *E, Value *sol, int ord, const char *y, int x) {
    Value *eqs = v_list(ord + 1);                             /* subs reaches inside function terms: exp(y) too */
    Value *d = sol;
    for (int k = 0; k <= ord; k++) {
        Value *eq = v_list(2); eq->kind = V_EQ; eq->items[0] = am_gen(deriv_var(y, k)); eq->items[1] = d;
        eqs->items[k] = eq;
        d = D(d, x);
    }
    Value *sa[2] = {E, eqs};
    Value *r = am_reevaluate(call("subs", sa, 2));
    int z = am_zero_test(r, NULL, 0);
    return z;
}

/* y' = g(x) h(y): integral of dy/h(y) = integral of g(x) dx + C1, solved for y when solve can, checked by substitution */
typedef struct { Value *R; int g; Value *v; } AtArg;
static Value *at_point(void *p) { AtArg *t = p; return am_normal_form(am_reevaluate(subs_gen(t->R, t->g, t->v))); }
typedef struct { Value *e; int y; } SolveArg;
extern int am_solve_noverify;
static Value *solve_try(void *p) { SolveArg *t = p; am_solve_noverify = 1; Value *r = am_solve1(t->e, t->y); am_solve_noverify = 0; return r; }

static Value *separable(Value *E, const char *y, int x, Value *conds) {
    int Y = deriv_var(y, 0), Yp = deriv_var(y, 1);
    Value *c1 = D(E, Yp);
    if (uses(c1, Yp) || is_zero_val(c1)) return NULL;
    Value *R = am_normal_form(v_neg(v_div(subs_gen(E, Yp, num_si(0)), c1)));     /* y' = R(x, y) */
    if (!uses(R, Y)) return NULL;
    Value *h = NULL;
    for (int t = 1; t <= 5 && !h; t++) {                     /* h(y) = R(x0, y) at a point where it is defined and not 0 */
        AtArg aa = {R, x, num_si(t)};
        Value *hv;
        if (am_try(at_point, &aa, &hv) && !is_zero_val(hv) && uses(hv, Y)) h = hv;
    }
    if (!h) return NULL;
    Value *g = am_normal_form(v_div(R, h));
    if (uses(g, Y)) return NULL;                              /* not separable */
    Value *ia[2] = {v_div(num_si(1), h), am_gen(Y)}, *ga[2] = {g, am_gen(x)};
    am_fact_mute++;
    Value *H = call("integrate", ia, 2), *G = call("integrate", ga, 2);
    am_fact_mute--;
    char *hs = v_str_of(H), *gs = v_str_of(G);
    int unev = strstr(hs, "integrate(") || strstr(gs, "integrate(");
    free(hs); free(gs);
    if (unev) am_fail("dsolve: a separable equation, but the integral of 1/h(%s) or of g(%s) was not found", y, am_varnames[x]);
    Value *C = am_gen(am_var_index("C1", 2));
    int ncond = 0;
    if (conds) {                                              /* y(x0) = v0 fixes C1 */
        if (conds->kind != V_LIST || conds->n != 1) am_fail("dsolve: a first-order equation takes one condition, [y(x0) = v0]");
        Value *c = conds->items[0];
        int cg = c->kind == V_EQ ? am_gen_of(c->items[0]) : -1;
        if (cg < 0 || !am_vars[cg].head || strcmp(am_vars[cg].head, y) || am_vars[cg].nargs != 1) am_fail("dsolve: write the condition as %s(x0) = value", y);
        Value *x0 = am_vars[cg].args[0], *v0 = c->items[1];
        C = am_reevaluate(v_sub(subs_gen(H, Y, v0), subs_gen(G, x, x0)));
        ncond = 1;
        (void)x0;
    }
    Value *implicit = v_sub(v_sub(H, G), C);
    am_fact("separable", "true");
    {   /* the constant solutions h(y) = 0 */
        SolveArg sa = {h, Y};
        Value *cs;
        int mute = am_fact_mute; am_fact_mute = 1;
        if (am_try(solve_try, &sa, &cs) && cs->kind == V_LIST && cs->n) { char *t = v_str_of(cs); char *js = am_json_str(t); am_fact("constant_solutions", "%s", js); free(js); free(t); }
        am_fact_mute = mute;
    }
    SolveArg sa = {implicit, Y};
    Value *sols;
    int mute = am_fact_mute; am_fact_mute = 1;
    int solved = am_try(solve_try, &sa, &sols) && sols->kind == V_LIST;
    am_solve_noverify = 0;
    am_fact_mute = mute;
    am_status_clear();
    Value *keep = v_list(0);
    keep->items = calloc((size_t)(solved && sols->n ? sols->n : 1), sizeof(Value *));
    int worst = 1;
    if (solved) for (int i = 0; i < sols->n; i++) {
        Value *cand = sols->items[i]->items[1];
        for (int j = 1; j <= 16; j++) {                       /* periodic branches: C1 takes them in */
            char nm[8]; snprintf(nm, sizeof nm, "n%d", j);
            for (int k = 0; k < am_nvars; k++) if (!am_vars[k].kernel && !strcmp(am_varnames[k], nm)) cand = am_reevaluate(subs_gen(cand, k, num_si(0)));
        }
        int z = check(E, cand, 1, y, x);
        if (z == 0) continue;
        if (ncond) {
            Value *c = conds->items[0];
            int cg = am_gen_of(c->items[0]);
            Value *d = v_sub(subs_gen(cand, x, am_vars[cg].args[0]), c->items[1]);
            if (am_zero_test(d, NULL, 0) == 0) continue;
        }
        if (z != 1) worst = z == 2 && worst == 1 ? 2 : (z == -1 ? -1 : worst);
        Value *eq = v_list(2); eq->kind = V_EQ; eq->items[0] = am_gen(Y); eq->items[1] = cand;
        keep->items[keep->n++] = eq;
    }
    if (keep->n) {
        const char *what = ncond ? "the condition fixes C1" : "C1 is the constant of the separated integration";
        if (worst == 1) am_status(S_PROVED, "separable: the integral of dy/h(y) equals the integral of g(x) dx plus C1, solved for %s; put back into the equation: it holds exactly; %s", y, what);
        else if (worst == 2) am_status(S_PROBABLE, "separable; solved for %s; put back into the equation: it holds at random points; %s", y, what);
        else am_status(S_UNKNOWN, "separable; solved for %s; the check by substitution could not be decided", y);
        return keep->n == 1 ? keep->items[0] : keep;
    }
    /* implicit: H(y) = G(x) + C1 */
    am_status(S_PROVED, "separable: the solution in implicit form, the integral of dy/h(y) equals the integral of g(x) dx plus C1 (not solved for %s)", y);
    am_fact("implicit", "true");
    Value *eq = v_list(2); eq->kind = V_EQ; eq->items[0] = H; eq->items[1] = v_add(G, C);
    return eq;
}

Value *b_dsolve(Value **a, int n) {
    if (n < 3 || n > 4) am_fail("dsolve(eq, y, x[, [y(x0) = v0, y'(x0) = v1, ...]])");
    int yg = am_gen_of(a[1]), x = am_gen_of(a[2]);
    if (yg < 0 || am_vars[yg].kernel) {                          /* y(x) given instead of y */
        if (yg >= 0 && am_vars[yg].head && am_vars[yg].nargs == 1) x = x < 0 ? am_gen_of(am_vars[yg].args[0]) : x;
        else am_fail("dsolve: the second argument is the unknown function's name, y");
    }
    if (x < 0 || am_vars[x].kernel) am_fail("dsolve: the third argument is the variable, x");
    char y[96];
    snprintf(y, sizeof y, "%s", am_vars[yg].head ? am_vars[yg].head : am_varnames[yg]);
    Value *E = a[0]->kind == V_EQ ? v_sub(a[0]->items[0], a[0]->items[1]) : a[0];
    E = to_prime_form(E, y, x);
    if (E->kind != V_RF) am_fail("dsolve: the equation does not involve %s", y);
    int ord = -1, g[MAXORD + 1];
    for (int k = 0; k <= MAXORD; k++) { g[k] = deriv_var(y, k); if (uses(E, g[k])) ord = k; }
    if (ord < 1) am_fail("dsolve: no derivative of %s in the equation", y);
    /* linear: E = sum a_k(x) y^(k) + r(x) */
    Value *coef[MAXORD + 1], *r = E;
    int linear = 1;
    for (int k = 0; k <= ord; k++) {
        Value *dk[2] = {E, am_gen(g[k])};
        coef[k] = call("diff", dk, 2);
        for (int j = 0; j <= ord; j++) if (uses(coef[k], g[j])) linear = 0;
    }
    if (!linear && ord == 1) { Value *r = separable(E, y, x, n == 4 ? a[3] : NULL); if (r) return r; }
    if (!linear) am_fail("dsolve: only linear and separable first-order equations are solved so far (the equation is not linear in %s and its derivatives)", y);
    for (int k = 0; k <= ord; k++) r = subs_gen(r, g[k], num_si(0));
    am_fact("order", "%d", ord);
    am_fact("linear", "true");
    int constcoef = 1;
    for (int k = 0; k <= ord; k++) if (uses(coef[k], x)) constcoef = 0;
    Value *basis[MAXORD]; int nb = 0;
    Value *sol = NULL;
    if (constcoef) {
        /* the characteristic polynomial sum a_k r^k, with rational coefficients */
        fmpq_poly_t cp; fmpq_poly_init(cp);
        fmpq_t q; fmpq_init(q);
        for (int k = 0; k <= ord; k++) {
            if (!v_is_rational(am_reevaluate(coef[k]), q)) am_fail("dsolve: the coefficients must be numbers (symbolic coefficients: later)");
            fmpq_poly_set_coeff_fmpq(cp, k, q);
        }
        fmpq_clear(q);
        fmpz_poly_t zp; fmpz_poly_init(zp); fmpq_poly_get_numerator(zp, cp);
        qqbar_ptr roots = _qqbar_vec_init(ord);
        qqbar_roots_fmpz_poly(roots, zp, 0);                      /* with multiplicity, equal roots next to each other */
        Value *X = am_gen(x);
        for (slong i = 0; i < ord; ) {
            slong m = 1;
            while (i + m < ord && qqbar_equal(roots + i + m, roots + i)) m++;
            if (qqbar_is_real(roots + i)) {
                Value *rv = v_num(); ca_set_qqbar(rv->num, roots + i, am_ca);
                Value *e = v_mul(rv, X), *ex = call("exp", &e, 1);
                for (slong j = 0; j < m; j++) basis[nb++] = v_mul(v_pow(X, num_si(j)), ex);
            } else if (qqbar_sgn_im(roots + i) > 0) {
                Value *rv = v_num(); ca_set_qqbar(rv->num, roots + i, am_ca);
                Value *re = v_num(), *im = v_num();
                ca_re(re->num, rv->num, am_ca); ca_im(im->num, rv->num, am_ca);
                Value *e = v_mul(re, X), *ex = call("exp", &e, 1);
                Value *w = v_mul(im, X);
                Value *c = call("cos", &w, 1), *s = call("sin", &w, 1);
                for (slong j = 0; j < m; j++) {
                    basis[nb++] = v_mul(v_mul(v_pow(X, num_si(j)), ex), c);
                    basis[nb++] = v_mul(v_mul(v_pow(X, num_si(j)), ex), s);
                }
            }
            i += m;
        }
        _qqbar_vec_clear(roots, ord);
        fmpz_poly_clear(zp); fmpq_poly_clear(cp);
        if (nb != ord) am_fail("internal: dsolve found %d basis functions for order %d", nb, ord);
        am_work("characteristic roots give %d independent solutions", nb);
    } else if (ord == 1) {
        /* a1 y' + a0 y + r = 0: y = (C1 - integral(mu r / a1)) / mu, mu = exp(integral(a0 / a1)) */
        Value *p = v_div(coef[0], coef[1]);
        Value *ia[2] = {p, am_gen(x)};
        Value *P = call("integrate", ia, 2);
        am_status_clear();
        Value *mu = call("exp", &P, 1);
        basis[nb++] = v_div(num_si(1), mu);
        if (!is_zero_val(r)) {
            Value *ib[2] = {v_neg(v_div(v_mul(mu, r), coef[1])), am_gen(x)};
            Value *Q = call("integrate", ib, 2);
            am_status_clear();
            sol = v_div(Q, mu);
        }
        am_work("integrating factor exp(%s)", v_str_of(P));
    } else am_fail("dsolve: linear equations of order %d with non-constant coefficients are not solved yet", ord);
    /* a particular solution by variation of parameters: W u' = (0, ..., 0, -r/a_n) */
    if (!sol && !is_zero_val(r)) {
        Value *W = v_list(ord), *rhs = v_list(ord);
        for (int i = 0; i < ord; i++) {
            W->items[i] = v_list(ord);
            for (int j = 0; j < ord; j++) { Value *d = basis[j]; for (int k = 0; k < i; k++) d = D(d, x); W->items[i]->items[j] = d; }
            rhs->items[i] = i == ord - 1 ? v_neg(v_div(r, coef[ord])) : num_si(0);
        }
        Value *la[2] = {W, rhs};
        Value *u = call("linsolve", la, 2);
        am_status_clear();
        sol = num_si(0);
        for (int j = 0; j < ord; j++) {
            Value *ia[2] = {am_normal_form(am_reevaluate(u->items[j])), am_gen(x)};   /* sin^2 + cos^2 = 1 first */
            Value *U = call("integrate", ia, 2);
            sol = v_add(sol, v_mul(U, basis[j]));
        }
        am_status_clear();
        am_work("a particular solution by variation of parameters");
    }
    if (!sol) sol = num_si(0);
    {   /* the particular solution's normal form when it is shorter: x cos^2 + x sin^2 is x */
        Value *nf = am_normal_form(sol);
        if (nf->kind == V_RF || nf->kind == V_NUM) {
            char *a1 = v_str_of(nf), *b1 = v_str_of(sol);
            if (strlen(a1) < strlen(b1)) sol = nf;
            free(a1); free(b1);
        }
    }
    /* the constants */
    Value *gen = sol;
    Value *C[MAXORD];
    for (int j = 0; j < nb; j++) {
        char nm[16]; snprintf(nm, sizeof nm, "C%d", j + 1);
        C[j] = am_gen(am_var_index(nm, strlen(nm)));
        gen = v_add(gen, v_mul(C[j], basis[j]));
    }
    /* initial conditions: y^(k)(x0) = v */
    if (n == 4) {
        if (a[3]->kind != V_LIST) am_fail("dsolve: the conditions are a list [y(x0) = v0, y'(x0) = v1, ...]");
        int nc = a[3]->n;
        Value *M = v_list(nc), *rhs = v_list(nc);
        for (int i = 0; i < nc; i++) {
            Value *c = a[3]->items[i];
            int cg = c->kind == V_EQ ? am_gen_of(c->items[0]) : -1;
            if (cg < 0 || !am_vars[cg].head || am_vars[cg].nargs != 1) am_fail("dsolve: write each condition as y(x0) = value or y'(x0) = value");
            const char *h = am_vars[cg].head;
            size_t yl = strlen(y);
            if (strncmp(h, y, yl)) am_fail("dsolve: a condition on %s, not on %s", h, y);
            int k = 0;
            for (const char *t = h + yl; *t; t++) { if (*t != '\'') am_fail("dsolve: a condition on %s, not on %s", h, y); k++; }
            Value *dk = gen;
            for (int j = 0; j < k; j++) dk = D(dk, x);
            Value *at = am_reevaluate(subs_gen(dk, x, am_vars[cg].args[0]));
            M->items[i] = v_list(nb);
            for (int j = 0; j < nb; j++) { Value *dc[2] = {at, C[j]}; M->items[i]->items[j] = call("diff", dc, 2); }
            Value *rest = at;
            for (int j = 0; j < nb; j++) rest = subs_gen(rest, am_gen_of(C[j]), num_si(0));
            rhs->items[i] = v_sub(c->items[1], rest);
        }
        Value *la[2] = {M, rhs};
        Value *cs = call("linsolve", la, 2);
        am_status_clear();
        if (cs->n == 0) { am_status(S_PROVED, "the conditions contradict each other"); return v_list(0); }
        Value *val[AM_MAXVARS];
        for (int i = 0; i < am_nvars; i++) val[i] = am_gen(i);
        for (int j = 0; j < nb; j++) val[am_gen_of(C[j])] = cs->items[j];
        gen = am_reevaluate(am_subs_rf(gen, val));
    }

    int z = check(E, gen, ord, y, x);
    Value *out = v_list(2); out->kind = V_EQ;
    out->items[0] = am_gen(deriv_var(y, 0));
    out->items[1] = gen;
    if (z == 0) am_fail("internal: the solution found does not satisfy the equation");
    if (z == 1) am_status(S_PROVED, n == 4 ? "put back into the equation: it holds exactly; the conditions fix the constants" :
                                             "put back into the equation: it holds exactly; with %d constants this is the general solution of a linear equation of order %d", nb, ord);
    else if (z == 2) am_status(S_PROBABLE, "put back into the equation: it holds at random points (certified evaluation)");
    else am_status(S_UNKNOWN, "the check by substitution could not be decided");
    am_fact("constants", "%d", n == 4 ? 0 : nb);
    return out;
}
