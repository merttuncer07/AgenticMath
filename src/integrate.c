/* integrate(f, x): antiderivatives.
 *
 * Rational functions in x, exactly (Bronstein, Symbolic Integration I, ch. 2):
 *   - the polynomial part by division;
 *   - the rational part by Hermite reduction (Mack's linear version) over Q;
 *   - the logarithmic part by Rothstein-Trager: R(t) = res_x(D, A - t D'), every root alpha of R gives
 *     alpha log(gcd(D, A - alpha D')), with exact algebraic alpha (qqbar, Calcium);
 *   - a pair of complex conjugate roots becomes a log and arctangents with real coefficients (Rioboo's LogToAtan).
 * Other integrands: linearity, constant factors, integration by parts for a polynomial times exp, sin, cos, log or
 * atan of a linear argument, and the rules for integrate in the library (lib/integrate.am).
 *
 * Every antiderivative is checked: its derivative minus f is shown to be exactly 0. When that difference is a
 * rational function in x whose coefficients are algebraic numbers, it is evaluated exactly at more points than its
 * degree, which proves it is 0. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/fmpq_poly.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpz_poly_factor.h>
#include <flint/fmpz_mpoly.h>
#include <flint/ca_poly.h>
#include <flint/qqbar.h>
#include <flint/acb.h>

/* ---------------- conversions ---------------- */

/* f as num/den in Q[x], if f is a rational function of x alone with rational coefficients */
static int as_rational(const Value *f, int x, fmpq_poly_t num, fmpq_poly_t den) {
    fmpq_t q; fmpq_init(q);
    if (v_is_rational(f, q)) { fmpq_poly_set_fmpq(num, q); fmpq_poly_one(den); fmpq_clear(q); return 1; }
    fmpq_clear(q);
    if (f->kind != V_RF) return 0;
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, f->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i] && i != x) return 0;
    fmpz_poly_t n, d; fmpz_poly_init(n); fmpz_poly_init(d);
    fmpz_mpoly_get_fmpz_poly(n, fmpz_mpoly_q_numref(f->rf), x, am_mp);
    fmpz_mpoly_get_fmpz_poly(d, fmpz_mpoly_q_denref(f->rf), x, am_mp);
    fmpq_poly_set_fmpz_poly(num, n); fmpq_poly_set_fmpz_poly(den, d);
    fmpz_poly_clear(n); fmpz_poly_clear(d);
    return 1;
}

static Value *val_fmpq_poly(const fmpq_poly_t p, int x) {
    fmpz_poly_t z; fmpz_poly_init(z);
    fmpq_poly_get_numerator(z, p);
    Value *v = v_rf();
    fmpz_mpoly_set_fmpz_poly(fmpz_mpoly_q_numref(v->rf), z, x, am_mp);
    fmpz_mpoly_one(fmpz_mpoly_q_denref(v->rf), am_mp);
    Value *d = v_num();
    ca_set_fmpz(d->num, fmpq_poly_denref(p), am_ca);
    fmpz_poly_clear(z);
    return v_div(v, d);
}

static Value *val_ca(const ca_t c) { Value *v = v_num(); ca_set(v->num, c, am_ca); return v; }

static Value *val_ca_poly(const ca_poly_t p, int x) {
    Value *s = v_num(), *X = am_gen(x);
    for (slong k = p->length - 1; k >= 0; k--) s = v_add(v_mul(s, X), val_ca(p->coeffs + k));   /* Horner */
    return s;
}

static Value *call1(const char *f, Value *a) { return am_call(f, &a, 1); }

/* s a + t b = c with deg s < deg b (over Q) */
static void ext_euclid(fmpq_poly_t s, fmpq_poly_t t, const fmpq_poly_t a, const fmpq_poly_t b, const fmpq_poly_t c) {
    fmpq_poly_t g, s0, t0, q, r; fmpq_poly_init(g); fmpq_poly_init(s0); fmpq_poly_init(t0); fmpq_poly_init(q); fmpq_poly_init(r);
    fmpq_poly_xgcd(g, s0, t0, a, b);                        /* s0 a + t0 b = g */
    fmpq_poly_divrem(q, r, c, g);
    if (!fmpq_poly_is_zero(r)) am_fail("internal: Hermite reduction, the gcd does not divide");
    fmpq_poly_mul(s0, s0, q);
    fmpq_poly_divrem(q, s, s0, b);                          /* s = s0 c / g mod b */
    fmpq_poly_mul(r, s, a);
    fmpq_poly_sub(r, c, r);
    fmpq_poly_divrem(t, q, r, b);                           /* t = (c - s a) / b */
    fmpq_poly_clear(g); fmpq_poly_clear(s0); fmpq_poly_clear(t0); fmpq_poly_clear(q); fmpq_poly_clear(r);
}

/* ---------------- LogToAtan over real algebraic coefficients ---------------- */

/* g = gcd(a, b), u a + v b = g, by Euclid's algorithm over Calcium numbers */
static void ca_poly_xgcd_(ca_poly_t g, ca_poly_t u, ca_poly_t v, const ca_poly_t a, const ca_poly_t b) {
    ca_poly_t r0, r1, u0, u1, v0, v1, q, r, t;
    ca_poly_init(r0, am_ca); ca_poly_init(r1, am_ca); ca_poly_init(u0, am_ca); ca_poly_init(u1, am_ca);
    ca_poly_init(v0, am_ca); ca_poly_init(v1, am_ca); ca_poly_init(q, am_ca); ca_poly_init(r, am_ca); ca_poly_init(t, am_ca);
    ca_poly_set(r0, a, am_ca); ca_poly_set(r1, b, am_ca);
    ca_poly_one(u0, am_ca); ca_poly_zero(u1, am_ca); ca_poly_zero(v0, am_ca); ca_poly_one(v1, am_ca);
    for (int it = 0; r1->length > 0 && it < 10000; it++) {
        if (!ca_poly_divrem(q, r, r0, r1, am_ca)) am_fail("integrate: an exact division could not be decided");
        ca_poly_swap(r0, r1, am_ca); ca_poly_swap(r1, r, am_ca);
        ca_poly_mul(t, q, u1, am_ca); ca_poly_sub(t, u0, t, am_ca); ca_poly_swap(u0, u1, am_ca); ca_poly_swap(u1, t, am_ca);
        ca_poly_mul(t, q, v1, am_ca); ca_poly_sub(t, v0, t, am_ca); ca_poly_swap(v0, v1, am_ca); ca_poly_swap(v1, t, am_ca);
    }
    ca_poly_set(g, r0, am_ca); ca_poly_set(u, u0, am_ca); ca_poly_set(v, v0, am_ca);
    ca_poly_clear(r0, am_ca); ca_poly_clear(r1, am_ca); ca_poly_clear(u0, am_ca); ca_poly_clear(u1, am_ca);
    ca_poly_clear(v0, am_ca); ca_poly_clear(v1, am_ca); ca_poly_clear(q, am_ca); ca_poly_clear(r, am_ca); ca_poly_clear(t, am_ca);
}

/* a value with the same derivative as i log((A + iB)/(A - iB)), as a sum of arctangents of polynomials */
static Value *log_to_atan(const ca_poly_t A, const ca_poly_t B, int x, int depth) {
    if (depth > 200) am_fail("integrate: LogToAtan does not terminate");
    ca_poly_t q, r; ca_poly_init(q, am_ca); ca_poly_init(r, am_ca);
    if (!ca_poly_divrem(q, r, A, B, am_ca)) am_fail("integrate: an exact division could not be decided");
    Value *two = v_num(); ca_set_si(two->num, 2, am_ca);
    Value *out;
    if (r->length == 0) out = v_mul(two, call1("atan", v_div(val_ca_poly(A, x), val_ca_poly(B, x))));
    else if (A->length < B->length) {
        ca_poly_t nb; ca_poly_init(nb, am_ca); ca_poly_neg(nb, B, am_ca);
        out = log_to_atan(nb, A, x, depth + 1);
        ca_poly_clear(nb, am_ca);
    } else {
        ca_poly_t D, C, G, na, t1, t2; ca_poly_init(D, am_ca); ca_poly_init(C, am_ca); ca_poly_init(G, am_ca);
        ca_poly_init(na, am_ca); ca_poly_init(t1, am_ca); ca_poly_init(t2, am_ca);
        ca_poly_neg(na, A, am_ca);
        ca_poly_xgcd_(G, D, C, B, na);                        /* B D - A C = G */
        ca_poly_mul(t1, A, D, am_ca); ca_poly_mul(t2, B, C, am_ca); ca_poly_add(t1, t1, t2, am_ca);
        out = v_add(v_mul(two, call1("atan", v_div(val_ca_poly(t1, x), val_ca_poly(G, x)))), log_to_atan(D, C, x, depth + 1));
        ca_poly_clear(D, am_ca); ca_poly_clear(C, am_ca); ca_poly_clear(G, am_ca);
        ca_poly_clear(na, am_ca); ca_poly_clear(t1, am_ca); ca_poly_clear(t2, am_ca);
    }
    ca_poly_clear(q, am_ca); ca_poly_clear(r, am_ca);
    return out;
}

/* ---------------- rational functions ---------------- */

static Value *integrate_rational(const fmpq_poly_t num, const fmpq_poly_t den, int x) {
    fmpq_poly_t q, A, D, P;
    fmpq_poly_init(q); fmpq_poly_init(A); fmpq_poly_init(D); fmpq_poly_init(P);
    fmpq_poly_set(D, den);
    fmpq_poly_divrem(q, A, num, D);                          /* f = q + A/D */
    fmpq_poly_integral(P, q);
    Value *result = val_fmpq_poly(P, x);
    if (!fmpq_poly_is_zero(q)) am_work("polynomial part: %s", v_str_of(result));
    if (fmpq_poly_is_zero(A)) goto done;
    {   /* Hermite reduction: the rational part */
        fmpq_poly_t Dp, Dm, Ds, Dm2, Dms, Dmp, a, B, C, t, u;
        fmpq_poly_init(Dp); fmpq_poly_init(Dm); fmpq_poly_init(Ds); fmpq_poly_init(Dm2); fmpq_poly_init(Dms); fmpq_poly_init(Dmp);
        fmpq_poly_init(a); fmpq_poly_init(B); fmpq_poly_init(C); fmpq_poly_init(t); fmpq_poly_init(u);
        fmpq_poly_derivative(Dp, D);
        fmpq_poly_gcd(Dm, D, Dp);
        fmpq_poly_div(Ds, D, Dm);
        Value *g = v_num();
        int steps = 0;
        while (fmpq_poly_degree(Dm) > 0) {
            fmpq_poly_derivative(Dmp, Dm);
            fmpq_poly_gcd(Dm2, Dm, Dmp);
            fmpq_poly_div(Dms, Dm, Dm2);
            fmpq_poly_mul(t, Ds, Dmp);
            fmpq_poly_div(a, t, Dm);
            fmpq_poly_neg(a, a);                               /* a = -Ds Dm' / Dm */
            ext_euclid(B, C, a, Dms, A);                       /* B a + C Dms = A */
            fmpq_poly_derivative(t, B);
            fmpq_poly_div(u, Ds, Dms);
            fmpq_poly_mul(t, t, u);
            fmpq_poly_sub(A, C, t);                            /* A = C - B' Ds / Dms */
            g = v_add(g, v_div(val_fmpq_poly(B, x), val_fmpq_poly(Dm, x)));
            fmpq_poly_swap(Dm, Dm2);
            steps++;
        }
        if (steps) am_work("Hermite reduction: rational part %s", v_str_of(g));
        result = v_add(result, g);
        fmpq_poly_set(D, Ds);
        fmpq_poly_clear(Dp); fmpq_poly_clear(Dm); fmpq_poly_clear(Ds); fmpq_poly_clear(Dm2); fmpq_poly_clear(Dms); fmpq_poly_clear(Dmp);
        fmpq_poly_clear(a); fmpq_poly_clear(B); fmpq_poly_clear(C); fmpq_poly_clear(t); fmpq_poly_clear(u);
    }
    if (fmpq_poly_is_zero(A)) goto done;
    {   /* Rothstein-Trager: A/D with D squarefree, deg A < deg D */
        fmpz_poly_t Ai, Di; fmpz_poly_init(Ai); fmpz_poly_init(Di);
        fmpq_poly_get_numerator(Ai, A); fmpq_poly_get_numerator(Di, D);
        fmpq_t c; fmpq_init(c);                                /* A/D = c Ai/Di */
        fmpq_set_fmpz_frac(c, fmpq_poly_denref(D), fmpq_poly_denref(A));
        fmpz_mpoly_ctx_t ctx2; fmpz_mpoly_ctx_init(ctx2, 2, ORD_LEX);
        fmpz_mpoly_t mA, mD, mDp, T, R; fmpz_mpoly_init(mA, ctx2); fmpz_mpoly_init(mD, ctx2); fmpz_mpoly_init(mDp, ctx2);
        fmpz_mpoly_init(T, ctx2); fmpz_mpoly_init(R, ctx2);
        fmpz_poly_t Dpi; fmpz_poly_init(Dpi); fmpz_poly_derivative(Dpi, Di);
        fmpz_mpoly_set_fmpz_poly(mA, Ai, 0, ctx2); fmpz_mpoly_set_fmpz_poly(mD, Di, 0, ctx2); fmpz_mpoly_set_fmpz_poly(mDp, Dpi, 0, ctx2);
        fmpz_mpoly_gen(T, 1, ctx2);
        fmpz_mpoly_mul(T, T, mDp, ctx2);
        fmpz_mpoly_sub(T, mA, T, ctx2);                        /* Ai - t Di' */
        if (!fmpz_mpoly_resultant(R, mD, T, 0, ctx2)) am_fail("integrate: the resultant could not be computed");
        fmpz_poly_t Rt; fmpz_poly_init(Rt);
        fmpz_mpoly_get_fmpz_poly(Rt, R, 1, ctx2);
        fmpz_poly_factor_t F; fmpz_poly_factor_init(F);
        fmpz_poly_factor(F, Rt);
        Value *logs = v_num();
        int nlog = 0, natan = 0;
        for (slong i = 0; i < F->num; i++) {
            slong d = fmpz_poly_degree(F->p + i);
            if (d < 1) continue;
            qqbar_ptr roots = _qqbar_vec_init(d);
            qqbar_roots_fmpz_poly(roots, F->p + i, QQBAR_ROOTS_IRREDUCIBLE);
            for (slong k = 0; k < d; k++) {
                ca_t al; ca_init(al, am_ca);
                ca_set_qqbar(al, roots + k, am_ca);
                ca_mul_fmpq(al, al, c, am_ca);                 /* the coefficient of the log, for A/D */
                ca_poly_t cD, cA, cS; ca_poly_init(cD, am_ca); ca_poly_init(cA, am_ca); ca_poly_init(cS, am_ca);
                ca_poly_set_fmpz_poly(cD, Di, am_ca);
                ca_poly_set_fmpz_poly(cA, Ai, am_ca);
                ca_t r; ca_init(r, am_ca);
                ca_set_qqbar(r, roots + k, am_ca);
                ca_poly_t cDp; ca_poly_init(cDp, am_ca); ca_poly_derivative(cDp, cD, am_ca);
                ca_poly_t t2; ca_poly_init(t2, am_ca);
                for (slong j = 0; j < cDp->length; j++) {}
                ca_poly_set(t2, cDp, am_ca);
                for (slong j = 0; j < t2->length; j++) ca_mul(t2->coeffs + j, t2->coeffs + j, r, am_ca);
                ca_poly_sub(cA, cA, t2, am_ca);                /* Ai - root Di' */
                if (!ca_poly_gcd(cS, cD, cA, am_ca)) am_fail("integrate: a gcd over algebraic numbers could not be decided");
                ca_poly_make_monic(cS, cS, am_ca);
                int real = qqbar_is_real(roots + k);
                if (real) {
                    logs = v_add(logs, v_mul(val_ca(al), call1("log", val_ca_poly(cS, x))));
                    nlog++;
                } else if (qqbar_sgn_im(roots + k) > 0) {      /* with its conjugate: a log(A^2 + B^2) + b LogToAtan(A, B) */
                    ca_poly_t cAr, cBi, s2; ca_poly_init(cAr, am_ca); ca_poly_init(cBi, am_ca); ca_poly_init(s2, am_ca);
                    ca_poly_fit_length(cAr, cS->length, am_ca); ca_poly_fit_length(cBi, cS->length, am_ca);
                    for (slong j = 0; j < cS->length; j++) { ca_re(cAr->coeffs + j, cS->coeffs + j, am_ca); ca_im(cBi->coeffs + j, cS->coeffs + j, am_ca); }
                    _ca_poly_set_length(cAr, cS->length, am_ca); _ca_poly_normalise(cAr, am_ca);
                    _ca_poly_set_length(cBi, cS->length, am_ca); _ca_poly_normalise(cBi, am_ca);
                    ca_t a, b; ca_init(a, am_ca); ca_init(b, am_ca);
                    ca_re(a, al, am_ca); ca_im(b, al, am_ca);
                    ca_poly_mul(s2, cAr, cAr, am_ca);
                    ca_poly_t s3; ca_poly_init(s3, am_ca); ca_poly_mul(s3, cBi, cBi, am_ca); ca_poly_add(s2, s2, s3, am_ca); ca_poly_clear(s3, am_ca);
                    if (ca_check_is_zero(a, am_ca) != T_TRUE) { logs = v_add(logs, v_mul(val_ca(a), call1("log", val_ca_poly(s2, x)))); nlog++; }
                    logs = v_add(logs, v_mul(val_ca(b), log_to_atan(cAr, cBi, x, 0)));
                    natan++;
                    ca_clear(a, am_ca); ca_clear(b, am_ca);
                    ca_poly_clear(cAr, am_ca); ca_poly_clear(cBi, am_ca); ca_poly_clear(s2, am_ca);
                }
                ca_clear(al, am_ca); ca_clear(r, am_ca);
                ca_poly_clear(cD, am_ca); ca_poly_clear(cA, am_ca); ca_poly_clear(cS, am_ca); ca_poly_clear(cDp, am_ca); ca_poly_clear(t2, am_ca);
            }
            _qqbar_vec_clear(roots, d);
        }
        char *rs = fmpz_poly_get_str_pretty(Rt, "t");
        am_work("Rothstein-Trager: R(t) = %s; %d log term%s, %d arctangent pair%s", rs, nlog, nlog == 1 ? "" : "s", natan, natan == 1 ? "" : "s");
        flint_free(rs);
        result = v_add(result, logs);
        fmpz_poly_factor_clear(F); fmpz_poly_clear(Rt); fmpz_poly_clear(Dpi);
        fmpz_mpoly_clear(mA, ctx2); fmpz_mpoly_clear(mD, ctx2); fmpz_mpoly_clear(mDp, ctx2); fmpz_mpoly_clear(T, ctx2); fmpz_mpoly_clear(R, ctx2);
        fmpz_mpoly_ctx_clear(ctx2);
        fmpz_poly_clear(Ai); fmpz_poly_clear(Di); fmpq_clear(c);
    }
done:
    fmpq_poly_clear(q); fmpq_poly_clear(A); fmpq_poly_clear(D); fmpq_poly_clear(P);
    return result;
}

/* ---------------- other integrands ---------------- */

static int unevaluated(const Value *v) {                     /* contains an integrate(...) term */
    if (v->kind == V_LIST || v->kind == V_EQ) { for (int i = 0; i < v->n; i++) if (unevaluated(v->items[i])) return 1; return 0; }
    if (v->kind != V_RF) return 0;
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i] && am_vars[i].head && !strcmp(am_vars[i].head, "integrate")) return 1;
    return 0;
}

static Value *integrate_any(Value *f, int x, int depth);
Value *rf_den_value(const Value *t);

/* the library's rules for antiderivative(f, x); when none applies, integrate(f, x) left as it is */
static Value *by_rules(Value *t, int x) {
    Value *a[2] = {t, am_gen(x)};
    Value *r = am_call("antiderivative", a, 2);
    int g = am_gen_of(r);
    if (g >= 0 && am_vars[g].head && !strcmp(am_vars[g].head, "antiderivative")) return am_kernel_value("integrate", a, 2);
    return r;
}

/* G with t replaced by v, function terms re-evaluated (log(t) becomes log(cos(u))) */
static Value *back_subs(Value *G, int t, Value *v) {
    Value *eq = v_list(2); eq->kind = V_EQ; eq->items[0] = am_gen(t); eq->items[1] = v;
    Value *a[2] = {G, eq};
    return am_call("subs", a, 2);
}

/* sin(u)^m cos(u)^n (u linear in x; m, n may be negative): t = cos(u) when m is odd, t = sin(u) when n is odd
 * (a rational integral in t); both even and not negative: cos^2 = (1 + cos 2u)/2, sin^2 = (1 - cos 2u)/2 */
static Value *trig_powers(Value *t, int x, int depth) {
    if (t->kind != V_RF) return NULL;
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, t->rf, am_mp);
    int sv = -1, cv = -1;
    Value *u = NULL;
    for (int i = 0; i < am_nvars; i++) {
        if (!used[i]) continue;
        if (i == x) return NULL;
        if (!am_vars[i].kernel || am_vars[i].numval || am_free_of(am_gen(i), x)) continue;
        const char *h = am_vars[i].head;
        if (!h || am_vars[i].nargs != 1 || (strcmp(h, "sin") && strcmp(h, "cos"))) return NULL;
        Value *ui = am_vars[i].args[0];
        if (u) { char *a = v_str_of(u), *b = v_str_of(ui); int same = !strcmp(a, b); free(a); free(b); if (!same) return NULL; }
        u = ui;
        if (h[0] == 's') sv = i; else cv = i;
    }
    if (!u) return NULL;
    Value *ua[2] = {u, am_gen(x)};
    Value *du = am_call("diff", ua, 2);
    if (!am_free_of(du, x) || (du->kind == V_NUM && ca_check_is_zero(du->num, am_ca) == T_TRUE)) return NULL;
    /* the exponents: t = c * s^m * c^n with c free of x, from the numerator and denominator monomials */
    const fmpz_mpoly_struct *N = fmpz_mpoly_q_numref(t->rf), *D = fmpz_mpoly_q_denref(t->rf);
    if (fmpz_mpoly_length(N, am_mp) != 1 || fmpz_mpoly_length(D, am_mp) != 1) return NULL;
    slong m = (sv >= 0 ? fmpz_mpoly_degree_si(N, sv, am_mp) - fmpz_mpoly_degree_si(D, sv, am_mp) : 0);
    slong nn = (cv >= 0 ? fmpz_mpoly_degree_si(N, cv, am_mp) - fmpz_mpoly_degree_si(D, cv, am_mp) : 0);
    if (m > 40 || nn > 40 || m < -40 || nn < -40) return NULL;
    Value *S = sv >= 0 ? am_gen(sv) : NULL, *C = cv >= 0 ? am_gen(cv) : NULL;
    Value *trigpart;
    Value *em = v_num(); ca_set_si(em->num, m, am_ca);
    Value *en = v_num(); ca_set_si(en->num, nn, am_ca);
    if (S && C) trigpart = v_mul(v_pow(S, em), v_pow(C, en));
    else trigpart = S ? v_pow(S, em) : v_pow(C, en);
    Value *coef = v_div(t, trigpart);
    if (!am_free_of(coef, x)) return NULL;
    int tv = am_var_index("t_trig", 6);
    Value *T = am_gen(tv), *one = v_num(); ca_one(one->num, am_ca);
    Value *R = NULL;
    if (m & 1) {                                                /* t = cos u: -1/u' int (1 - t^2)^((m-1)/2) t^n dt */
        if (m < 0) return NULL;
        Value *h = v_num(); ca_set_si(h->num, (m - 1) / 2, am_ca);
        Value *g = v_mul(v_pow(v_sub(one, v_mul(T, T)), h), v_pow(T, en));
        Value *G = integrate_any(g, tv, depth + 1);
        R = v_neg(v_div(back_subs(G, tv, am_call("cos", &u, 1)), du));
    } else if (nn & 1) {                                        /* t = sin u: 1/u' int t^m (1 - t^2)^((n-1)/2) dt */
        if (nn < 0) return NULL;
        Value *h = v_num(); ca_set_si(h->num, (nn - 1) / 2, am_ca);
        Value *g = v_mul(v_pow(T, em), v_pow(v_sub(one, v_mul(T, T)), h));
        Value *G = integrate_any(g, tv, depth + 1);
        R = v_div(back_subs(G, tv, am_call("sin", &u, 1)), du);
    } else if (m < 0 || nn < 0) {                               /* both even, one negative: t = tan u, du = dt/(1 + t^2) */
        /* sin^m cos^n = t^m (1 + t^2)^(-(m + n)/2) */
        slong e = -(m + nn) / 2 - 1;
        Value *g = v_mul(v_pow(T, em), v_pow(v_add(one, v_mul(T, T)), (({ Value *ev = v_num(); ca_set_si(ev->num, e, am_ca); ev; }))));
        Value *G = integrate_any(g, tv, depth + 1);
        Value *back = back_subs(G, tv, am_call("tan", &u, 1));
        /* atan(tan(u)) -> u: equal up to constants between the poles, which an antiderivative allows (checked below) */
        if (back->kind == V_RF) {
            int us[AM_MAXVARS] = {0}, n1 = am_nvars;
            fmpz_mpoly_q_used_vars(us, back->rf, am_mp);
            Value *val[AM_MAXVARS];
            for (int i = 0; i < n1; i++) {
                val[i] = am_gen(i);
                if (us[i] && am_vars[i].head && !strcmp(am_vars[i].head, "atan") && am_vars[i].nargs == 1) {
                    int g2 = am_gen_of(am_vars[i].args[0]);
                    if (g2 >= 0 && am_vars[g2].head && !strcmp(am_vars[g2].head, "tan")) val[i] = am_vars[g2].args[0];
                }
            }
            back = am_subs_rf(back, val);
        }
        R = v_div(back, du);
    } else if (m >= 0 && nn >= 0 && m + nn > 0) {               /* both even: lower the powers with cos(2u) */
        Value *two = v_num(); ca_set_si(two->num, 2, am_ca);
        Value *u2 = v_mul(two, u), *c2 = am_call("cos", &u2, 1);
        Value *s2h = v_div(v_sub(one, c2), two), *c2h = v_div(v_add(one, c2), two);
        Value *hm = v_num(); ca_set_si(hm->num, m / 2, am_ca);
        Value *hn = v_num(); ca_set_si(hn->num, nn / 2, am_ca);
        Value *lowered = v_mul(v_pow(s2h, hm), v_pow(c2h, hn));
        R = integrate_any(lowered, x, depth + 1);
    } else return NULL;
    if (R) am_work("powers of sin and cos of %s by substitution", v_str_of(u));
    return R ? v_mul(coef, R) : NULL;
}

/* the antiderivative of a single term: c * x^k * (product of function terms) / D */
static Value *integrate_term(Value *t, int x, int depth) {
    { Value *r = trig_powers(t, x, depth); if (r) return r; }
    if (am_free_of(t, x)) return v_mul(t, am_gen(x));
    /* split off the factor free of x: in the numerator's single monomial and the denominator */
    fmpq_poly_t n, d; fmpq_poly_init(n); fmpq_poly_init(d);
    if (as_rational(t, x, n, d)) { Value *r = integrate_rational(n, d, x); fmpq_poly_clear(n); fmpq_poly_clear(d); return r; }
    fmpq_poly_clear(n); fmpq_poly_clear(d);
    const fmpz_mpoly_struct *N = fmpz_mpoly_q_numref(t->rf);
    Value *Xv = am_gen(x);
    if (fmpz_mpoly_length(N, am_mp) == 1) {
        ulong ex[AM_MAXVARS]; fmpz_t c; fmpz_init(c);
        fmpz_mpoly_get_term_exp_ui(ex, N, 0, am_mp);
        fmpz_mpoly_get_term_coeff_fmpz(c, N, 0, am_mp);
        Value *cons = v_num(); ca_set_fmpz(cons->num, c, am_ca);
        Value *dep = v_num(); ca_one(dep->num, am_ca);
        int nker = 0, kv = -1;
        for (int i = 0; i < am_nvars; i++) {
            if (!ex[i]) continue;
            Value *e = v_num(); ca_set_ui(e->num, ex[i], am_ca);
            Value *pw = v_pow(am_gen(i), e);
            if (am_free_of(am_gen(i), x)) cons = v_mul(cons, pw);
            else { dep = v_mul(dep, pw); if (i != x) { nker++; kv = i; } }
        }
        fmpz_clear(c);
        Value *Dv = rf_den_value(t);
        if (am_free_of(Dv, x)) {
            cons = v_div(cons, Dv);
            Value *cf = v_num(); ca_one(cf->num, am_ca);
            if (!(cons->kind == V_NUM && ca_check_is_one(cons->num, am_ca) == T_TRUE)) {
                Value *r = integrate_any(dep, x, depth + 1);
                return v_mul(cons, r);
            }
            /* polynomial in x times one function term with exponent 1: by parts */
            if (nker == 1 && ex[kv] == 1 && am_vars[kv].head) {
                slong k = (slong)ex[x];
                const char *h = am_vars[kv].head;
                Value *K = am_gen(kv);
                if (k > 0 && (!strcmp(h, "exp") || !strcmp(h, "sin") || !strcmp(h, "cos"))) {
                    Value *I = by_rules(K, x);                  /* int x^k K = x^k I - k int x^(k-1) I, I = int K */
                    if (!unevaluated(I)) {
                        Value *e = v_num(); ca_set_si(e->num, k, am_ca);
                        Value *e1 = v_num(); ca_set_si(e1->num, k - 1, am_ca);
                        am_work("by parts: the integral of %s times a power of %s", am_vars[kv].name, am_varnames[x]);
                        return v_sub(v_mul(v_pow(Xv, e), I), v_mul(e, integrate_any(v_mul(v_pow(Xv, e1), I), x, depth + 1)));
                    }
                }
                if (!strcmp(h, "log") || !strcmp(h, "atan")) {     /* int p K = P K - int P K', P = int p, K' rational */
                    Value *e = v_num(); ca_set_si(e->num, k, am_ca);
                    Value *p = v_pow(Xv, e);
                    Value *P = integrate_any(p, x, depth + 1);
                    Value *a[2] = {K, Xv};
                    Value *dK = am_call("diff", a, 2);
                    am_work("by parts: %s times a power of %s", am_vars[kv].name, am_varnames[x]);
                    return v_sub(v_mul(P, K), integrate_any(v_mul(P, dK), x, depth + 1));
                }
            }
        }
    }
    return by_rules(t, x);                                     /* the library's rules, else integrate(t, x) unevaluated */
}

Value *rf_den_value(const Value *t) {
    Value *v = v_rf();
    fmpz_mpoly_set(fmpz_mpoly_q_numref(v->rf), fmpz_mpoly_q_denref(t->rf), am_mp);
    fmpz_mpoly_one(fmpz_mpoly_q_denref(v->rf), am_mp);
    return v;
}

/* exp(u)^k below the line becomes exp(-k u) above it (multiplying by 1 = exp(u)^k exp(-k u)) */
static Value *lift_exp(Value *f) {
    if (f->kind != V_RF) return f;
    const fmpz_mpoly_struct *D = fmpz_mpoly_q_denref(f->rf);
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_used_vars(used, D, am_mp);
    int n0 = am_nvars;
    for (int i = 0; i < n0; i++) {
        if (!used[i] || !am_vars[i].head || strcmp(am_vars[i].head, "exp") || am_vars[i].nargs != 1) continue;
        slong k = fmpz_mpoly_degree_si(D, i, am_mp);
        if (k <= 0) continue;
        Value *ek = v_num(); ca_set_si(ek->num, k, am_ca);
        Value *nu = v_neg(v_mul(ek, am_vars[i].args[0]));
        Value *inv = am_call("exp", &nu, 1);
        f = v_mul(v_mul(f, v_pow(am_gen(i), ek)), inv);
    }
    return f;
}

/* tan(u) as sin(u)/cos(u), so that powers of sin and cos cover it */
static Value *tan_to_sincos(Value *f) {
    if (f->kind != V_RF) return f;
    int used[AM_MAXVARS] = {0}, any = 0, n0 = am_nvars;
    fmpz_mpoly_q_used_vars(used, f->rf, am_mp);
    Value *val[AM_MAXVARS];
    for (int i = 0; i < n0; i++) {
        val[i] = am_gen(i);
        if (used[i] && am_vars[i].head && !strcmp(am_vars[i].head, "tan") && am_vars[i].nargs == 1) {
            Value *a = am_vars[i].args[0];
            val[i] = v_div(am_call("sin", &a, 1), am_call("cos", &a, 1));
            any = 1;
        }
    }
    return any ? am_subs_rf(f, val) : f;
}

static Value *integrate_any(Value *f, int x, int depth) {
    if (depth > 50) am_fail("integrate: too deep");
    if (f->kind == V_NUM) return v_mul(f, am_gen(x));
    if (f->kind != V_RF) am_fail("integrate needs an expression");
    f = lift_exp(tan_to_sincos(f));
    if (f->kind == V_NUM) return v_mul(f, am_gen(x));
    fmpq_poly_t n, d; fmpq_poly_init(n); fmpq_poly_init(d);
    if (as_rational(f, x, n, d)) { Value *r = integrate_rational(n, d, x); fmpq_poly_clear(n); fmpq_poly_clear(d); return r; }
    fmpq_poly_clear(n); fmpq_poly_clear(d);
    const fmpz_mpoly_struct *N = fmpz_mpoly_q_numref(f->rf);
    Value *Dv = rf_den_value(f);
    {   /* linearity: the numerator grouped by its function-term part, each group's polynomial in x over the denominator */
        slong len = fmpz_mpoly_length(N, am_mp);
        ulong (*keys)[AM_MAXVARS] = calloc((size_t)(len ? len : 1), sizeof *keys);
        int *grp = calloc((size_t)(len ? len : 1), sizeof(int)), ng = 0;
        ulong ex[AM_MAXVARS];
        for (slong i = 0; i < len; i++) {
            fmpz_mpoly_get_term_exp_ui(ex, N, i, am_mp);
            ex[x] = 0;
            int g = -1;
            for (int j = 0; j < ng && g < 0; j++) if (!memcmp(keys[j], ex, sizeof ex)) g = j;
            if (g < 0) { g = ng++; memcpy(keys[g], ex, sizeof ex); }
            grp[i] = g;
        }
        if (ng > 1) {
            Value *sum = v_num();
            fmpz_mpoly_t term, acc; fmpz_mpoly_init(term, am_mp); fmpz_mpoly_init(acc, am_mp);
            for (int g = 0; g < ng; g++) {
                fmpz_mpoly_zero(acc, am_mp);
                for (slong i = 0; i < len; i++) if (grp[i] == g) { fmpz_mpoly_get_term(term, N, i, am_mp); fmpz_mpoly_add(acc, acc, term, am_mp); }
                Value *tv = v_rf();
                fmpz_mpoly_set(fmpz_mpoly_q_numref(tv->rf), acc, am_mp);
                fmpz_mpoly_one(fmpz_mpoly_q_denref(tv->rf), am_mp);
                sum = v_add(sum, integrate_any(v_div(tv, Dv), x, depth + 1));
            }
            fmpz_mpoly_clear(term, am_mp); fmpz_mpoly_clear(acc, am_mp);
            free(keys); free(grp);
            return sum;
        }
        free(keys); free(grp);
    }
    if (fmpz_mpoly_length(N, am_mp) > 1) {                    /* one group: linearity over its terms */
        Value *sum = v_num();
        fmpz_mpoly_t term; fmpz_mpoly_init(term, am_mp);
        for (slong i = 0; i < fmpz_mpoly_length(N, am_mp); i++) {
            fmpz_mpoly_get_term(term, N, i, am_mp);
            Value *tv = v_rf();
            fmpz_mpoly_set(fmpz_mpoly_q_numref(tv->rf), term, am_mp);
            fmpz_mpoly_one(fmpz_mpoly_q_denref(tv->rf), am_mp);
            sum = v_add(sum, integrate_term(v_div(tv, Dv), x, depth));
        }
        fmpz_mpoly_clear(term, am_mp);
        if (!unevaluated(sum)) return sum;
        Value *whole = by_rules(f, x);                          /* term by term failed: the rules on the whole */
        return unevaluated(whole) ? sum : whole;
    }
    return integrate_term(f, x, depth);
}

/* ---------------- the check: derivative minus integrand is 0 ---------------- */

static truth_t is_zero_in_x(Value *d, int x) {
    if (d->kind == V_NUM) return ca_check_is_zero(d->num, am_ca);
    if (d->kind != V_RF) return T_UNKNOWN;
    if (fmpz_mpoly_q_is_zero(d->rf, am_mp)) return T_TRUE;
    /* the numerator, a polynomial in x and algebraic constants, evaluated exactly at deg + 1 points */
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, d->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i] && i != x && !(am_vars[i].kernel && am_vars[i].numval)) return T_UNKNOWN;
    slong deg = fmpz_mpoly_degree_si(fmpz_mpoly_q_numref(d->rf), x, am_mp);
    Value *num = v_rf();
    fmpz_mpoly_set(fmpz_mpoly_q_numref(num->rf), fmpz_mpoly_q_numref(d->rf), am_mp);
    fmpz_mpoly_one(fmpz_mpoly_q_denref(num->rf), am_mp);
    Value *val[AM_MAXVARS];
    for (int i = 0; i < am_nvars; i++) val[i] = am_vars[i].numval ? am_vars[i].numval : am_gen(i);
    for (slong k = 0; k <= deg; k++) {
        Value *pt = v_num(); ca_set_si(pt->num, 7 + 3 * k, am_ca);
        val[x] = pt;
        Value *r = am_subs_rf(num, val);
        if (r->kind != V_NUM) return T_UNKNOWN;
        truth_t z = ca_check_is_zero(r->num, am_ca);
        if (z != T_TRUE) return z;
    }
    return T_TRUE;
}

int am_integrate_numeric(acb_t res, Value *f, int x, Value *a, Value *b, slong digits);
int am_eval_acb(acb_t out, Value *f, int x, const acb_t z, int analytic, slong prec);
Value *b_limit(Value **a, int n);
static Value *indefinite(Value **a, int n);

static int is_inf(Value *v) { return v->kind == V_NUM && ca_is_special(v->num, am_ca); }

/* a ball as a decimal string with only correct digits */
static Value *ball_value(const acb_t r, slong digits) {
    char *re = arb_get_str(acb_realref(r), digits, ARB_STR_NO_RADIUS);
    Value *v;
    if (arb_is_zero(acb_imagref(r)) || arb_contains_zero(acb_imagref(r))) v = v_str(re);
    else {
        char *im = arb_get_str(acb_imagref(r), digits, ARB_STR_NO_RADIUS);
        char *s = malloc(strlen(re) + strlen(im) + 8);
        sprintf(s, "%s + %s*I", re, im);
        v = v_str(s);
        free(s); flint_free(im);
    }
    flint_free(re);
    return v;
}

/* built from x, constants, exp, sin and cos with only constants below the line: continuous everywhere */
static int entire(Value *F, int x) {
    if (F->kind == V_NUM) return 1;
    if (F->kind != V_RF) return 0;
    Value *D = rf_den_value(F);
    if (!am_free_of(D, x)) return 0;
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, F->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) {
        if (!used[i] || !am_vars[i].kernel || am_vars[i].numval || am_free_of(am_gen(i), x)) continue;
        const char *h = am_vars[i].head;
        if (!h || (strcmp(h, "exp") && strcmp(h, "sin") && strcmp(h, "cos")) || !entire(am_vars[i].args[0], x)) return 0;
    }
    return 1;
}

/* integrate(f, x, a, b) */
static Value *definite(Value *f, Value *xv, Value *a, Value *b) {
    int x = am_gen_of(xv);
    if (!am_free_of(a, x) || !am_free_of(b, x)) am_fail("integrate: the limits must not depend on %s", am_varnames[x]);
    int finite = !is_inf(a) && !is_inf(b);
    /* a rational integrand with a pole on the interval does not have an integral */
    fmpq_poly_t n, d; fmpq_poly_init(n); fmpq_poly_init(d);
    int rational = as_rational(f, x, n, d);
    if (rational && fmpq_poly_degree(d) > 0) {
        fmpz_poly_t dz; fmpz_poly_init(dz); fmpq_poly_get_numerator(dz, d);
        slong deg = fmpz_poly_degree(dz);
        qqbar_ptr r = _qqbar_vec_init(deg);
        qqbar_roots_fmpz_poly(r, dz, 0);
        for (slong k = 0; k < deg; k++) {
            if (!qqbar_is_real(r + k)) continue;
            Value *rv = v_num(); ca_set_qqbar(rv->num, r + k, am_ca);
            Value *lo = a, *hi = b;
            if (finite && a->kind == V_NUM && b->kind == V_NUM && ca_check_gt(a->num, b->num, am_ca) == T_TRUE) { lo = b; hi = a; }
            int above = is_inf(lo) ? (ca_check_is_neg_inf(lo->num, am_ca) == T_TRUE) : (lo->kind == V_NUM && ca_check_ge(rv->num, lo->num, am_ca) == T_TRUE);
            int below = is_inf(hi) ? (ca_check_is_pos_inf(hi->num, am_ca) == T_TRUE) : (hi->kind == V_NUM && ca_check_le(rv->num, hi->num, am_ca) == T_TRUE);
            if (above && below) {
                char *rs = v_str_of(rv);
                am_status(S_PROVED, "the integrand has a pole at %s = %s on the interval, where it is not integrable", am_varnames[x], rs);
                char *js = am_json_str(rs); am_fact("pole", "%s", js); free(js); free(rs);
                am_fact("converges", "false");
                _qqbar_vec_clear(r, deg); fmpz_poly_clear(dz);
                return v_str("diverges");
            }
        }
        _qqbar_vec_clear(r, deg); fmpz_poly_clear(dz);
    }
    fmpq_poly_clear(n); fmpq_poly_clear(d);
    /* the antiderivative, then its limits at the ends */
    Value *ia[2] = {f, xv};
    Value *F = indefinite(ia, 2);
    Status inner = am_status_get();
    char inner_why[512]; snprintf(inner_why, sizeof inner_why, "the antiderivative's check was not complete");
    acb_t num; acb_init(num);
    int have_num = finite && am_integrate_numeric(num, f, x, a, b, 30);
    if (unevaluated(F)) {
        if (!have_num) { acb_clear(num); am_fail("integrate: no antiderivative found and no certified numerical value (an infinite interval, or a singularity on it)"); }
        am_account_reset();
        am_status(S_CERTIFIED, "no antiderivative found; the value by certified numerical integration (Arb), every digit shown correct");
        am_fact("antiderivative_found", "false");
        Value *r = ball_value(num, 30);
        acb_clear(num);
        return r;
    }
    Value *la[4] = {F, xv, b, v_str("-")}, *lb[4] = {F, xv, a, v_str("+")};
    am_fact_mute++;
    Value *Fb = b_limit(la, is_inf(b) ? 3 : 4), *Fa = b_limit(lb, is_inf(a) ? 3 : 4);
    am_fact_mute--;
    if (Fb->kind == V_STR || Fa->kind == V_STR) am_fail("integrate: the antiderivative has no limit at an end of the interval");
    Value *exact = am_reevaluate(v_sub(Fb, Fa));
    am_status_clear();                                         /* the definite integral gets its own verdict */
    if (inner == S_PROBABLE || inner == S_UNKNOWN || inner == S_NUMERIC) am_status(inner, "%s", inner_why);
    if (exact->kind == V_NUM && ca_is_special(exact->num, am_ca)) {
        am_status(S_PROVED, "the antiderivative tends to infinity at an end of the interval");
        am_fact("converges", "false");
        acb_clear(num);
        return v_str("diverges");
    }
    if (have_num) {
        acb_t ex; acb_init(ex);
        int ok = am_eval_acb(ex, exact, x, ex, 0, 128);
        if (ok && !acb_overlaps(ex, num)) {                     /* the antiderivative jumps inside the interval */
            am_account_reset();
            am_status(S_CERTIFIED, "the antiderivative found is not continuous on the interval; the value by certified numerical integration (Arb)");
            am_fact("antiderivative_continuous", "false");
            Value *r = ball_value(num, 30);
            acb_clear(ex); acb_clear(num);
            return r;
        }
        acb_clear(ex);
        if (rational) am_status(S_PROVED, "F(b) - F(a) for a checked antiderivative, continuous on the interval (no pole there); agrees with certified numerical integration");
        else if (entire(F, x)) am_status(S_PROVED, "F(b) - F(a) for a checked antiderivative built from polynomials, exp, sin and cos, hence continuous; agrees with certified numerical integration");
        else am_status(S_PROBABLE, "F(b) - F(a) for a checked antiderivative; agrees with certified numerical integration to 30 digits, its continuity on the interval is not proved");
        am_fact("numerical_check", "\"agrees to 30 digits (Arb)\"");
    } else if (rational) am_status(S_PROVED, "F(b) - F(a) for a checked antiderivative, continuous on the interval (no pole there)");
    else if (entire(F, x)) am_status(S_PROVED, "F(b) - F(a) for a checked antiderivative built from polynomials, exp, sin and cos, hence continuous");
    else {
        am_status(S_EXACT, "F(b) - F(a) for a checked antiderivative; continuity on the interval not checked (no certified numerical value)");
        am_fact("continuity_checked", "false");
    }
    acb_clear(num);
    return exact;
}

Value *b_integrate(Value **a, int n) {
    if (n == 4) {
        int g = am_gen_of(a[1]);
        if (g < 0 || am_vars[g].kernel) { char *s_ = v_str_of(a[1]); am_fail("integrate: the second argument must be a variable (got %s)", s_); }
        return definite(a[0], a[1], a[2], a[3]);
    }
    return indefinite(a, n);
}

static Value *indefinite(Value **a, int n) {
    if (n != 2) am_fail("integrate(f, x) or integrate(f, x, a, b)");
    int x = -1;
    {
        int g = am_gen_of(a[1]);
        if (g < 0 || am_vars[g].kernel) { char *s_ = v_str_of(a[1]); am_fail("integrate: the second argument must be a variable (got %s)", s_); }
        x = g;
    }
    Value *f = a[0];
    if (f->kind == V_LIST) {
        Value *r = v_list(f->n);
        for (int i = 0; i < f->n; i++) { Value *b[2] = {f->items[i], a[1]}; r->items[i] = indefinite(b, 2); }
        return r;
    }
    Value *F = integrate_any(f, x, 0);
    if (unevaluated(F)) {
        am_status(S_UNKNOWN, "no antiderivative found for part of the integrand; that part is left as integrate(...)");
        am_fact("antiderivative_found", "false");
        return F;
    }
    Value *b[2] = {F, a[1]};
    Value *dF = am_call("diff", b, 2);
    Value *diffr = am_reevaluate(v_sub(dF, f));
    truth_t z = is_zero_in_x(diffr, x);
    int zt = z == T_TRUE ? 1 : z == T_FALSE ? 0 : am_zero_test(diffr, NULL, 0);
    if (zt == 0) am_fail("internal: the antiderivative found does not differentiate back to the integrand");
    am_fact("antiderivative_found", "true");
    if (zt == 1) {
        am_status(S_PROVED, "checked: its derivative equals the integrand exactly (add any constant)");
        am_fact("verified_by", "\"differentiation\"");
    } else if (zt == 2) {
        am_status(S_PROBABLE, "its derivative equals the integrand at 5 random points (certified evaluation), not proved symbolically");
        am_fact("verified_by", "\"differentiation, numerically at random points\"");
    } else am_status(S_UNKNOWN, "an antiderivative was found by rules, but the check by differentiation could not be decided");
    return F;
}
