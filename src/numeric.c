/* Certified numerics: an expression evaluated on a complex ball (Arb), and integrals by Arb's rigorous
 * quadrature (Gauss-Legendre with error bounds from analyticity, Petras' algorithm). Every number that leaves
 * here is an enclosure: the true value lies inside. */
#include "am.h"

#include <stdlib.h>
#include <string.h>

#include <flint/acb.h>
#include <flint/acb_calc.h>
#include <flint/acb_hypgeom.h>

/* f at the ball z for the variable x: 1 on success, 0 if f is not analytic there (when analytic is asked) or has
 * other free variables */
int am_eval_acb(acb_t out, Value *f, int x, const acb_t z, int analytic, slong prec);

static int eval_gen(acb_t out, int g, int x, const acb_t z, int analytic, slong prec) {
    if (g == x) { acb_set(out, z); return 1; }
    if (!am_vars[g].kernel) return 0;                           /* another variable: no number */
    if (am_vars[g].numval) { ca_get_acb(out, am_vars[g].numval->num, prec, am_ca); return 1; }
    if (am_vars[g].nargs != 1) return 0;
    acb_t u; acb_init(u);
    int ok = am_eval_acb(u, am_vars[g].args[0], x, z, analytic, prec);
    const char *h = am_vars[g].head;
    if (ok) {
        if (!strcmp(h, "exp")) acb_exp(out, u, prec);
        else if (!strcmp(h, "sin")) acb_sin(out, u, prec);
        else if (!strcmp(h, "cos")) acb_cos(out, u, prec);
        else if (!strcmp(h, "tan")) acb_tan(out, u, prec);
        else if (!strcmp(h, "log")) acb_log_analytic(out, u, analytic, prec);
        else if (!strcmp(h, "sqrt")) acb_sqrt_analytic(out, u, analytic, prec);
        else if (!strcmp(h, "abs")) acb_real_abs(out, u, analytic, prec);
        else if (!strcmp(h, "gamma")) acb_gamma(out, u, prec);
        else if (!strcmp(h, "erf")) acb_hypgeom_erf(out, u, prec);
        else if (!strcmp(h, "zeta")) acb_zeta(out, u, prec);
        else if (!strcmp(h, "Si")) acb_hypgeom_si(out, u, prec);
        else if (!strcmp(h, "atan") || !strcmp(h, "asin") || !strcmp(h, "acos")) {
            /* branch cuts: atan on the imaginary axis beyond +-i, asin and acos on the real axis beyond +-1 */
            if (analytic) {
                int bad;
                acb_t w; acb_init(w);
                arb_t one; arb_init(one); arb_one(one);
                if (h[1] == 't') {
                    arb_abs(acb_realref(w), acb_imagref(u));
                    bad = arb_contains_zero(acb_realref(u)) && !arb_lt(acb_realref(w), one);
                } else {
                    arb_abs(acb_realref(w), acb_realref(u));
                    bad = arb_contains_zero(acb_imagref(u)) && !arb_lt(acb_realref(w), one);
                }
                acb_clear(w); arb_clear(one);
                if (bad) { acb_indeterminate(out); acb_clear(u); return 1; }
            }
            if (h[1] == 't') acb_atan(out, u, prec);
            else if (h[1] == 's') acb_asin(out, u, prec);
            else acb_acos(out, u, prec);
        } else ok = 0;
    }
    acb_clear(u);
    return ok;
}

static int eval_poly(acb_t out, const fmpz_mpoly_t p, int x, const acb_t z, int analytic, slong prec) {
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_used_vars(used, p, am_mp);
    acb_ptr g = _acb_vec_init(am_nvars ? am_nvars : 1);
    for (int i = 0; i < am_nvars; i++) if (used[i] && !eval_gen(g + i, i, x, z, analytic, prec)) { _acb_vec_clear(g, am_nvars ? am_nvars : 1); return 0; }
    acb_zero(out);
    acb_t t, pw; acb_init(t); acb_init(pw);
    ulong ex[AM_MAXVARS]; fmpz_t c; fmpz_init(c);
    for (slong k = 0; k < fmpz_mpoly_length(p, am_mp); k++) {
        fmpz_mpoly_get_term_exp_ui(ex, p, k, am_mp);
        fmpz_mpoly_get_term_coeff_fmpz(c, p, k, am_mp);
        acb_set_fmpz(t, c);
        for (int i = 0; i < am_nvars; i++) if (ex[i]) { acb_pow_ui(pw, g + i, ex[i], prec); acb_mul(t, t, pw, prec); }
        acb_add(out, out, t, prec);
    }
    fmpz_clear(c); acb_clear(t); acb_clear(pw);
    _acb_vec_clear(g, am_nvars ? am_nvars : 1);
    return 1;
}

int am_eval_acb(acb_t out, Value *f, int x, const acb_t z, int analytic, slong prec) {
    if (f->kind == V_NUM) { ca_get_acb(out, f->num, prec, am_ca); return 1; }
    if (f->kind != V_RF) return 0;
    acb_t n, d; acb_init(n); acb_init(d);
    int ok = eval_poly(n, fmpz_mpoly_q_numref(f->rf), x, z, analytic, prec) && eval_poly(d, fmpz_mpoly_q_denref(f->rf), x, z, analytic, prec);
    if (ok) acb_div(out, n, d, prec);
    acb_clear(n); acb_clear(d);
    return ok;
}

typedef struct { Value *f; int x; int failed; } Integrand;

static int integrand(acb_ptr out, const acb_t z, void *param, slong order, slong prec) {
    Integrand *I = param;
    if (!am_eval_acb(out, I->f, I->x, z, order == 1, prec)) { I->failed = 1; acb_indeterminate(out); }
    return 0;
}

/* the integral of f from a to b (finite reals), enclosed to about `digits` digits: 1 on success */
int am_integrate_numeric(acb_t res, Value *f, int x, Value *a, Value *b, slong digits) {
    Integrand I = {f, x, 0};
    slong prec = (slong)(digits * 3.33) + 30;
    acb_t A, B; acb_init(A); acb_init(B);
    if (!am_eval_acb(A, a, -1, A, 0, prec) || !am_eval_acb(B, b, -1, B, 0, prec)) { acb_clear(A); acb_clear(B); return 0; }
    mag_t tol; mag_init(tol);
    mag_set_ui_2exp_si(tol, 1, -(slong)(digits * 3.33) - 4);
    acb_calc_integrate_opt_t opt; acb_calc_integrate_opt_init(opt);
    opt->eval_limit = 20000;                                  /* a value or nothing, quickly */
    opt->depth_limit = 200;
    acb_calc_integrate(res, integrand, &I, A, B, prec, tol, opt, prec);
    mag_clear(tol); acb_clear(A); acb_clear(B);
    return !I.failed && acb_is_finite(res);
}
