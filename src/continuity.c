/* Continuity of an expression on a closed interval [a, b] of real numbers: a proof or nothing.
 *
 * Each function term's argument must stay in its domain: sqrt(u) needs u >= 0, log(u) needs u > 0, asin and acos
 * need 1 - u^2 >= 0, tan(u) needs cos(u) != 0, and every denominator must be nonzero. A condition on a
 * polynomial in x is decided exactly from its real roots; any other is checked by ball arithmetic over [a, b]
 * cut into pieces (an enclosure over a piece holds at every point of it). */
#include "am.h"

#include <stdlib.h>
#include <string.h>

#include <flint/fmpz_poly.h>
#include <flint/qqbar.h>
#include <flint/acb.h>

int am_eval_acb(acb_t out, Value *f, int x, const acb_t z, int analytic, slong prec);

enum { NONZERO, POSITIVE, NONNEG };
static int open_ends;                 /* 1: the open interval (a, b); the ends are left to one-sided limits */

static int holds_ball(const acb_t v, int what) {
    if (!acb_is_finite(v)) return 0;
    if (what == NONZERO) return !acb_contains_zero(v);
    if (!arb_is_zero(acb_imagref(v))) return 0;
    return what == POSITIVE ? arb_is_positive(acb_realref(v)) : arb_is_nonnegative(acb_realref(v));
}

/* by pieces: [lo, hi] cut in halves while the enclosure does not decide, down to a width of 2^-depth of the whole */
static int by_balls(Value *g, int x, const arb_t lo, const arb_t hi, int what, int depth) {
    acb_t z, v; acb_init(z); acb_init(v);
    arb_union(acb_realref(z), lo, hi, 128);
    int ok = am_eval_acb(v, g, x, z, 0, 128) && holds_ball(v, what);
    acb_clear(z); acb_clear(v);
    if (ok) return 1;
    if (depth <= 0) return 0;
    arb_t mid; arb_init(mid);
    arb_add(mid, lo, hi, 128); arb_mul_2exp_si(mid, mid, -1);
    ok = by_balls(g, x, lo, mid, what, depth - 1) && by_balls(g, x, mid, hi, what, depth - 1);
    arb_clear(mid);
    return ok;
}

static Value *num_si(slong k) { Value *v = v_num(); ca_set_si(v->num, k, am_ca); return v; }

/* g = N/D with N, D polynomials in x alone: decided exactly. -1 when g is not of that kind */
static int by_roots(Value *g, int x, Value *a, Value *b, int what) {
    if (g->kind == V_NUM) {
        if (what == NONZERO) return ca_check_is_zero(g->num, am_ca) == T_FALSE;
        truth_t r = what == POSITIVE ? ca_check_gt(g->num, num_si(0)->num, am_ca) : ca_check_ge(g->num, num_si(0)->num, am_ca);
        return r == T_TRUE;
    }
    if (g->kind != V_RF) return -1;
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, g->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i] && i != x) return -1;
    fmpz_poly_t N, D, P; fmpz_poly_init(N); fmpz_poly_init(D); fmpz_poly_init(P);
    fmpz_mpoly_get_fmpz_poly(N, fmpz_mpoly_q_numref(g->rf), x, am_mp);
    fmpz_mpoly_get_fmpz_poly(D, fmpz_mpoly_q_denref(g->rf), x, am_mp);
    fmpz_poly_mul(P, N, D);                                  /* the sign of N/D where D != 0 */
    int ok = 1;
    /* the real roots of N and D in [a, b], with the ends: the sign is constant between neighbours */
    slong deg = fmpz_poly_degree(P);
    qqbar_ptr r = deg > 0 ? _qqbar_vec_init(deg) : NULL;
    if (deg > 0) qqbar_roots_fmpz_poly(r, P, 0);
    Value **pts = malloc((size_t)(deg + 2) * sizeof(Value *)); int np = 0;
    pts[np++] = a;
    for (slong i = 0; i < deg; i++) {
        if (!qqbar_is_real(r + i)) continue;
        Value *rv = v_num(); ca_set_qqbar(rv->num, r + i, am_ca);
        if (ca_check_gt(rv->num, a->num, am_ca) != T_TRUE || ca_check_lt(rv->num, b->num, am_ca) != T_TRUE) {
            /* a root at an end: N or D zero there */
            if (!open_ends && (ca_check_equal(rv->num, a->num, am_ca) == T_TRUE || ca_check_equal(rv->num, b->num, am_ca) == T_TRUE)) {
                /* D zero at an end: a pole there; N zero at an end: g = 0, against NONZERO and POSITIVE */
                qqbar_t dv; qqbar_init(dv); qqbar_evaluate_fmpz_poly(dv, D, r + i);
                if (qqbar_is_zero(dv) || what != NONNEG) ok = 0;
                qqbar_clear(dv);
            }
            continue;
        }
        qqbar_t dv; qqbar_init(dv); qqbar_evaluate_fmpz_poly(dv, D, r + i);
        if (qqbar_is_zero(dv) || what != NONNEG) ok = 0;    /* a pole inside, or a zero of N inside */
        qqbar_clear(dv);
        int dup = 0;
        for (int j = 1; j < np; j++) if (ca_check_equal(pts[j]->num, rv->num, am_ca) == T_TRUE) dup = 1;
        if (!dup) pts[np++] = rv;
    }
    pts[np++] = b;
    if (r) _qqbar_vec_clear(r, deg);
    /* sort the points (few): insertion sort by exact comparison */
    for (int i = 1; i < np && ok; i++)
        for (int j = i; j > 0 && ca_check_lt(pts[j]->num, pts[j - 1]->num, am_ca) == T_TRUE; j--) { Value *t = pts[j]; pts[j] = pts[j - 1]; pts[j - 1] = t; }
    /* the sign at the midpoint of each gap */
    for (int i = 0; i + 1 < np && ok; i++) {
        Value *m = v_div(v_add(pts[i], pts[i + 1]), num_si(2));
        ca_t s, t; ca_init(s, am_ca); ca_init(t, am_ca);
        for (slong k = fmpz_poly_degree(P); k >= 0; k--) { ca_mul(s, s, m->num, am_ca); ca_add_fmpz(s, s, P->coeffs + k, am_ca); }
        truth_t pos = ca_check_gt(s, num_si(0)->num, am_ca);
        if (what == NONZERO) { if (ca_check_is_zero(s, am_ca) != T_FALSE) ok = 0; }
        else if (pos != T_TRUE) ok = 0;
        ca_clear(s, am_ca); ca_clear(t, am_ca);
    }
    if (fmpz_poly_is_zero(P) && what != NONNEG) ok = 0;
    free(pts);
    fmpz_poly_clear(N); fmpz_poly_clear(D); fmpz_poly_clear(P);
    return ok;
}

static int holds_on(Value *g, int x, Value *a, Value *b, int what) {
    int r = by_roots(g, x, a, b, what);
    if (r >= 0) return r;
    arb_t lo, hi; arb_init(lo); arb_init(hi);
    acb_t t; acb_init(t);
    ca_get_acb(t, a->num, 128, am_ca); arb_set(lo, acb_realref(t));
    ca_get_acb(t, b->num, 128, am_ca); arb_set(hi, acb_realref(t));
    int ok = by_balls(g, x, lo, hi, what, 10);
    acb_clear(t); arb_clear(lo); arb_clear(hi);
    return ok;
}

static int real_kernel(const char *h) {
    static const char *ok[] = {"exp", "sin", "cos", "atan", "erf", "abs", "Si", NULL};
    for (int i = 0; ok[i]; i++) if (!strcmp(h, ok[i])) return 1;
    return 0;
}

static int cont(Value *F, int x, Value *a, Value *b, int depth) {
    if (F->kind == V_NUM) return 1;
    if (F->kind != V_RF || depth > 20) return 0;
    Value *Dv = v_rf();
    fmpz_mpoly_set(fmpz_mpoly_q_numref(Dv->rf), fmpz_mpoly_q_denref(F->rf), am_mp);
    fmpz_mpoly_one(fmpz_mpoly_q_denref(Dv->rf), am_mp);
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, F->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) {
        if (!used[i] || i == x) continue;
        if (!am_vars[i].kernel) return 0;                       /* another variable: not a function of x alone */
        if (am_vars[i].numval || am_free_of(am_gen(i), x)) continue;
        const char *h = am_vars[i].head;
        if (!h || am_vars[i].nargs != 1) return 0;
        Value *u = am_vars[i].args[0];
        if (!cont(u, x, a, b, depth + 1)) return 0;
        if (real_kernel(h)) continue;
        if (!strcmp(h, "sqrt")) { if (!holds_on(u, x, a, b, NONNEG)) return 0; continue; }
        if (!strcmp(h, "log")) { if (!holds_on(u, x, a, b, POSITIVE)) return 0; continue; }
        if (!strcmp(h, "asin") || !strcmp(h, "acos")) { if (!holds_on(v_sub(num_si(1), v_mul(u, u)), x, a, b, NONNEG)) return 0; continue; }
        if (!strcmp(h, "tan")) { if (!holds_on(am_call("cos", &u, 1), x, a, b, NONZERO)) return 0; continue; }
        return 0;
    }
    if (!am_free_of(Dv, x) && !holds_on(Dv, x, a, b, NONZERO)) return 0;
    return 1;
}

/* 1 when F is proved continuous on [a, b] (on (a, b) when open is 1), a and b real numbers */
int am_continuous_on(Value *F, int x, Value *a, Value *b, int open) {
    open_ends = open;
    if (a->kind != V_NUM || b->kind != V_NUM || ca_is_special(a->num, am_ca) || ca_is_special(b->num, am_ca)) return 0;
    if (ca_check_is_real(a->num, am_ca) != T_TRUE || ca_check_is_real(b->num, am_ca) != T_TRUE) return 0;
    if (ca_check_gt(a->num, b->num, am_ca) == T_TRUE) { Value *t = a; a = b; b = t; }
    return cont(F, x, a, b, 0);
}
