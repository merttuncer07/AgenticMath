/* Whole numbers (FLINT) and sums.
 *
 * sum(f, k, a, b): added term by term for numeric bounds up to 10^5 terms; otherwise a closed form, checked:
 *   - f a polynomial in k: F with F(k + 1) - F(k) = f(k) by linear algebra (the discrete antiderivative), then
 *     F(b + 1) - F(a);
 *   - f geometric (f(k + 1)/f(k) = r free of k): f(a)(r^(b - a + 1) - 1)/(r - 1), and f(a)/(1 - r) to infinity when
 *     |r| < 1;
 *   - f hypergeometric (f(k + 1)/f(k) rational in k): Gosper's algorithm, z(b + 1) - z(a), checked. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/fmpz_factor.h>
#include <flint/fmpq_mat.h>
#include <flint/fmpz_poly_factor.h>
#include <flint/arith.h>

static int whole(const Value *v, fmpz_t out) {
    fmpq_t q; fmpq_init(q);
    int ok = v_is_rational(v, q) && fmpz_is_one(fmpq_denref(q));
    if (ok) fmpz_set(out, fmpq_numref(q));
    fmpq_clear(q);
    return ok;
}
static Value *num_z(const fmpz_t z) { Value *v = v_num(); ca_set_fmpz(v->num, z, am_ca); return v; }
static Value *num_si(slong k) { Value *v = v_num(); ca_set_si(v->num, k, am_ca); return v; }

#define WHOLE(i, name) fmpz_t name; fmpz_init(name); if (!whole(a[i], name)) am_fail("%s: the arguments must be whole numbers", fname);

static Value *b_mod(Value **a, int n) {
    const char *fname = "mod";
    if (n != 2) am_fail("mod(a, m)");
    WHOLE(0, x) WHOLE(1, m)
    if (fmpz_is_zero(m)) am_fail("mod: m is 0");
    fmpz_t r; fmpz_init(r); fmpz_mod(r, x, m);                 /* 0 <= r < |m| */
    Value *v = num_z(r);
    fmpz_clear(r); fmpz_clear(x); fmpz_clear(m);
    return v;
}

static Value *b_powmod(Value **a, int n) {
    const char *fname = "powmod";
    if (n != 3) am_fail("powmod(a, e, m)");
    WHOLE(0, x) WHOLE(1, e) WHOLE(2, m)
    if (fmpz_sgn(m) <= 0) am_fail("powmod: m must be positive");
    fmpz_t r; fmpz_init(r);
    if (fmpz_sgn(e) < 0) {
        fmpz_t inv; fmpz_init(inv);
        if (!fmpz_invmod(inv, x, m)) am_fail("powmod: %s has no inverse modulo %s", v_str_of(a[0]), v_str_of(a[2]));
        fmpz_neg(e, e);
        fmpz_powm(r, inv, e, m);
        fmpz_clear(inv);
    } else fmpz_powm(r, x, e, m);
    Value *v = num_z(r);
    fmpz_clear(r); fmpz_clear(x); fmpz_clear(e); fmpz_clear(m);
    return v;
}

static Value *b_invmod(Value **a, int n) {
    const char *fname = "invmod";
    if (n != 2) am_fail("invmod(a, m)");
    WHOLE(0, x) WHOLE(1, m)
    fmpz_t r; fmpz_init(r);
    if (fmpz_cmp_ui(m, 1) <= 0 || !fmpz_invmod(r, x, m)) am_fail("invmod: no inverse (they share a factor, or m <= 1)");
    Value *v = num_z(r);
    fmpz_clear(r); fmpz_clear(x); fmpz_clear(m);
    return v;
}

static Value *b_lcm(Value **a, int n) {
    const char *fname = "lcm";
    if (n < 2) am_fail("lcm(a, b, ...)");
    fmpz_t l; fmpz_init_set_ui(l, 1);
    for (int i = 0; i < n; i++) { WHOLE(i, x) fmpz_lcm(l, l, x); fmpz_clear(x); }
    Value *v = num_z(l); fmpz_clear(l);
    return v;
}

static Value *b_divisors(Value **a, int n) {
    const char *fname = "divisors";
    if (n != 1) am_fail("divisors(n)");
    WHOLE(0, x)
    if (fmpz_is_zero(x)) am_fail("divisors: 0 has infinitely many");
    fmpz_abs(x, x);
    fmpz_factor_t F; fmpz_factor_init(F); fmpz_factor(F, x);
    slong cnt = 1;
    for (slong i = 0; i < F->num; i++) { cnt *= (slong)F->exp[i] + 1; if (cnt > 100000) am_fail("divisors: more than 100000"); }
    fmpz *d = _fmpz_vec_init(cnt);
    fmpz_one(d); slong len = 1;
    for (slong i = 0; i < F->num; i++) {                      /* multiply in each prime power */
        slong old = len;
        fmpz_t pp; fmpz_init_set_ui(pp, 1);
        for (ulong e = 1; e <= F->exp[i]; e++) { fmpz_mul(pp, pp, F->p + i); for (slong j = 0; j < old; j++) fmpz_mul(d + len++, d + j, pp); }
        fmpz_clear(pp);
    }
    _fmpz_vec_sort(d, len);
    Value *out = v_list((int)len);
    for (slong i = 0; i < len; i++) out->items[i] = num_z(d + i);
    _fmpz_vec_clear(d, cnt); fmpz_factor_clear(F); fmpz_clear(x);
    am_status(S_PROVED, "from the complete factorization");
    return out;
}

static Value *b_nextprime(Value **a, int n) {
    const char *fname = "nextprime";
    if (n != 1) am_fail("nextprime(n)");
    WHOLE(0, x)
    fmpz_t r; fmpz_init(r);
    fmpz_nextprime(r, x, 1);                                   /* proved prime */
    Value *v = num_z(r);
    fmpz_clear(r); fmpz_clear(x);
    am_status(S_PROVED, "the smallest prime above n, its primality proved");
    return v;
}

static Value *b_totient(Value **a, int n) {
    const char *fname = "totient";
    if (n != 1) am_fail("totient(n)");
    WHOLE(0, x)
    if (fmpz_sgn(x) <= 0) am_fail("totient: n must be positive");
    fmpz_t r; fmpz_init(r); fmpz_euler_phi(r, x);
    Value *v = num_z(r); fmpz_clear(r); fmpz_clear(x);
    return v;
}

static Value *b_fibonacci(Value **a, int n) {
    const char *fname = "fibonacci";
    if (n != 1) am_fail("fibonacci(n)");
    WHOLE(0, x)
    if (!fmpz_fits_si(x) || fmpz_cmp_si(x, 10000000) > 0 || fmpz_cmp_si(x, -10000000) < 0) am_fail("fibonacci: |n| up to 10^7");
    slong k = fmpz_get_si(x);
    fmpz_t r; fmpz_init(r); fmpz_fib_ui(r, (ulong)(k < 0 ? -k : k));
    if (k < 0 && !(k & 1)) fmpz_neg(r, r);                    /* F(-n) = (-1)^(n + 1) F(n) */
    Value *v = num_z(r); fmpz_clear(r); fmpz_clear(x);
    return v;
}

static Value *b_lucas(Value **a, int n) {
    const char *fname = "lucas";
    if (n != 1) am_fail("lucas(n)");
    WHOLE(0, x)
    if (fmpz_sgn(x) < 0 || fmpz_cmp_si(x, 10000000) > 0) am_fail("lucas: 0 <= n <= 10^7");
    ulong k = fmpz_get_ui(x);
    fmpz_t r, t; fmpz_init(r); fmpz_init(t);
    if (k == 0) fmpz_set_ui(r, 2);
    else { fmpz_fib_ui(r, k - 1); fmpz_fib_ui(t, k + 1); fmpz_add(r, r, t); }   /* L(n) = F(n - 1) + F(n + 1) */
    Value *v = num_z(r); fmpz_clear(r); fmpz_clear(t); fmpz_clear(x);
    return v;
}

static Value *b_bernoulli(Value **a, int n) {
    const char *fname = "bernoulli";
    if (n != 1) am_fail("bernoulli(n)");
    WHOLE(0, x)
    if (fmpz_sgn(x) < 0 || fmpz_cmp_si(x, 100000) > 0) am_fail("bernoulli: 0 <= n <= 10^5");
    fmpq_t q; fmpq_init(q); arith_bernoulli_number(q, fmpz_get_ui(x));
    Value *v = v_num(); ca_set_fmpq(v->num, q, am_ca); fmpq_clear(q); fmpz_clear(x);
    return v;
}

static Value *b_partitions(Value **a, int n) {
    const char *fname = "partitions";
    if (n != 1) am_fail("partitions(n)");
    WHOLE(0, x)
    if (fmpz_sgn(x) < 0 || fmpz_cmp_si(x, 100000000) > 0) am_fail("partitions: 0 <= n <= 10^8");
    fmpz_t r; fmpz_init(r); arith_number_of_partitions(r, fmpz_get_ui(x));
    Value *v = num_z(r); fmpz_clear(r); fmpz_clear(x);
    return v;
}

static Value *b_crt(Value **a, int n) {
    if (n != 2 || a[0]->kind != V_LIST || a[1]->kind != V_LIST || a[0]->n != a[1]->n || a[0]->n == 0) am_fail("crt([r1, r2, ...], [m1, m2, ...])");
    fmpz_t r, m, ri, mi, g, s, t; fmpz_init(r); fmpz_init_set_ui(m, 1); fmpz_init(ri); fmpz_init(mi); fmpz_init(g); fmpz_init(s); fmpz_init(t);
    for (int i = 0; i < a[0]->n; i++) {
        if (!whole(a[0]->items[i], ri) || !whole(a[1]->items[i], mi) || fmpz_sgn(mi) <= 0) am_fail("crt: whole residues and positive moduli");
        fmpz_xgcd(g, s, t, m, mi);                             /* s m + t mi = g */
        fmpz_sub(t, ri, r);
        if (!fmpz_divisible(t, g)) { am_status(S_PROVED, "the congruences contradict each other"); am_fact("solutions", "0"); return v_list(0); }
        fmpz_divexact(t, t, g);
        fmpz_mul(t, t, s);
        fmpz_mul(t, t, m);
        fmpz_add(r, r, t);
        fmpz_divexact(t, mi, g);
        fmpz_mul(m, m, t);                                     /* lcm */
        fmpz_mod(r, r, m);
    }
    Value *out = v_list(2); out->items[0] = num_z(r); out->items[1] = num_z(m);
    am_status(S_PROVED, "x = first entry modulo the second; every solution");
    fmpz_clear(r); fmpz_clear(m); fmpz_clear(ri); fmpz_clear(mi); fmpz_clear(g); fmpz_clear(s); fmpz_clear(t);
    return out;
}

static Value *b_len(Value **a, int n) {
    if (n != 1 || (a[0]->kind != V_LIST && a[0]->kind != V_STR)) am_fail("len(list)");
    return num_si(a[0]->kind == V_LIST ? a[0]->n : (slong)strlen(a[0]->str));
}

static Value *b_product(Value **a, int n) {
    if (n != 1 || a[0]->kind != V_LIST) am_fail("product(list)");
    Value *p = num_si(1);
    for (int i = 0; i < a[0]->n; i++) p = v_mul(p, a[0]->items[i]);
    return p;
}

/* ---------------- sums ---------------- */

static Value *subs1(Value *f, int k, Value *val) {
    Value *eq = v_list(2); eq->kind = V_EQ; eq->items[0] = am_gen(k); eq->items[1] = val;
    Value *b[2] = {f, eq};
    return am_call("subs", b, 2);
}

/* F with F(k + 1) - F(k) = p(k), F(0) = 0, for a polynomial p in k (coefficients may involve other symbols) */
static Value *discrete_antiderivative(Value *p, int k, slong d) {
    /* F = sum_{j=1}^{d+1} c_j k^j; F(k+1) - F(k) = sum_j c_j ((k+1)^j - k^j); match coefficients of k^0..k^d */
    Value *K = am_gen(k);
    Value **c = malloc((size_t)(d + 2) * sizeof(Value *));
    /* triangular: the coefficient of k^m in (k+1)^j - k^j is binomial(j, m) for m < j; solve from the top */
    Value **pc = malloc((size_t)(d + 1) * sizeof(Value *));
    for (slong m = 0; m <= d; m++) {                          /* the coefficient of k^m in p */
        Value *t = p;
        for (slong i = 0; i < m; i++) { Value *args[2] = {t, K}; t = am_call("diff", args, 2); }
        Value *at0 = subs1(t, k, num_si(0));
        fmpz_t f; fmpz_init(f); fmpz_fac_ui(f, (ulong)m);
        pc[m] = v_div(at0, num_z(f));
        fmpz_clear(f);
    }
    for (slong j = d + 1; j >= 1; j--) {
        Value *s = pc[j - 1];                                  /* coefficient of k^(j-1): c_j * j + sum_{i>j} c_i binom(i, j-1) */
        for (slong i = j + 1; i <= d + 1; i++) {
            fmpz_t b; fmpz_init(b); fmpz_bin_uiui(b, (ulong)i, (ulong)(j - 1));
            s = v_sub(s, v_mul(c[i], num_z(b)));
            fmpz_clear(b);
        }
        c[j] = v_div(s, num_si(j));
    }
    Value *F = num_si(0);
    for (slong j = 1; j <= d + 1; j++) F = v_add(F, v_mul(c[j], v_pow(K, num_si(j))));
    free(c); free(pc);
    return F;
}

/* ---------------- Gosper's algorithm ----------------
 * For a hypergeometric term t(k) (t(k + 1)/t(k) = r(k) in Q(k)), find z(k) = R(k) t(k) with z(k + 1) - z(k) = t(k)
 * and R rational, or show none exists. Write r(k) = a(k)/b(k) * c(k + 1)/c(k) with gcd(a(k), b(k + h)) = 1 for all
 * h >= 0 (the shifts h come from pairs of irreducible factors), then solve a(k) x(k + 1) - b(k - 1) x(k) = c(k) for a
 * polynomial x by linear algebra over a degree bound; R = b(k - 1) x(k)/c(k). */

static void shift_poly(fmpz_poly_t out, const fmpz_poly_t p, slong s) {
    fmpz_t c; fmpz_init_set_si(c, s); fmpz_poly_taylor_shift(out, p, c); fmpz_clear(c);
}

static int cmp_slong(const void *x, const void *y) { slong a = *(const slong *)x, b = *(const slong *)y; return (a > b) - (a < b); }

/* the shifts h >= 1 with gcd(a(k), b(k + h)) != 1 */
static slong shifts(slong *out, slong max, const fmpz_poly_t a, const fmpz_poly_t b) {
    slong n = 0;
    fmpz_poly_factor_t fa, fb; fmpz_poly_factor_init(fa); fmpz_poly_factor_init(fb);
    fmpz_poly_factor(fa, a); fmpz_poly_factor(fb, b);
    fmpq_t s, t; fmpq_init(s); fmpq_init(t);
    fmpz_poly_t g, sh; fmpz_poly_init(g); fmpz_poly_init(sh);
    for (slong i = 0; i < fa->num; i++) for (slong j = 0; j < fb->num; j++) {
        const fmpz_poly_struct *f = fa->p + i, *h = fb->p + j;
        slong d = fmpz_poly_degree(f);
        if (d < 1 || d != fmpz_poly_degree(h)) continue;
        /* f(k) ~ h(k + s): s = (f_{d-1}/f_d - h_{d-1}/h_d)/d */
        fmpq_set_fmpz_frac(s, f->coeffs + d - 1, f->coeffs + d);
        fmpq_set_fmpz_frac(t, h->coeffs + d - 1, h->coeffs + d);
        fmpq_sub(s, s, t); { fmpz_t dz; fmpz_init_set_si(dz, d); fmpq_div_fmpz(s, s, dz); fmpz_clear(dz); }
        if (!fmpz_is_one(fmpq_denref(s)) || fmpz_sgn(fmpq_numref(s)) <= 0 || !fmpz_fits_si(fmpq_numref(s))) continue;
        slong hsh = fmpz_get_si(fmpq_numref(s));
        if (hsh > 100000) continue;
        shift_poly(sh, b, hsh); fmpz_poly_gcd(g, a, sh);
        if (fmpz_poly_degree(g) < 1) continue;
        int seen = 0;
        for (slong m = 0; m < n; m++) if (out[m] == hsh) seen = 1;
        if (!seen && n < max) out[n++] = hsh;
    }
    qsort(out, (size_t)n, sizeof(slong), cmp_slong);
    fmpz_poly_clear(g); fmpz_poly_clear(sh); fmpq_clear(s); fmpq_clear(t);
    fmpz_poly_factor_clear(fa); fmpz_poly_factor_clear(fb);
    return n;
}

static Value *poly_value(const fmpz_poly_t p, int k, const fmpz_t den) {
    Value *r = num_si(0), *K = am_gen(k);
    for (slong i = fmpz_poly_degree(p); i >= 0; i--) {
        Value *c = v_num(); fmpq_t q; fmpq_init(q);
        fmpq_set_fmpz_frac(q, p->coeffs + i, den);
        ca_set_fmpq(c->num, q, am_ca); fmpq_clear(q);
        r = v_add(v_mul(r, K), c);
    }
    return r;
}

/* the ratio as a(k)/b(k) with integer polynomials; 0 when it is not a rational function of k alone */
static int ratio_polys(fmpz_poly_t a, fmpz_poly_t b, Value *r, int k) {
    if (r->kind == V_NUM) {
        fmpq_t q; fmpq_init(q);
        if (!ca_get_fmpq(q, r->num, am_ca)) { fmpq_clear(q); return 0; }   /* a number field ratio: not handled yet */
        fmpz_poly_set_fmpz(a, fmpq_numref(q)); fmpz_poly_set_fmpz(b, fmpq_denref(q)); fmpq_clear(q);
        return !fmpz_poly_is_zero(a);
    }
    if (r->kind != V_RF) return 0;
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, r->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i] && i != k) return 0;
    return fmpz_mpoly_get_fmpz_poly(a, fmpz_mpoly_q_numref(r->rf), k, am_mp)
        && fmpz_mpoly_get_fmpz_poly(b, fmpz_mpoly_q_denref(r->rf), k, am_mp);
}

/* z(k) with z(k + 1) - z(k) = t(k), or NULL; *hyper is set when t is hypergeometric (then NULL means none exists) */
static Value *gosper(Value *t, int k, Value *ratio, int *hyper) {
    *hyper = 0;
    fmpz_poly_t a, b, c, g, sh, A, B; Value *z = NULL;
    fmpz_poly_init(a); fmpz_poly_init(b); fmpz_poly_init(c); fmpz_poly_init(g); fmpz_poly_init(sh);
    fmpz_poly_init(A); fmpz_poly_init(B);
    if (!ratio_polys(a, b, ratio, k)) goto done;
    *hyper = 1;
    fmpz_poly_one(c);
    slong hs[64]; slong nh = shifts(hs, 64, a, b);
    for (slong m = 0; m < nh; m++) {
        shift_poly(sh, b, hs[m]); fmpz_poly_gcd(g, a, sh);
        if (fmpz_poly_degree(g) < 1) continue;
        fmpz_poly_div(a, a, g);
        shift_poly(sh, g, -hs[m]); fmpz_poly_div(b, b, sh);
        for (slong i = 1; i <= hs[m]; i++) { shift_poly(sh, g, -i); fmpz_poly_mul(c, c, sh); }
    }
    fmpz_poly_set(A, a); shift_poly(B, b, -1);
    slong dA = fmpz_poly_degree(A), dB = fmpz_poly_degree(B), dc = fmpz_poly_degree(c), D;
    if (dA != dB || !fmpz_equal(A->coeffs + dA, B->coeffs + dB)) D = dc - (dA > dB ? dA : dB);
    else {
        D = dc - dA + 1;
        if (dA >= 1) {
            fmpz_t e, q, rem; fmpz_init(e); fmpz_init(q); fmpz_init(rem);
            fmpz_sub(e, B->coeffs + dA - 1, A->coeffs + dA - 1);
            fmpz_fdiv_qr(q, rem, e, A->coeffs + dA);
            if (fmpz_is_zero(rem) && fmpz_cmp_si(q, D) > 0 && fmpz_cmp_si(q, 1000) <= 0) D = fmpz_get_si(q);
            fmpz_clear(e); fmpz_clear(q); fmpz_clear(rem);
        }
    }
    if (D < 0) goto done;
    {
        /* columns: A(k)(k + 1)^j - B(k) k^j for j = 0..D */
        slong rows = D + 1 + (dA > dB ? dA : dB);
        if (dc + 1 > rows) rows = dc + 1;
        fmpq_mat_t M, R, X; fmpq_mat_init(M, rows, D + 1); fmpq_mat_init(R, rows, 1); fmpq_mat_init(X, D + 1, 1);
        fmpz_poly_t col, kp; fmpz_poly_init(col); fmpz_poly_init(kp);
        for (slong j = 0; j <= D; j++) {
            fmpz_poly_zero(kp); fmpz_poly_set_coeff_si(kp, j, 1);
            shift_poly(sh, kp, 1); fmpz_poly_mul(col, A, sh);
            fmpz_poly_mul(sh, B, kp); fmpz_poly_sub(col, col, sh);
            for (slong i = 0; i <= fmpz_poly_degree(col) && i < rows; i++) fmpz_set(fmpq_numref(fmpq_mat_entry(M, i, j)), col->coeffs + i);
        }
        for (slong i = 0; i <= dc; i++) fmpz_set(fmpq_numref(fmpq_mat_entry(R, i, 0)), c->coeffs + i);
        if (fmpq_mat_can_solve(X, M, R)) {
            /* x with a common denominator */
            fmpz_t den; fmpz_init_set_ui(den, 1);
            for (slong j = 0; j <= D; j++) fmpz_lcm(den, den, fmpq_denref(fmpq_mat_entry(X, j, 0)));
            fmpz_poly_t x; fmpz_poly_init(x);
            for (slong j = 0; j <= D; j++) {
                fmpz_t v; fmpz_init(v);
                fmpz_divexact(v, den, fmpq_denref(fmpq_mat_entry(X, j, 0)));
                fmpz_mul(v, v, fmpq_numref(fmpq_mat_entry(X, j, 0)));
                fmpz_poly_set_coeff_fmpz(x, j, v); fmpz_clear(v);
            }
            fmpz_poly_mul(x, x, B);
            fmpz_t one; fmpz_init_set_ui(one, 1);
            z = v_mul(v_div(poly_value(x, k, den), poly_value(c, k, one)), t);
            fmpz_clear(one); fmpz_poly_clear(x); fmpz_clear(den);
        }
        fmpz_poly_clear(col); fmpz_poly_clear(kp);
        fmpq_mat_clear(M); fmpq_mat_clear(R); fmpq_mat_clear(X);
    }
done:
    fmpz_poly_clear(a); fmpz_poly_clear(b); fmpz_poly_clear(c); fmpz_poly_clear(g); fmpz_poly_clear(sh);
    fmpz_poly_clear(A); fmpz_poly_clear(B);
    return z;
}

/* 1 when the rational function z/t of k has no pole at a whole number >= lo */
static int poles_clear(Value *R, int k, Value *lo) {
    fmpz_t L; fmpz_init(L);
    int ok = whole(lo, L);
    if (ok && R->kind == V_RF) {
        fmpz_poly_t d; fmpz_poly_init(d);
        if (!fmpz_mpoly_get_fmpz_poly(d, fmpz_mpoly_q_denref(R->rf), k, am_mp)) ok = 0;
        else {
            fmpz_poly_factor_t f; fmpz_poly_factor_init(f); fmpz_poly_factor(f, d);
            for (slong i = 0; i < f->num; i++) {
                const fmpz_poly_struct *p = f->p + i;
                if (fmpz_poly_degree(p) != 1 || !fmpz_divisible(p->coeffs, p->coeffs + 1)) continue;
                fmpz_t r; fmpz_init(r); fmpz_divexact(r, p->coeffs, p->coeffs + 1); fmpz_neg(r, r);
                if (fmpz_cmp(r, L) >= 0) ok = 0;
                fmpz_clear(r);
            }
            fmpz_poly_factor_clear(f);
        }
        fmpz_poly_clear(d);
    }
    fmpz_clear(L);
    return ok;
}

static int is_inf_val(Value *v) { return v->kind == V_NUM && ca_is_special(v->num, am_ca); }

static Value *b_sum(Value **a, int n) {
    if (n == 1) {                                              /* sum(list) */
        if (a[0]->kind != V_LIST) am_fail("sum(list) or sum(f, k, a, b)");
        Value *s = num_si(0);
        for (int i = 0; i < a[0]->n; i++) s = v_add(s, a[0]->items[i]);
        return s;
    }
    if (n != 4) am_fail("sum(f, k, a, b): the term, the index, the first and last values (b may be oo)");
    int k = am_gen_of(a[1]);
    if (k < 0 || am_vars[k].kernel) am_fail("sum: the second argument must be the index variable");
    Value *f = a[0], *lo = a[2], *hi = a[3];
    fmpz_t A, B; fmpz_init(A); fmpz_init(B);
    if (whole(lo, A) && whole(hi, B)) {                         /* term by term */
        fmpz_t cnt; fmpz_init(cnt); fmpz_sub(cnt, B, A);
        if (fmpz_cmp_si(cnt, 100000) <= 0) {
            Value *s = num_si(0);
            slong a0 = fmpz_get_si(A), b0 = fmpz_get_si(B);
            for (slong i = a0; i <= b0; i++) s = v_add(s, subs1(f, k, num_si(i)));
            fmpz_clear(cnt); fmpz_clear(A); fmpz_clear(B);
            am_status(S_EXACT, "added term by term, exactly");
            return s;
        }
        fmpz_clear(cnt);
    }
    fmpz_clear(A); fmpz_clear(B);
    int infinite = is_inf_val(hi);
    if (infinite && ca_check_is_pos_inf(hi->num, am_ca) != T_TRUE) am_fail("sum: the upper limit may be oo, not -oo");
    if (is_inf_val(lo)) am_fail("sum: the lower limit must be finite");
    /* polynomial in k */
    if (f->kind == V_NUM || (f->kind == V_RF && am_free_of(f, k)) || (f->kind == V_RF && fmpz_mpoly_is_fmpz(fmpz_mpoly_q_denref(f->rf), am_mp) && !am_free_of(f, k))) {
        int poly = 1;
        slong d = 0;
        if (f->kind == V_RF) {
            int used[AM_MAXVARS] = {0};
            fmpz_mpoly_q_used_vars(used, f->rf, am_mp);
            for (int i = 0; i < am_nvars; i++) if (used[i] && am_vars[i].kernel && !am_free_of(am_gen(i), k)) poly = 0;
            if (poly) d = fmpz_mpoly_degree_si(fmpz_mpoly_q_numref(f->rf), k, am_mp);
            if (!fmpz_mpoly_is_fmpz(fmpz_mpoly_q_denref(f->rf), am_mp) && !am_free_of(f, k)) poly = 0;
        }
        if (poly) {
            if (infinite) {
                if (f->kind == V_NUM && ca_check_is_zero(f->num, am_ca) == T_TRUE) return num_si(0);
                am_status(S_PROVED, "a nonzero polynomial term does not tend to 0: the series diverges");
                am_fact("converges", "false");
                return v_str("diverges");
            }
            Value *F = discrete_antiderivative(f, k, d < 0 ? 0 : d);
            Value *chk = v_sub(v_sub(subs1(F, k, v_add(am_gen(k), num_si(1))), F), f);
            if (!(chk->kind == V_NUM && ca_check_is_zero(chk->num, am_ca) == T_TRUE) && !(chk->kind == V_RF && fmpz_mpoly_q_is_zero(chk->rf, am_mp)))
                am_fail("internal: the discrete antiderivative does not check");
            am_status(S_PROVED, "F(b + 1) - F(a) with F(k + 1) - F(k) equal to the term, checked exactly");
            am_fact("method", "\"discrete antiderivative of a polynomial\"");
            Value *r = v_sub(subs1(F, k, v_add(hi, num_si(1))), subs1(F, k, lo));
            return r;
        }
    }
    /* geometric: f(k + 1)/f(k) free of k */
    Value *ratio = am_reevaluate(v_div(subs1(f, k, v_add(am_gen(k), num_si(1))), f));
    ratio = am_normal_form(ratio);
    if (ratio->kind == V_RF && !am_free_of(ratio, k)) {
        /* exp(k*log(r)) forms: compare at two values of k */
        Value *r1 = am_reevaluate(subs1(ratio, k, num_si(1))), *r2 = am_reevaluate(subs1(ratio, k, num_si(2)));
        Value *d = v_sub(r1, r2);
        if (am_zero_test(d, NULL, 0) == 1) ratio = r1;
    }
    if (ratio->kind == V_NUM || am_free_of(ratio, k)) {
        Value *fa = subs1(f, k, lo);
        if (infinite) {
            Value *ar = am_reevaluate(ratio);
            if (ar->kind != V_NUM) am_fail("sum: the ratio of a geometric series must be a number to decide convergence");
            Value *absr = v_num(); ca_abs(absr->num, ar->num, am_ca);
            Value *one = num_si(1);
            truth_t lt = ca_check_lt(absr->num, one->num, am_ca);
            if (lt == T_TRUE) {
                am_status(S_PROVED, "a geometric series with ratio %s, |ratio| < 1", v_str_of(ar));
                am_fact("method", "\"geometric\"");
                return v_div(fa, v_sub(num_si(1), ar));
            }
            if (lt == T_FALSE) { am_status(S_PROVED, "a geometric series with |ratio| >= 1 diverges"); am_fact("converges", "false"); return v_str("diverges"); }
            am_fail("sum: could not decide whether |ratio| < 1");
        }
        Value *cnt = v_add(v_sub(hi, lo), num_si(1));
        Value *one = num_si(1);
        Value *dr = v_sub(ratio, one);
        if ((dr->kind == V_NUM && ca_check_is_zero(dr->num, am_ca) == T_TRUE)) { am_status(S_PROVED, "a constant term"); return v_mul(fa, cnt); }
        am_status(S_PROVED, "a geometric sum with ratio %s", v_str_of(ratio));
        am_fact("method", "\"geometric\"");
        return v_div(v_mul(fa, v_sub(v_pow(ratio, cnt), one)), dr);
    }
    {   /* c/k^s to infinity: a p-series, zeta(s) less its first terms; s <= 1 diverges */
        slong sdeg = f->kind == V_RF ? fmpz_mpoly_degree_si(fmpz_mpoly_q_denref(f->rf), k, am_mp) - fmpz_mpoly_degree_si(fmpz_mpoly_q_numref(f->rf), k, am_mp) : 0;
        fmpz_t A0; fmpz_init(A0);
        if (infinite && sdeg >= 1 && sdeg <= 10000 && whole(lo, A0) && fmpz_sgn(A0) > 0 && fmpz_cmp_si(A0, 100000) <= 0) {
            Value *ks = v_pow(am_gen(k), num_si(sdeg));
            Value *c = v_mul(f, ks);
            if (am_free_of(c, k)) {
                if (sdeg == 1) {
                    fmpz_clear(A0);
                    am_status(S_PROVED, "c/k with c = %s nonzero: the harmonic series diverges", v_str_of(c));
                    am_fact("converges", "false");
                    return v_str("diverges");
                }
                Value *zarg = num_si(sdeg);
                Value *zv = am_call("zeta", &zarg, 1);
                for (slong j = 1; j < fmpz_get_si(A0); j++) zv = v_sub(zv, v_pow(num_si(j), num_si(-sdeg)));
                fmpz_clear(A0);
                am_status(S_PROVED, "c/k^%ld: a p-series, c*(zeta(%ld) less the terms before the lower limit)", (long)sdeg, (long)sdeg);
                am_fact("method", "\"p-series\"");
                return v_mul(c, zv);
            }
        }
        fmpz_clear(A0);
    }
    int hyper = 0;
    Value *z = gosper(f, k, ratio, &hyper);
    if (z) {
        Value *K1 = v_add(am_gen(k), num_si(1));
        Value *chk = am_normal_form(am_reevaluate(v_sub(v_sub(subs1(z, k, K1), z), f)));
        int zt = am_zero_test(chk, NULL, 0);
        if ((zt == 1 || zt == 2) && poles_clear(am_normal_form(v_div(z, f)), k, lo)) {
            if (zt == 1) am_status(S_PROVED, "z(b + 1) - z(a) with z(k) = %s found by Gosper's algorithm; z(k + 1) - z(k) equals the term exactly and z has no pole in the range", v_str_of(z));
            else am_status(S_PROBABLE, "z(b + 1) - z(a) with z(k) = %s found by Gosper's algorithm; z(k + 1) - z(k) equals the term at random points", v_str_of(z));
            am_fact("method", "\"Gosper\"");
            am_fact("antidifference", "\"%s\"", v_str_of(z));
            Value *res;
            if (infinite) {                                    /* the limit of z(N + 1) - z(a) */
                Value *args[3] = {z, am_gen(k), hi};
                res = v_sub(am_call("limit", args, 3), subs1(z, k, lo));
            } else res = v_sub(subs1(z, k, v_add(hi, num_si(1))), subs1(z, k, lo));
            res = am_normal_form(res);
            return res;
        }
    }
    if (hyper && !z) {
        am_status(S_UNKNOWN, "no closed form: Gosper's algorithm shows the partial sums are not a hypergeometric term plus a constant");
        am_fact("gosper_summable", "false");
    } else
        am_status(S_UNKNOWN, "no closed form found (polynomial, geometric and Gosper-summable hypergeometric terms are handled)");
    Value *args[4] = {f, a[1], lo, hi};
    return am_kernel_value("sum", args, 4);
}

static const struct { const char *name; Builtin f; const char *sig, *doc; } DTABLE[] = {
    {"mod", b_mod, "mod(a, m)", "the remainder, 0 <= r < |m|"},
    {"powmod", b_powmod, "powmod(a, e, m)", "a^e modulo m (e may be negative when a is invertible)"},
    {"invmod", b_invmod, "invmod(a, m)", "the inverse of a modulo m"},
    {"lcm", b_lcm, "lcm(a, b, ...)", "least common multiple of whole numbers"},
    {"divisors", b_divisors, "divisors(n)", "all positive divisors, in order"},
    {"nextprime", b_nextprime, "nextprime(n)", "the smallest prime greater than n (proved prime)"},
    {"totient", b_totient, "totient(n)", "Euler's totient"},
    {"fibonacci", b_fibonacci, "fibonacci(n)", "the Fibonacci number F(n) (F(0) = 0, F(1) = 1; negative n too)"},
    {"lucas", b_lucas, "lucas(n)", "the Lucas number L(n) (L(0) = 2, L(1) = 1)"},
    {"bernoulli", b_bernoulli, "bernoulli(n)", "the Bernoulli number B(n) (B(1) = -1/2)"},
    {"partitions", b_partitions, "partitions(n)", "the number of partitions of n"},
    {"crt", b_crt, "crt([r1, ...], [m1, ...])", "the Chinese remainder theorem: [x, M] with every solution x mod M, or [] when they contradict"},
    {"sum", b_sum, "sum(list) | sum(f, k, a, b)", "a sum: term by term for numeric bounds, closed forms for polynomial and geometric terms (b may be oo), checked"},
    {"product", b_product, "product(list)", "the product of the elements"},
    {"len", b_len, "len(list)", "the number of elements"},
    {NULL, NULL, NULL, NULL}};

Builtin am_discrete_builtin(const char *name, size_t len) {
    for (int i = 0; DTABLE[i].name; i++) if (strlen(DTABLE[i].name) == len && !strncmp(DTABLE[i].name, name, len)) return DTABLE[i].f;
    return NULL;
}
int am_discrete_doc(int i, const char **name, const char **sig, const char **doc) {
    if (!DTABLE[i].name) return 0;
    *name = DTABLE[i].name; *sig = DTABLE[i].sig; *doc = DTABLE[i].doc;
    return 1;
}
