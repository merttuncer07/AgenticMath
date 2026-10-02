/* Series and limits.
 *
 * A series in t = x - a is kept as exact coefficients (values: numbers, or expressions in other variables) for
 * the powers t^v, ..., t^(N-1), and the order N up to which it is known: sum c_k t^(v+k) + O(t^N). Arithmetic
 * keeps track of N honestly (dividing by a series that starts at t^w loses w terms); the elementary functions of
 * a series are composed from their own expansions. log(t) itself has no series; when it appears it is kept as a
 * symbol in the coefficients, which is what a limit needs.
 *
 * limit(f, x, a) reads the leading term of the series at a (at infinity, of f(1/t) at t = 0+). */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { slong v, N; Value **c; int flat, huge, bounded; } Ser;   /* c[k]: the coefficient of t^(v+k), k < N - v */
/* flat: smaller than every power of t (exp(-1/t)); huge = +-1: larger than every power, with that sign (exp(1/t)).
 * The light part of the Gruntz algorithm: enough for exp at infinity when the comparison is not close. */
static int cur_dir;                                           /* t -> 0+ (1), or from both sides (0) */

static slong len(const Ser *s) { return s->N - s->v > 0 ? s->N - s->v : 0; }
static Value *zero(void) { return v_num(); }
static Value *num_si(slong k) { Value *z = v_num(); ca_set_si(z->num, k, am_ca); return z; }
static Value *num_q(slong p, slong q) { Value *z = v_num(); fmpq_t r; fmpq_init(r); fmpq_set_si(r, p, (ulong)q); ca_set_fmpq(z->num, r, am_ca); fmpq_clear(r); return z; }

static Ser mk(slong v, slong N) {
    Ser s; s.v = v; s.N = N; s.flat = 0; s.huge = 0; s.bounded = 0;
    slong n = len(&s);
    s.c = malloc((size_t)(n ? n : 1) * sizeof(Value *));
    for (slong k = 0; k < n; k++) s.c[k] = zero();
    return s;
}
static Value *coef(const Ser *s, slong p) { return p >= s->v && p < s->N ? s->c[p - s->v] : zero(); }

static int probable_zero;                                     /* a coefficient was taken as 0 on numerical evidence */

/* is a coefficient zero? decided exactly when possible */
static int is_zero(Value *c) {
    if (c->kind == V_NUM) {
        truth_t t = ca_check_is_zero(c->num, am_ca);
        if (t != T_UNKNOWN) return t == T_TRUE;
    }
    if (c->kind == V_RF && fmpz_mpoly_q_is_zero(c->rf, am_mp)) return 1;
    int z = am_zero_test(c, NULL, 0);
    if (z == 2) { probable_zero = 1; return 1; }
    if (z < 0) am_fail("series: cannot decide whether a coefficient is zero");
    return z == 1;
}

/* drop leading zero coefficients */
static void normalize(Ser *s) {
    while (len(s) > 0 && is_zero(s->c[0])) { memmove(s->c, s->c + 1, (size_t)(len(s) - 1) * sizeof(Value *)); s->v++; }
}

static int sign_lead(Ser *a);
static int sign_lead(Ser *a) {                                /* the sign of the leading coefficient (real), or 0 */
    normalize(a);
    if (len(a) == 0) return 0;
    Value *c = am_reevaluate(a->c[0]);
    fmpq_t q; fmpq_init(q);
    if (v_is_rational(c, q)) { int sg = fmpq_sgn(q); fmpq_clear(q); return sg; }
    fmpq_clear(q);
    if (c->kind != V_NUM || ca_check_is_real(c->num, am_ca) != T_TRUE) return 0;
    if (ca_check_gt(c->num, zero()->num, am_ca) == T_TRUE) return 1;
    if (ca_check_lt(c->num, zero()->num, am_ca) == T_TRUE) return -1;
    return 0;
}
static Ser add(Ser a, Ser b, int sub) {
    if (a.bounded || b.bounded) {
        Ser o = a.bounded ? b : a;
        if (o.huge) return o;
        am_fail("limit: an oscillating term (sin or cos of a growing argument) that does not die out");
    }
    if (a.huge || b.huge) {
        if (a.huge && b.huge) am_fail("limit: two terms that grow faster than every power; comparing them needs the full Gruntz algorithm, not built yet");
        Ser r = a.huge ? a : b;
        if (b.huge && sub) r.huge = -r.huge;
        return r;
    }
    if (a.flat && b.flat) return a;
    if (a.flat || b.flat) {                                    /* the flat term counts only when the other is all zero */
        Ser o = a.flat ? b : a;
        int allzero = 1;
        for (slong k = 0; k < len(&o) && allzero; k++) allzero = is_zero(o.c[k]);
        if (allzero) return a.flat ? a : b;
        if (a.flat && sub) { Ser r = mk(b.v, b.N); for (slong k = 0; k < len(&b); k++) r.c[k] = v_neg(b.c[k]); return r; }
        return o;
    }
    slong v = a.v < b.v ? a.v : b.v, N = a.N < b.N ? a.N : b.N;
    Ser r = mk(v, N);
    for (slong p = v; p < N; p++) r.c[p - v] = sub ? v_sub(coef(&a, p), coef(&b, p)) : v_add(coef(&a, p), coef(&b, p));
    return r;
}

static Ser mul(Ser a, Ser b) {
    if (a.bounded || b.bounded) {                              /* bounded times smaller than every power: still that small */
        Ser o = a.bounded ? b : a;
        if (o.flat) return o;
        if (o.bounded) return o;
        am_fail("limit: an oscillating term (sin or cos of a growing argument) that does not die out");
    }
    if (a.huge || b.huge) {
        if (a.flat || b.flat || (a.huge && b.huge && 0)) am_fail("limit: a product of a term smaller and a term larger than every power; needs the full Gruntz algorithm, not built yet");
        if (a.huge && b.huge) { Ser r = a; r.huge = a.huge * b.huge; return r; }
        Ser h = a.huge ? a : b, o = a.huge ? b : a;
        int sg = sign_lead(&o);
        if (!sg) am_fail("limit: the sign of a factor next to an exponentially large term is not known");
        h.huge *= sg;
        return h;
    }
    if (a.flat) return a;
    if (b.flat) return b;
    slong v = a.v + b.v;
    slong N1 = a.N + b.v, N2 = b.N + a.v, N = N1 < N2 ? N1 : N2;
    Ser r = mk(v, N);
    for (slong p = v; p < N; p++) {
        Value *s = zero();
        for (slong i = a.v; i < a.N; i++) {
            slong j = p - i;
            if (j < b.v) break;
            if (j >= b.N) continue;
            s = v_add(s, v_mul(coef(&a, i), coef(&b, j)));
        }
        r.c[p - v] = s;
    }
    return r;
}

static Ser scale(Ser a, Value *c) { Ser r = mk(a.v, a.N); for (slong k = 0; k < len(&a); k++) r.c[k] = v_mul(a.c[k], c); return r; }

static Ser constant(Value *c, slong N) { Ser r = mk(0, N > 0 ? N : 1); r.c[0] = c; if (N <= 0) r.N = 1; return r; }

/* 1/a: a must have a nonzero leading coefficient */
static Ser inv(Ser a) {
    if (a.huge) { Ser r = mk(a.N, a.N); r.flat = 1; return r; }
    if (a.flat) am_fail("limit: dividing by a term smaller than every power; needs the full Gruntz algorithm, not built yet");
    normalize(&a);
    if (len(&a) == 0) am_fail("series: division by a series that vanishes to the order computed; ask for more terms");
    slong n = len(&a);                                       /* relative precision */
    Ser r = mk(-a.v, -a.v + n);
    Value *c0 = a.c[0];
    r.c[0] = v_div(num_si(1), c0);
    for (slong k = 1; k < n; k++) {
        Value *s = zero();
        for (slong j = 1; j <= k; j++) s = v_add(s, v_mul(a.c[j], r.c[k - j]));
        r.c[k] = v_neg(v_div(s, c0));
    }
    return r;
}

static Ser powi(Ser a, slong e) {
    if (a.flat || a.huge) {
        if (e == 0) return constant(num_si(1), a.N + 64);
        if (e < 0) return powi(inv(a), -e);
        Ser r = a; if (a.huge && !(e & 1)) r.huge = 1;
        return r;
    }
    if (e < 0) return powi(inv(a), -e);
    if (e == 0) return constant(num_si(1), a.N - a.v + 64);
    Ser r = a, b = a;
    e--;
    while (e) { if (e & 1) r = mul(r, b); e >>= 1; if (e) b = mul(b, b); }
    return r;
}

/* sum_k w_k h^k for a series h with valuation >= 1, to absolute order N */
static Ser compose(Value **w, slong nw, Ser h, slong N) {
    Ser r = mk(0, N);
    r.c[0] = w[0];
    Ser hp = h;
    for (slong k = 1; k < nw && k * (h.v > 0 ? h.v : 1) < N; k++) {
        if (k > 1) hp = mul(hp, h);
        for (slong p = hp.v; p < N && p < hp.N; p++) if (p >= 0) r.c[p] = v_add(r.c[p], v_mul(w[k], coef(&hp, p)));
        if (hp.N < r.N) r.N = hp.N;
    }
    return r;
}

static Ser deriv(Ser a) {                                     /* d/dt */
    Ser r = mk(a.v - 1, a.N - 1);
    for (slong p = a.v; p < a.N; p++) r.c[p - 1 - (a.v - 1)] = v_mul(num_si(p), coef(&a, p));
    return r;
}
static Ser integ(Ser a, Value *c0) {                          /* the antiderivative with value c0 at t = 0 */
    if (a.v < 0) {
        for (slong p = a.v; p < 0 && p < a.N; p++) if (!is_zero(coef(&a, p))) am_fail("series: a term t^%ld under an integral", (long)p);
    }
    Ser r = mk(0, a.N + 1);
    r.c[0] = c0;
    for (slong p = (a.v > 0 ? a.v : 0); p < a.N; p++) r.c[p + 1] = v_div(coef(&a, p), num_si(p + 1));
    return r;
}

static Value *call1(const char *f, Value *a) { return am_call(f, &a, 1); }

static Value *log_t;                                          /* log(t) as a symbol, when it appears */

/* the series of head(u) */
static Ser apply(const char *h, Ser u, int x, Value *a, slong N) {
    if (u.huge) {
        if (!strcmp(h, "exp")) { if (u.huge > 0) { Ser r = mk(0, N); r.huge = 1; return r; } Ser r = mk(N, N); r.flat = 1; return r; }
        am_fail("limit: %s of a term larger than every power; needs the full Gruntz algorithm, not built yet", h);
    }
    if (u.flat) u = mk(N, N);                                 /* smaller than every power: as 0 for an analytic function */
    normalize(&u);
    if (u.v < 0 && !strcmp(h, "exp")) {                       /* exp(c/t^k + ...): smaller or larger than every power */
        int sg = sign_lead(&u);
        if (!sg) am_fail("limit: exp of a large term whose sign is not known (it may oscillate)");
        if ((-u.v) & 1) {
            if (!cur_dir) am_fail("limit: exp(c/t^%ld) behaves differently on the two sides; give \"+\" or \"-\"", (long)-u.v);
            sg *= cur_dir;
        }
        Ser r = mk(sg < 0 ? N : 0, N);
        if (sg < 0) r.flat = 1; else r.huge = 1;
        return r;
    }
    Value *c0 = u.v == 0 && len(&u) ? u.c[0] : zero();
    if (u.v < 0 && !strcmp(h, "atan")) {                      /* atan(u) = sign(c) pi/2 - atan(1/u), u large */
        int sg = 0;
        Value *lead = am_reevaluate(u.c[0]);
        if (lead->kind == V_NUM && ca_check_is_real(lead->num, am_ca) == T_TRUE)
            sg = ca_check_gt(lead->num, zero()->num, am_ca) == T_TRUE ? 1 : ca_check_lt(lead->num, zero()->num, am_ca) == T_TRUE ? -1 : 0;
        if (!sg) am_fail("series: atan of a large term whose sign is not known");
        Value *pi = v_num(); ca_pi(pi->num, am_ca);
        Ser r = add(constant(v_mul(num_q(sg, 2), pi), N + 64), apply("atan", inv(u), x, a, N), 1);
        if (r.N > N) r.N = N;
        return r;
    }
    if (u.v < 0 && (!strcmp(h, "sin") || !strcmp(h, "cos"))) {   /* bounded, oscillating, for a real growing argument */
        Value *lead = am_reevaluate(u.c[0]);
        if (lead->kind == V_NUM && ca_check_is_real(lead->num, am_ca) == T_TRUE) { Ser r = mk(0, N); r.bounded = 1; return r; }
    }
    if (u.v < 0 && strcmp(h, "log") && strcmp(h, "sqrt"))
        am_fail("series: %s of a term that is infinite at the point (an essential singularity); limits of this kind need the Gruntz algorithm, not built yet", h);
    if (u.v > 0 && len(&u) == 0) am_fail("series: not enough terms; ask for a higher order");
    Ser hh = u;                                               /* u - c0, valuation >= 1 */
    if (u.v == 0) { hh = mk(u.v, u.N); for (slong k = 0; k < len(&u); k++) hh.c[k] = u.c[k]; hh.c[0] = zero(); normalize(&hh); if (len(&hh) == 0) hh.v = u.N; }
    slong n = N + 2;
    Value **w = malloc((size_t)(n + 1) * sizeof(Value *));
    Ser out;
    if (!strcmp(h, "exp") || !strcmp(h, "sin") || !strcmp(h, "cos")) {
        Value *f = num_si(1);
        Value **e = malloc((size_t)(n + 1) * sizeof(Value *)), **s = malloc((size_t)(n + 1) * sizeof(Value *)), **c = malloc((size_t)(n + 1) * sizeof(Value *));
        for (slong k = 0; k <= n; k++) {
            if (k) f = v_mul(f, num_si(k));
            Value *ik = v_div(num_si(1), f);
            e[k] = ik;
            s[k] = (k & 1) ? ((k / 2) & 1 ? v_neg(ik) : ik) : zero();
            c[k] = (k & 1) ? zero() : ((k / 2) & 1 ? v_neg(ik) : ik);
        }
        if (!strcmp(h, "exp")) out = scale(compose(e, n + 1, hh, N), call1("exp", c0));
        else {
            Ser S = compose(s, n + 1, hh, N), C = compose(c, n + 1, hh, N);
            Value *sc = call1("sin", c0), *cc = call1("cos", c0);
            if (!strcmp(h, "sin")) out = add(scale(C, sc), scale(S, cc), 0);
            else out = add(scale(C, cc), scale(S, sc), 1);
        }
        free(e); free(s); free(c);
    } else if (!strcmp(h, "log")) {
        if (u.v != 0) {                                       /* log(t^v w) = v log(t) + log(w) */
            Ser wv = mk(0, u.N - u.v);
            for (slong k = 0; k < len(&u); k++) wv.c[k] = u.c[k];
            Ser lw = apply("log", wv, x, a, N);
            Ser r = mk(lw.v < 0 ? lw.v : 0, lw.N);
            for (slong p = r.v; p < r.N; p++) r.c[p - r.v] = coef(&lw, p);
            r.c[-r.v] = v_add(r.c[-r.v], v_mul(num_si(u.v), log_t));
            out = r;
        } else {
            w[0] = call1("log", c0);
            for (slong k = 1; k <= n; k++) w[k] = v_div(num_si((k & 1) ? 1 : -1), v_mul(num_si(k), v_pow(c0, num_si(k))));
            out = compose(w, n + 1, hh, N);
        }
    } else if (!strcmp(h, "sqrt")) {
        if (u.v != 0) {
            if (u.v & 1) am_fail("series: sqrt of a series starting at an odd power gives fractional powers (Puiseux series), not built yet");
            Ser wv = mk(0, u.N - u.v);
            for (slong k = 0; k < len(&u); k++) wv.c[k] = u.c[k];
            Ser r = apply("sqrt", wv, x, a, N);
            r.v += u.v / 2; r.N += u.v / 2;
            out = r;
        } else {
            Value *b = num_si(1);                            /* binomial(1/2, k) / c0^k */
            Value *half = num_q(1, 2), *sq = call1("sqrt", c0);
            w[0] = sq;
            for (slong k = 1; k <= n; k++) { b = v_mul(b, v_div(v_sub(half, num_si(k - 1)), num_si(k))); w[k] = v_mul(sq, v_div(b, v_pow(c0, num_si(k)))); }
            out = compose(w, n + 1, hh, N);
        }
    } else if (!strcmp(h, "tan")) {
        out = mul(apply("sin", u, x, a, N + 2), inv(apply("cos", u, x, a, N + 2)));
    } else if (!strcmp(h, "atan") || !strcmp(h, "asin") || !strcmp(h, "acos")) {
        Ser du = deriv(u), uu = mul(u, u);
        Ser den;
        if (!strcmp(h, "atan")) den = add(constant(num_si(1), uu.N), uu, 0);
        else den = apply("sqrt", add(constant(num_si(1), uu.N), uu, 1), x, a, N + 2);
        Ser q = mul(du, inv(den));
        if (!strcmp(h, "acos")) q = scale(q, num_si(-1));
        out = integ(q, call1(h, c0));
    } else am_fail("series: no expansion known for %s", h);
    free(w);
    if (out.N > N) out.N = N;
    return out;
}

static Ser of_value(Value *f, int x, Value *a, slong N);

/* a generator at the point: x -> a + t, another variable -> itself, a function term -> its series */
static Ser of_gen(int g, int x, Value *a, slong N) {
    if (g == x) { Ser t = mk(0, N + 64); t.c[0] = a; t.c[1] = num_si(1); return t; }   /* a + t, exact */
    if (!am_vars[g].kernel || am_vars[g].numval || am_free_of(am_gen(g), x)) return constant(am_gen(g), N + 64);
    if (am_vars[g].nargs != 1) am_fail("series: no expansion known for %s", am_vars[g].name);
    Ser u = of_value(am_vars[g].args[0], x, a, N + 2);
    return apply(am_vars[g].head, u, x, a, N);
}

static Ser of_poly(const fmpz_mpoly_t p, int x, Value *a, slong N) {
    Ser sum = mk(0, N + 64);
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_used_vars(used, p, am_mp);
    Ser gs[AM_MAXVARS];
    for (int i = 0; i < am_nvars; i++) if (used[i]) gs[i] = of_gen(i, x, a, N);
    ulong ex[AM_MAXVARS]; fmpz_t c; fmpz_init(c);
    for (slong t = 0; t < fmpz_mpoly_length(p, am_mp); t++) {
        fmpz_mpoly_get_term_exp_ui(ex, p, t, am_mp);
        fmpz_mpoly_get_term_coeff_fmpz(c, p, t, am_mp);
        Value *cv = v_num(); ca_set_fmpz(cv->num, c, am_ca);
        Ser term = constant(cv, N + 64);
        for (int i = 0; i < am_nvars; i++) if (ex[i]) term = mul(term, powi(gs[i], (slong)ex[i]));
        sum = add(sum, term, 0);
    }
    fmpz_clear(c);
    return sum;
}

static Ser of_value(Value *f, int x, Value *a, slong N) {
    if (f->kind == V_NUM) return constant(f, N + 64);
    if (f->kind != V_RF) am_fail("series needs an expression");
    Ser n = of_poly(fmpz_mpoly_q_numref(f->rf), x, a, N);
    if (fmpz_mpoly_is_one(fmpz_mpoly_q_denref(f->rf), am_mp)) return n;
    Ser d = of_poly(fmpz_mpoly_q_denref(f->rf), x, a, N + 4);
    return mul(n, inv(d));
}

/* the series of f at x = a to order N (absolute), retrying with more terms when divisions lose some */
static Ser series_at(Value *f, int x, Value *a, slong N) {
    for (slong extra = 0; extra <= 24; extra += 4) {
        Ser s = of_value(f, x, a, N + extra);
        if (s.flat || s.huge) return s;
        if (s.bounded) am_fail("limit: the expression oscillates (sin or cos of a growing argument) and does not settle");
        if (s.N >= N) { s.N = N; normalize(&s); if (s.v > N) s.v = N; return s; }
    }
    am_fail("series: could not reach the order asked for");
}

static Value *as_value(Ser s, Value *tv) {
    Value *r = zero();
    for (slong p = s.v; p < s.N; p++) r = v_add(r, v_mul(coef(&s, p), v_pow(tv, num_si(p))));
    return r;
}

static int var_arg(Value *v, const char *f) {
    int g = am_gen_of(v);
    if (g < 0 || am_vars[g].kernel) am_fail("%s: expected a variable", f);
    return g;
}

/* the series written term by term, in ascending powers of (x - a) */
static char *series_text(Ser s, int x, Value *pt, slong N, int with_O) {
    char *ps = v_str_of(pt);
    int at0 = pt->kind == V_NUM && ca_check_is_zero(pt->num, am_ca) == T_TRUE;
    char base[512];
    if (at0) snprintf(base, sizeof base, "%s", am_varnames[x]);
    else if (ps[0] == '-') snprintf(base, sizeof base, "(%s + %s)", am_varnames[x], ps + 1);
    else snprintf(base, sizeof base, "(%s - %s)", am_varnames[x], ps);
    free(ps);
    size_t cap = 256, n = 0;
    char *out = malloc(cap); out[0] = 0;
    #define PUT(str) do { size_t l_ = strlen(str); while (n + l_ + 1 > cap) { cap *= 2; out = realloc(out, cap); } memcpy(out + n, str, l_ + 1); n += l_; } while (0)
    for (slong p = s.v; p < s.N; p++) {
        Value *c = coef(&s, p);
        if (is_zero(c)) continue;
        char pw[600] = "";
        if (p == 1) snprintf(pw, sizeof pw, "%s", base);
        else if (p != 0) snprintf(pw, sizeof pw, "%s^%ld", base, (long)p);
        fmpq_t q; fmpq_init(q);
        char *term;
        if (v_is_rational(c, q)) {
            int neg = fmpq_sgn(q) < 0;
            fmpq_abs(q, q);
            char *nn = fmpz_get_str(NULL, 10, fmpq_numref(q)), *dd = fmpz_get_str(NULL, 10, fmpq_denref(q));
            term = malloc(strlen(nn) + strlen(dd) + strlen(pw) + 8);
            int one_n = fmpz_is_one(fmpq_numref(q)), one_d = fmpz_is_one(fmpq_denref(q));
            if (!pw[0]) sprintf(term, one_d ? "%s" : "%s/%s", nn, dd);
            else if (one_n) sprintf(term, one_d ? "%s" : "%s/%s", pw, dd);
            else sprintf(term, one_d ? "%s*%s" : "%s*%s/%s", nn, pw, dd);
            flint_free(nn); flint_free(dd);
            PUT(n ? (neg ? " - " : " + ") : (neg ? "-" : ""));
        } else {
            char *cs = v_str_of(c);
            int sum = strstr(cs + 1, " + ") || strstr(cs + 1, " - ");
            term = malloc(strlen(cs) + strlen(pw) + 8);
            if (!pw[0]) sprintf(term, "%s", cs);
            else sprintf(term, sum ? "(%s)*%s" : "%s*%s", cs, pw);
            free(cs);
            if (n && term[0] == '-' && !sum) { PUT(" - "); memmove(term, term + 1, strlen(term)); }
            else PUT(n ? " + " : "");
        }
        fmpq_clear(q);
        PUT(term);
        free(term);
    }
    if (with_O) {
        char o[620];
        snprintf(o, sizeof o, "%sO(%s^%ld)", n ? " + " : "", base, (long)N);
        PUT(o);
    }
    if (!n && !with_O) PUT("0");
    #undef PUT
    return out;
}

static void coefficient_fact(Ser s) {
    size_t cap = 64, n = 0;
    char *f = malloc(cap); f[0] = 0;
    for (slong p = s.v; p < s.N; p++) {
        char *cs = v_str_of(coef(&s, p)), *js = am_json_str(cs);
        size_t need = n + strlen(js) + 4;
        while (need >= cap) { cap *= 2; f = realloc(f, cap); }
        n += (size_t)sprintf(f + n, "%s%s", n ? "," : "", js);
        free(cs); free(js);
    }
    am_fact("coefficients", "[%s]", f);
    free(f);
}

static slong order_arg(Value *v) {
    fmpq_t q; fmpq_init(q);
    if (!v_is_rational(v, q) || !fmpz_is_one(fmpq_denref(q)) || fmpz_cmp_si(fmpq_numref(q), 0) <= 0 || fmpz_cmp_si(fmpq_numref(q), 200) > 0)
        am_fail("series: the order must be a whole number from 1 to 200");
    slong N = fmpz_get_si(fmpq_numref(q));
    fmpq_clear(q);
    return N;
}

/* taylor(f, x[, a[, n]]): the polynomial (or Laurent polynomial) without the O term, for further computation */
Value *b_taylor(Value **a, int n) {
    if (n < 2 || n > 4) am_fail("taylor(f, x[, a[, n]]): the expression, the variable, the point (default 0), the order (default 6)");
    int x = var_arg(a[1], "taylor");
    Value *pt = n > 2 ? a[2] : zero();
    slong N = n > 3 ? order_arg(a[3]) : 6;
    Value *tv = v_sub(am_gen(x), pt);
    log_t = call1("log", tv);
    probable_zero = 0;
    cur_dir = 0;
    Ser s = series_at(a[0], x, pt, N);
    if (s.flat || s.huge) am_fail("taylor: the expansion involves exp of an infinite term (not a power series)");
    if (probable_zero) am_status(S_PROBABLE, "exact coefficients, but a coefficient was taken as 0 on numerical evidence");
    else am_status(S_EXACT, "the terms of the series below order %ld, exactly", (long)N);
    am_fact("order", "%ld", (long)N);
    coefficient_fact(s);
    return as_value(s, tv);
}

/* series(f, x[, a[, n]]) */
Value *b_series(Value **a, int n) {
    if (n < 2 || n > 4) am_fail("series(f, x[, a[, n]]): the expression, the variable, the point (default 0), the order (default 6)");
    int x = var_arg(a[1], "series");
    Value *pt = n > 2 ? a[2] : zero();
    slong N = n > 3 ? order_arg(a[3]) : 6;
    if (pt->kind == V_NUM && ca_is_special(pt->num, am_ca)) am_fail("series at infinity: use series(subs(f, x = 1/t), t) for now");
    Value *tv = v_sub(am_gen(x), pt);
    Value *lt = call1("log", tv);
    log_t = lt;
    probable_zero = 0;
    cur_dir = 0;
    Ser s = series_at(a[0], x, pt, N);
    if (s.flat || s.huge) am_fail("series: the expansion involves exp of an infinite term (not a power series)");
    char *txt = series_text(s, x, pt, N, 1);
    Value *r = v_str(txt);
    free(txt);
    coefficient_fact(s);
    if (probable_zero) am_status(S_PROBABLE, "exact coefficients, but a coefficient was taken as 0 on numerical evidence");
    else am_status(S_EXACT, "exact coefficients up to the order shown");
    am_fact("order", "%ld", (long)N);
    am_fact("valuation", "%ld", (long)s.v);
    return r;
}

/* ---------------- limits ---------------- */

static Value *infinity(int sign) { Value *v = v_num(); if (sign > 0) ca_pos_inf(v->num, am_ca); else if (sign < 0) ca_neg_inf(v->num, am_ca); else ca_uinf(v->num, am_ca); return v; }

/* the sign of a real number, or 0 if it is not known to be real */
static int sign_of(Value *c) {
    c = am_reevaluate(c);
    fmpq_t q; fmpq_init(q);
    if (v_is_rational(c, q)) { int sg = fmpq_sgn(q); fmpq_clear(q); return sg; }
    fmpq_clear(q);
    if (c->kind != V_NUM) return 0;
    if (ca_check_is_real(c->num, am_ca) != T_TRUE) return 0;
    if (ca_check_gt(c->num, zero()->num, am_ca) == T_TRUE) return 1;
    if (ca_check_lt(c->num, zero()->num, am_ca) == T_TRUE) return -1;
    return 0;
}

/* limit(f, x, a[, "+"|"-"]) */
Value *b_limit(Value **a, int n) {
    if (n < 3 || n > 4) am_fail("limit(f, x, a[, dir]): dir is \"+\" (from the right) or \"-\"; a may be oo or -oo");
    int x = var_arg(a[1], "limit");
    int dir = 0;
    if (n == 4) {
        if (a[3]->kind != V_STR || (strcmp(a[3]->str, "+") && strcmp(a[3]->str, "-"))) am_fail("limit: the direction is \"+\" or \"-\"");
        dir = a[3]->str[0] == '+' ? 1 : -1;
    }
    Value *pt = a[2], *f = a[0];
    int at_inf = 0;
    if (pt->kind == V_NUM && ca_is_special(pt->num, am_ca)) {
        if (ca_check_is_pos_inf(pt->num, am_ca) == T_TRUE) at_inf = 1;
        else if (ca_check_is_neg_inf(pt->num, am_ca) == T_TRUE) at_inf = -1;
        else am_fail("limit: the point must be a number, oo or -oo");
        /* x = 1/t (t -> 0+) or x = -1/t, function terms re-evaluated */
        Value *eq = v_list(2); eq->kind = V_EQ;
        eq->items[0] = am_gen(x); eq->items[1] = v_div(num_si(at_inf), am_gen(x));
        Value *b[2] = {f, eq};
        f = am_call("subs", b, 2);
        pt = zero();
        dir = 1;
    }
    if (dir && !at_inf) {                                     /* one-sided: x = a +- t^2, so half powers become whole */
        Value *eq = v_list(2); eq->kind = V_EQ;
        eq->items[0] = am_gen(x);
        eq->items[1] = v_add(pt, v_mul(num_si(dir), v_mul(am_gen(x), am_gen(x))));
        Value *b[2] = {f, eq};
        f = am_call("subs", b, 2);
        pt = zero();
    }
    Value *tv = v_sub(am_gen(x), pt);
    log_t = call1("log", tv);
    int lt = am_gen_of(log_t);
    probable_zero = 0;
    Ser s;
    slong N = 4;
    cur_dir = dir ? 1 : 0;                                     /* after the substitutions, t -> 0+ for one-sided limits */
    for (;;) {
        s = series_at(f, x, pt, N);
        if (s.flat || s.huge) {
            Value *res = s.flat ? zero() : infinity(s.huge);
            am_status(S_PROVED, s.flat ? "an exponential smaller than every power dominates: the limit is 0" : "an exponential larger than every power dominates");
            if (dir) am_fact("direction", "\"%s\"", dir > 0 ? "+" : "-");
            return res;
        }
        if (len(&s) > 0) break;
        if ((N *= 2) > 64) am_fail("limit: the series vanishes to order 64; the limit may be 0 but this is not proved");
    }
    Value *c = s.c[0];
    Value *res;
    int lead_has_log = lt >= 0 && !am_free_of(c, lt) ? 1 : 0;
    if (lt >= 0 && c->kind == V_RF) {
        int used[AM_MAXVARS] = {0};
        fmpz_mpoly_q_used_vars(used, c->rf, am_mp);
        lead_has_log = used[lt];
    }
    if (lead_has_log && dir == 0) dir = 1;                     /* log(x - a) is real only from the right */
    if (s.v > 0) res = zero();
    else if (s.v == 0 && !lead_has_log) res = c;
    else {
        /* infinite: the sign of the leading term */
        int sg;
        if (lead_has_log && s.v >= 0) {
            /* c = polynomial in L = log(t), L -> -oo: the sign of the top coefficient times (-1)^degree */
            if (s.v > 0) { res = zero(); goto done; }
            fmpz_mpoly_struct *num = fmpz_mpoly_q_numref(c->rf);
            slong d = fmpz_mpoly_degree_si(num, lt, am_mp);
            Value *top = v_rf();
            fmpz_mpoly_t tmp; fmpz_mpoly_init(tmp, am_mp);
            slong vars1[1] = {lt}; ulong exps1[1] = {(ulong)d};
            fmpz_mpoly_get_coeff_vars_ui(tmp, num, vars1, exps1, 1, am_mp);
            fmpz_mpoly_set(fmpz_mpoly_q_numref(top->rf), tmp, am_mp);
            fmpz_mpoly_set(fmpz_mpoly_q_denref(top->rf), fmpz_mpoly_q_denref(c->rf), am_mp);
            fmpz_mpoly_clear(tmp, am_mp);
            sg = sign_of(top) * ((d & 1) ? -1 : 1);
        } else {
            sg = sign_of(c);
            if (s.v < 0 && (-s.v) & 1) {                       /* an odd pole: the sides differ */
                if (dir == 0) {
                    am_status(S_PROVED, "the leading term is c*t^%ld with an odd power: +oo on one side, -oo on the other", (long)s.v);
                    am_fact("exists", "false");
                    return v_str("does not exist (the one-sided limits are +oo and -oo)");
                }
                sg *= dir;
            }
        }
        if (!sg) { res = infinity(0); am_fact("infinite", "true"); }
        else res = infinity(sg);
    }
done:
    if (res->kind == V_RF && !am_free_of(res, x)) am_fail("limit: internal, the limit depends on x");
    if (probable_zero) am_status(S_PROBABLE, "from the series at the point, but a coefficient was taken as 0 on numerical evidence");
    else am_status(S_PROVED, "read off the leading term of the series at the point (exact coefficients)");
    am_fact("leading_power", "%ld", (long)s.v);
    if (dir) am_fact("direction", "\"%s\"", dir > 0 ? "+" : "-");
    (void)at_inf;
    return res;
}
