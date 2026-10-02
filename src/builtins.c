/* Built-in functions. Each does its mathematics with FLINT (and Calcium, qqbar), and reports how sure the answer
 * is and the facts the computation produced. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/fmpz_factor.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpz_mpoly_factor.h>
#include <flint/qqbar.h>
#include <flint/acb.h>
#include <flint/ca_vec.h>

#include "msolve_bridge.h"

/* ---------------- helpers ---------------- */

static void need(int n, int lo, int hi, const char *name) {
    if (n < lo || n > hi) {
        if (lo == hi) am_fail("%s takes %d argument%s", name, lo, lo == 1 ? "" : "s");
        am_fail("%s takes %d to %d arguments", name, lo, hi);
    }
}

typedef struct { char *s; size_t n, cap; } Str;
static void sput(Str *b, const char *s) {
    size_t n = strlen(s);
    if (b->n + n + 1 > b->cap) { b->cap = (b->n + n + 1) * 2 + 64; b->s = realloc(b->s, b->cap); }
    memcpy(b->s + b->n, s, n + 1);
    b->n += n;
}
static void sputf(Str *b, const char *fmt, ...) __attribute__((format(printf, 2, 3)));
#include <stdarg.h>
static void sputf(Str *b, const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    char tmp[512]; vsnprintf(tmp, sizeof tmp, fmt, ap);
    va_end(ap);
    sput(b, tmp);
}

/* whole number argument */
static int get_fmpz(const Value *v, fmpz_t out) {
    fmpq_t q; fmpq_init(q);
    int ok = v_is_rational(v, q) && fmpz_is_one(fmpq_denref(q));
    if (ok) fmpz_set(out, fmpq_numref(q));
    fmpq_clear(q);
    return ok;
}
static slong get_si(const Value *v, const char *what) {
    fmpz_t z; fmpz_init(z);
    if (!get_fmpz(v, z) || !fmpz_fits_si(z)) { fmpz_clear(z); am_fail("%s must be a whole number", what); }
    slong r = fmpz_get_si(z);
    fmpz_clear(z);
    return r;
}

/* the variable named by v (a single generator) */
static int var_of(const Value *v) {
    if (v->kind != V_RF || !fmpz_mpoly_is_one(fmpz_mpoly_q_denref(v->rf), am_mp)) am_fail("expected a variable");
    const fmpz_mpoly_struct *p = fmpz_mpoly_q_numref(v->rf);
    for (int i = 0; i < am_nvars; i++) if (fmpz_mpoly_is_gen(p, i, am_mp) && !am_vars[i].kernel) return i;
    am_fail("expected a variable");
}

/* the variables a rational function uses */
static int used_vars(const Value *v, int *out) {
    int used[AM_MAXVARS] = {0}, n = 0;
    if (v->kind == V_RF) fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i]) out[n++] = i;
    return n;
}

/* the only variable, or the one given */
static int main_var(const Value *v, Value **args, int n, int at, const char *fname) {
    if (n > at) return var_of(args[at]);
    int vs[AM_MAXVARS], k = used_vars(v, vs);
    if (k == 1) return vs[0];
    if (k == 0) am_fail("%s: the expression has no variable", fname);
    am_fail("%s: several variables (%s, %s, ...): name one, as %s(p, %s)", fname, am_varnames[vs[0]], am_varnames[vs[1]], fname, am_varnames[vs[0]]);
}

static Value *rf_from_mpoly(const fmpz_mpoly_t num) {
    Value *r = v_rf();
    fmpz_mpoly_set(fmpz_mpoly_q_numref(r->rf), num, am_mp);
    fmpz_mpoly_one(fmpz_mpoly_q_denref(r->rf), am_mp);
    return r;
}

/* p as a polynomial over Q: integer numerator and a positive integer denominator */
static void as_poly(const Value *v, fmpz_mpoly_t num, fmpz_t den, const char *fname) {
    Value *r = v_to_rf(v);
    if (!fmpz_mpoly_is_fmpz(fmpz_mpoly_q_denref(r->rf), am_mp)) am_fail("%s needs a polynomial, not a quotient with variables below", fname);
    fmpz_mpoly_set(num, fmpz_mpoly_q_numref(r->rf), am_mp);
    fmpz_mpoly_get_fmpz(den, fmpz_mpoly_q_denref(r->rf), am_mp);
}

static char *mpoly_str(const fmpz_mpoly_t p) {     /* via the value writer, for the same spacing */
    Value *v = rf_from_mpoly(p);
    return v_str_of(v);
}

/* apply f to every element of a list */
static Value *map1(Value *(*f)(Value **, int), Value **a, int n) {
    if (n >= 1 && a[0]->kind == V_LIST) {
        Value *r = v_list(a[0]->n);
        for (int i = 0; i < a[0]->n; i++) {
            Value **b = calloc((size_t)n, sizeof *b);
            for (int j = 0; j < n; j++) b[j] = a[j];
            b[0] = a[0]->items[i];
            r->items[i] = f(b, n);
            free(b);
        }
        return r;
    }
    return NULL;
}

/* ---------------- numbers: elementary functions (Calcium) ---------------- */

typedef void (*CaFn)(ca_t, const ca_t, ca_ctx_t);
static Value *ca_apply(Value **a, int n, CaFn f, const char *name) {
    need(n, 1, 1, name);
    if (a[0]->kind != V_NUM) {
        fmpq_t q; fmpq_init(q);
        int rat = v_is_rational(a[0], q);
        fmpq_clear(q);
        if (!rat) {                                         /* sin(x): a function term; sin(-u) = -sin(u), cos(-u) = cos(u) */
            if (am_lead_sign(a[0]) < 0) {
                int odd = !strcmp(name, "sin") || !strcmp(name, "tan") || !strcmp(name, "atan") || !strcmp(name, "asin");
                int even = !strcmp(name, "cos");
                if (odd || even) {
                    Value *m = v_neg(a[0]);
                    Value *r = am_call(name, &m, 1);
                    return odd ? v_neg(r) : r;
                }
            }
            return am_kernel_value(name, a, 1);
        }
        a[0] = v_copy(a[0]);
        Value *t = v_num(); fmpq_t r; fmpq_init(r); v_is_rational(a[0], r); ca_set_fmpq(t->num, r, am_ca); fmpq_clear(r); a[0] = t;
    }
    Value *r = v_num();
    f(r->num, a[0]->num, am_ca);
    if (ca_is_special(r->num, am_ca)) am_fail("%s is undefined here", name);
    return r;
}
#define CAFN(cname, flintfn) \
    static Value *b_##cname(Value **a, int n) { Value *m = map1(b_##cname, a, n); return m ? m : ca_apply(a, n, flintfn, #cname); }
CAFN(sqrt, ca_sqrt)
CAFN(exp, ca_exp)
CAFN(log, ca_log)
CAFN(sin, ca_sin)
CAFN(cos, ca_cos)
CAFN(tan, ca_tan)
CAFN(atan, ca_atan)
CAFN(asin, ca_asin)
CAFN(acos, ca_acos)
CAFN(abs, ca_abs)
CAFN(re, ca_re)
CAFN(im, ca_im)
CAFN(conj, ca_conj)
CAFN(floor, ca_floor)
CAFN(ceil, ca_ceil)
CAFN(gamma, ca_gamma)
CAFN(erf, ca_erf)

/* N(x, digits): a decimal with every digit guaranteed (ball arithmetic) */
static Value *b_N(Value **a, int n) {
    Value *m = map1(b_N, a, n); if (m) return m;
    need(n, 1, 2, "N");
    slong d = n > 1 ? get_si(a[1], "the number of digits") : 15;
    if (d < 1 || d > 100000) am_fail("N: digits between 1 and 100000");
    Value *x = a[0];
    if (x->kind == V_EQ) {
        Value *r = v_list(2); r->kind = V_EQ;
        Value *b[2] = {x->items[0], a[1]};
        r->items[0] = x->items[0]->kind == V_RF ? x->items[0] : b_N(b, n);
        b[0] = x->items[1]; r->items[1] = b_N(b, n);
        return r;
    }
    if (x->kind == V_RF) x = am_reevaluate(x);              /* sqrt(2) kept among variables, sin(1/2): numbers again */
    if (x->kind == V_RF) {
        fmpq_t q; fmpq_init(q);
        if (!v_is_rational(x, q)) am_fail("N needs a number, not an expression with variables");
        Value *t = v_num(); ca_set_fmpq(t->num, q, am_ca); fmpq_clear(q); x = t;
    }
    if (x->kind != V_NUM) am_fail("N needs a number");
    char *s = ca_get_decimal_str(x->num, d, 0, am_ca);
    am_status(S_CERTIFIED, "digits guaranteed by ball arithmetic (Arb/Calcium)");
    Value *r = v_str(s);
    flint_free(s);
    return r;
}

/* ---------------- whole numbers ---------------- */

static Value *b_isprime(Value **a, int n) {
    need(n, 1, 1, "isprime");
    fmpz_t z; fmpz_init(z);
    if (!get_fmpz(a[0], z)) am_fail("isprime needs a whole number");
    int p = fmpz_is_prime(z);
    Value *r;
    if (p == 1) {
        r = v_bool(1); am_status(S_PROVED, "primality proved");
        if (am_lean && fmpz_sgn(z) > 0) { char *ns = fmpz_get_str(NULL, 10, z); char *L = malloc(strlen(ns) + 64); sprintf(L, "example : Nat.Prime %s := by norm_num", ns); am_lean_fact(L); free(L); flint_free(ns); }
    }
    else if (p == 0) { r = v_bool(0); am_status(S_PROVED, "a factor or a failed test shows it is composite"); }
    else { r = v_bool(fmpz_is_probabprime(z) ? 1 : 0); am_status(S_NUMERIC, "probable prime test (BPSW) only; no proof"); }
    fmpz_clear(z);
    return r;
}

static Value *factor_number(const Value *v) {
    fmpq_t q; fmpq_init(q);
    v_is_rational(v, q);
    if (fmpq_is_zero(q)) am_fail("0 has no factorization");
    Str b = {0, 0, 0}; sput(&b, "");
    if (fmpq_sgn(q) < 0) sput(&b, "-");
    int nf = 0, probable = 0;
    for (int part = 0; part < 2; part++) {
        fmpz_factor_t F; fmpz_factor_init(F);
        fmpz_factor(F, part ? fmpq_denref(q) : fmpq_numref(q));
        if (part && F->num) sput(&b, " / ");
        if (part && F->num > 1) sput(&b, "(");
        if (!part && F->num == 0) sput(&b, "1");
        for (slong i = 0; i < F->num; i++) {
            char *s = fmpz_get_str(NULL, 10, F->p + i);
            if (i) sput(&b, " * ");
            sput(&b, s); flint_free(s);
            if (F->exp[i] > 1) sputf(&b, "^%lu", (unsigned long)F->exp[i]);
            if (fmpz_is_prime(F->p + i) != 1) probable++;
            nf++;
        }
        if (part && F->num > 1) sput(&b, ")");
        if (!part) {
            am_fact("prime", (F->num == 1 && F->exp[0] == 1 && fmpq_sgn(q) > 0 && fmpz_is_one(fmpq_denref(q))) ? "true" : "false");
            am_fact("distinct_prime_factors", "%ld", (long)F->num);
        }
        fmpz_factor_clear(F);
    }
    if (am_lean && !probable && fmpz_is_one(fmpq_denref(q))) {
        char *ns = fmpz_get_str(NULL, 10, fmpq_numref(q));
        char *L = malloc(strlen(ns) + strlen(b.s) + 64);
        sprintf(L, "example : (%s : ℤ) = %s := by norm_num", ns, b.s);
        am_lean_fact(L);
        free(L); flint_free(ns);
    }
    if (probable) am_status(S_NUMERIC, "%d factor%s only probable primes (no proof)", probable, probable > 1 ? "s" : "");
    else am_status(S_PROVED, "every factor proved prime; multiplied back");
    fmpq_clear(q);
    Value *r = v_str(b.s);
    free(b.s);
    return r;
}

/* ---------------- polynomials ---------------- */

static void put_factors(Str *b, fmpz_mpoly_factor_t F, int *nterms) {
    for (slong i = 0; i < F->num; i++) {
        char *s = mpoly_str(F->poly + i);
        int sum = strchr(s + 1, '+') || strstr(s + 1, " - ");
        int par = sum && (F->num > 1 || !fmpz_is_one(F->exp + i) || (nterms && *nterms));
        if (b->n && b->s[b->n - 1] != '(' && b->s[b->n - 1] != '-') sput(b, "*");
        if (par && sum) sput(b, "(");
        sput(b, s);
        if (par && sum) sput(b, ")");
        if (!fmpz_is_one(F->exp + i)) { char *e = fmpz_get_str(NULL, 10, F->exp + i); sputf(b, "^%s", e); flint_free(e); }
        free(s);
    }
}

static Value *b_factor(Value **a, int n) {
    Value *m = map1(b_factor, a, n); if (m) return m;
    need(n, 1, 1, "factor");
    fmpq_t q; fmpq_init(q);
    int rat = v_is_rational(a[0], q);
    fmpq_clear(q);
    if (rat) return factor_number(a[0]);
    if (a[0]->kind != V_RF) am_fail("factor needs a whole number, a fraction or a polynomial");
    int vs[AM_MAXVARS], nv = used_vars(a[0], vs);
    fmpz_mpoly_factor_t F[2];
    fmpq_t unit; fmpq_init(unit); fmpq_one(unit);
    for (int part = 0; part < 2; part++) {
        fmpz_mpoly_factor_init(F[part], am_mp);
        const fmpz_mpoly_struct *p = part ? fmpz_mpoly_q_denref(a[0]->rf) : fmpz_mpoly_q_numref(a[0]->rf);
        if (!fmpz_mpoly_factor(F[part], p, am_mp)) am_fail("factor: the engine could not factor this polynomial");
        fmpz_mpoly_factor_sort(F[part], am_mp);
        fmpq_t c; fmpq_init(c);
        fmpz_mpoly_factor_get_constant_fmpq(c, F[part], am_mp);
        if (part) fmpq_div(unit, unit, c); else fmpq_mul(unit, unit, c);
        fmpq_clear(c);
    }
    /* the product, multiplied back */
    fmpz_mpoly_t back; fmpz_mpoly_init(back, am_mp);
    for (int part = 0; part < 2; part++) {
        fmpz_mpoly_factor_expand(back, F[part], am_mp);
        if (!fmpz_mpoly_equal(back, part ? fmpz_mpoly_q_denref(a[0]->rf) : fmpz_mpoly_q_numref(a[0]->rf), am_mp))
            am_fail("internal: the factors do not multiply back");
    }
    fmpz_mpoly_clear(back, am_mp);
    Str b = {0, 0, 0}; sput(&b, "");
    if (!fmpq_is_one(unit)) {
        if (fmpz_is_one(fmpq_numref(unit)) && fmpz_equal_si(fmpq_denref(unit), 1)) ;
        else if (fmpz_equal_si(fmpq_numref(unit), -1) && fmpz_is_one(fmpq_denref(unit))) sput(&b, "-");
        else {
            char *s = fmpq_get_str(NULL, 10, unit);
            if (fmpz_is_one(fmpq_denref(unit))) sput(&b, s); else sputf(&b, "(%s)", s);
            flint_free(s);
        }
    }
    int has_unit = b.n > 0;
    put_factors(&b, F[0], &has_unit);
    if (F[0]->num == 0 && (b.n == 0 || !strcmp(b.s, "-"))) sput(&b, "1");
    if (F[1]->num) {
        sput(&b, "/");
        int par = F[1]->num > 1 || !fmpz_is_one(F[1]->exp);
        if (par) sput(&b, "(");
        Str d = {0, 0, 0}; sput(&d, "");
        int one = 1;
        put_factors(&d, F[1], &one);
        sput(&b, d.s); free(d.s);
        if (par) sput(&b, ")");
    }
    if (am_lean) {                                               /* the factorization is an identity: ring */
        char *lv = am_lean_vars(vs, nv), *in = v_str_of(a[0]);
        char *L = malloc(strlen(lv) + strlen(in) + strlen(b.s) + 96);
        sprintf(L, "example %s: %s = %s := by ring", lv, in, b.s);
        am_lean_fact(L);
        free(L); free(lv); free(in);
    }
    if (nv == 1) am_status(S_PROVED, "every factor proved irreducible over Q (complete univariate factorization); multiplied back");
    else am_status(S_EXACT, "irreducible factors over Q from FLINT's multivariate factorization; multiplied back");
    {   /* facts read off the factors of the numerator */
        Str deg = {0, 0, 0}, mul = {0, 0, 0}, roots = {0, 0, 0};
        sput(&deg, "["); sput(&mul, "["); sput(&roots, "[");
        int sqfree = 1, nroots = 0;
        for (slong i = 0; i < F[0]->num; i++) {
            slong dg = fmpz_mpoly_total_degree_si(F[0]->poly + i, am_mp);
            sputf(&deg, "%s%ld", i ? "," : "", (long)dg);
            char *e = fmpz_get_str(NULL, 10, F[0]->exp + i); sputf(&mul, "%s%s", i ? "," : "", e); flint_free(e);
            if (!fmpz_is_one(F[0]->exp + i)) sqfree = 0;
            if (nv == 1 && dg == 1) {                            /* a x + b: the root -b/a */
                fmpz_t c0, c1; fmpz_init(c0); fmpz_init(c1);
                ulong ex[AM_MAXVARS] = {0};
                fmpz_mpoly_get_coeff_fmpz_ui(c0, F[0]->poly + i, ex, am_mp);
                ex[vs[0]] = 1;
                fmpz_mpoly_get_coeff_fmpz_ui(c1, F[0]->poly + i, ex, am_mp);
                fmpq_t r; fmpq_init(r); fmpq_set_fmpz_frac(r, c0, c1); fmpq_neg(r, r);
                char *s = fmpq_get_str(NULL, 10, r);
                char *js = am_json_str(s);
                sputf(&roots, "%s%s", nroots++ ? "," : "", js);
                free(js); flint_free(s); fmpq_clear(r); fmpz_clear(c0); fmpz_clear(c1);
            }
        }
        sput(&deg, "]"); sput(&mul, "]"); sput(&roots, "]");
        am_fact("irreducible", F[0]->num == 1 && fmpz_is_one(F[0]->exp) && fmpq_is_one(unit) && F[1]->num == 0 ? "true" : "false");
        am_fact("squarefree", sqfree ? "true" : "false");
        am_fact("factor_degrees", "%s", deg.s);
        am_fact("multiplicities", "%s", mul.s);
        if (nv == 1) am_fact("rational_roots", "%s", roots.s);
        free(deg.s); free(mul.s); free(roots.s);
    }
    fmpz_mpoly_factor_clear(F[0], am_mp); fmpz_mpoly_factor_clear(F[1], am_mp);
    fmpq_clear(unit);
    Value *r = v_str(b.s);
    free(b.s);
    return r;
}

static Value *b_expand(Value **a, int n) { need(n, 1, 1, "expand"); return a[0]; }

static Value *b_simplify(Value **a, int n) {
    Value *m = map1(b_simplify, a, n); if (m) return m;
    need(n, 1, 1, "simplify");
    Value *v = am_reevaluate(a[0]);
    Value *nf = am_normal_form(v);
    char *s1 = v_str_of(v), *s2 = v_str_of(nf);
    Value *r = strlen(s2) < strlen(s1) ? nf : v;
    free(s1); free(s2);
    return r;
}

/* coeff(p, x, k): the coefficient of x^k in p (a polynomial in x; the coefficient may involve other symbols) */
static Value *b_coeff(Value **a, int n) {
    need(n, 3, 3, "coeff");
    int x = var_of(a[1]);
    slong k = get_si(a[2], "the power");
    if (k < 0) return v_num();
    Value *p = a[0];
    if (p->kind == V_NUM) return k == 0 ? p : v_num();
    if (p->kind != V_RF || !am_free_of(rf_from_mpoly(fmpz_mpoly_q_denref(p->rf)), x)) am_fail("coeff: a polynomial in %s", am_varnames[x]);
    fmpz_mpoly_t c; fmpz_mpoly_init(c, am_mp);
    slong vars[1] = {x}; ulong exps[1] = {(ulong)k};
    fmpz_mpoly_get_coeff_vars_ui(c, fmpz_mpoly_q_numref(p->rf), vars, exps, 1, am_mp);
    Value *r = v_div(rf_from_mpoly(c), rf_from_mpoly(fmpz_mpoly_q_denref(p->rf)));
    fmpz_mpoly_clear(c, am_mp);
    return r;
}

static Value *b_numer(Value **a, int n) {
    need(n, 1, 1, "numer");
    Value *x = v_to_rf(a[0]);
    return rf_from_mpoly(fmpz_mpoly_q_numref(x->rf));
}

static Value *b_denom(Value **a, int n) {
    need(n, 1, 1, "denom");
    Value *x = v_to_rf(a[0]);
    return rf_from_mpoly(fmpz_mpoly_q_denref(x->rf));
}

static Value *b_gcd(Value **a, int n) {
    if (n < 2) am_fail("gcd takes two or more arguments");
    fmpz_t g, z; fmpz_init(g); fmpz_init(z);
    int all_int = 1;
    for (int i = 0; i < n; i++) if (!get_fmpz(a[i], z)) all_int = 0;
    if (all_int) {
        for (int i = 0; i < n; i++) { get_fmpz(a[i], z); fmpz_gcd(g, g, z); }
        Value *r = v_num(); ca_set_fmpz(r->num, g, am_ca);
        fmpz_clear(g); fmpz_clear(z);
        return r;
    }
    fmpz_clear(g); fmpz_clear(z);
    fmpz_mpoly_t G, P; fmpz_t d; fmpz_mpoly_init(G, am_mp); fmpz_mpoly_init(P, am_mp); fmpz_init(d);
    for (int i = 0; i < n; i++) {
        as_poly(a[i], P, d, "gcd");
        if (!fmpz_mpoly_gcd(G, G, P, am_mp)) am_fail("gcd: the engine failed");
    }
    Value *r = rf_from_mpoly(G);           /* over Q: made monic in its leading coefficient's sign, content 1 */
    fmpz_mpoly_clear(G, am_mp); fmpz_mpoly_clear(P, am_mp); fmpz_clear(d);
    return r;
}

/* is v free of the variable x, looking inside function terms? */
int am_free_of(const Value *v, int x) {
    if (v->kind == V_LIST || v->kind == V_EQ) { for (int i = 0; i < v->n; i++) if (!am_free_of(v->items[i], x)) return 0; return 1; }
    if (v->kind != V_RF) return 1;
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) {
        if (!used[i]) continue;
        if (i == x) return 0;
        if (am_vars[i].kernel && !am_vars[i].numval)
            for (int j = 0; j < am_vars[i].nargs; j++) if (!am_free_of(am_vars[i].args[j], x)) return 0;
    }
    return 1;
}

/* d/dx of one generator: 1 for x, 0 for constants and other variables, the rules' answer for a function term */
static Value *dgen(int v, int x) {
    Value *z = v_num();
    if (v == x) { ca_one(z->num, am_ca); return z; }
    if (!am_vars[v].kernel || am_vars[v].numval) return z;
    Value *g = am_gen(v);
    if (am_free_of(g, x)) return z;
    Value *args[2] = {g, am_gen(x)};
    return am_call("diff", args, 2);
}

/* d/dx of a polynomial with integer coefficients, through the chain rule */
static Value *dpoly(const fmpz_mpoly_t p, int x) {
    Value *r = v_num();
    int used[AM_MAXVARS] = {0};
    fmpz_mpoly_used_vars(used, p, am_mp);
    fmpz_mpoly_t d; fmpz_mpoly_init(d, am_mp);
    for (int v = 0; v < am_nvars; v++) {
        if (!used[v]) continue;
        Value *dv = dgen(v, x);
        if (dv->kind == V_NUM && ca_check_is_zero(dv->num, am_ca) == T_TRUE) continue;
        fmpz_mpoly_derivative(d, p, v, am_mp);
        r = v_add(r, v_mul(rf_from_mpoly(d), dv));
    }
    fmpz_mpoly_clear(d, am_mp);
    return r;
}

/* d/dx of a rational function: (N' D - N D') / D^2 */
static Value *diff_once(Value *f, int x) {
    if (f->kind == V_NUM) return v_num();
    if (f->kind == V_LIST || f->kind == V_EQ) {
        Value *r = v_list(f->n); r->kind = f->kind;
        for (int i = 0; i < f->n; i++) r->items[i] = diff_once(f->items[i], x);
        return r;
    }
    if (f->kind != V_RF) am_fail("diff needs an expression");
    int g = am_gen_of(f);                                       /* a lone function term no rule knows: f'(x) stays symbolic */
    if (g >= 0 && am_vars[g].kernel && !am_vars[g].numval) {
        if (am_free_of(f, x)) return v_num();
        Value *args[2] = {f, am_gen(x)};
        return am_kernel_value("diff", args, 2);
    }
    const fmpz_mpoly_struct *N = fmpz_mpoly_q_numref(f->rf), *D = fmpz_mpoly_q_denref(f->rf);
    Value *dN = dpoly(N, x);
    if (fmpz_mpoly_is_one(D, am_mp)) return dN;
    Value *Nv = rf_from_mpoly(N), *Dv = rf_from_mpoly(D);
    return v_div(v_sub(v_mul(dN, Dv), v_mul(Nv, dpoly(D, x))), v_mul(Dv, Dv));
}
static Value *b_diff(Value **a, int n) {
    need(n, 1, 3, "diff");
    int x = main_var(a[0], a, n, 1, "diff");
    slong k = n > 2 ? get_si(a[2], "the order") : 1;
    if (k < 0 || k > 10000) am_fail("diff: order between 0 and 10000");
    if (n == 2) return diff_once(a[0], x);                    /* the rules for diff(f, x) were tried before this */
    Value *f = a[0];
    for (slong i = 0; i < k; i++) { Value *args[2] = {f, am_gen(x)}; f = am_call("diff", args, 2); }
    return f;
}

static Value *b_degree(Value **a, int n) {
    need(n, 1, 2, "degree");
    fmpz_mpoly_t p; fmpz_t d; fmpz_mpoly_init(p, am_mp); fmpz_init(d);
    as_poly(a[0], p, d, "degree");
    slong deg = n > 1 ? fmpz_mpoly_degree_si(p, var_of(a[1]), am_mp) : fmpz_mpoly_total_degree_si(p, am_mp);
    Value *r = v_num(); ca_set_si(r->num, deg, am_ca);
    fmpz_mpoly_clear(p, am_mp); fmpz_clear(d);
    return r;
}

static Value *b_resultant(Value **a, int n) {
    need(n, 3, 3, "resultant");
    int x = var_of(a[2]);
    fmpz_mpoly_t p, q, r; fmpz_t dp, dq; fmpz_mpoly_init(p, am_mp); fmpz_mpoly_init(q, am_mp); fmpz_mpoly_init(r, am_mp); fmpz_init(dp); fmpz_init(dq);
    as_poly(a[0], p, dp, "resultant"); as_poly(a[1], q, dq, "resultant");
    if (!fmpz_mpoly_resultant(r, p, q, x, am_mp)) am_fail("resultant: the engine failed");
    Value *v = rf_from_mpoly(r);
    slong degp = fmpz_mpoly_degree_si(p, x, am_mp), degq = fmpz_mpoly_degree_si(q, x, am_mp);
    Value *s = v_num(); fmpq_t c; fmpq_init(c);                 /* res(p/dp, q/dq) = res(p, q) / (dp^degq dq^degp) */
    fmpz_t t; fmpz_init(t); fmpz_pow_ui(t, dp, (ulong)degq); fmpz_t u; fmpz_init(u); fmpz_pow_ui(u, dq, (ulong)degp); fmpz_mul(t, t, u);
    fmpz_one(fmpq_numref(c)); fmpz_set(fmpq_denref(c), t); fmpq_canonicalise(c);
    ca_set_fmpq(s->num, c, am_ca);
    fmpq_clear(c); fmpz_clear(t); fmpz_clear(u);
    fmpz_mpoly_clear(p, am_mp); fmpz_mpoly_clear(q, am_mp); fmpz_mpoly_clear(r, am_mp); fmpz_clear(dp); fmpz_clear(dq);
    return v_mul(v, s);
}

static Value *b_discriminant(Value **a, int n) {
    need(n, 1, 2, "discriminant");
    int x = main_var(a[0], a, n, 1, "discriminant");
    fmpz_mpoly_t p, r; fmpz_t d; fmpz_mpoly_init(p, am_mp); fmpz_mpoly_init(r, am_mp); fmpz_init(d);
    as_poly(a[0], p, d, "discriminant");
    if (!fmpz_mpoly_discriminant(r, p, x, am_mp)) am_fail("discriminant: the engine failed");
    Value *v = rf_from_mpoly(r);
    slong k = fmpz_mpoly_degree_si(p, x, am_mp);                /* disc(p/d) = disc(p) / d^(2k-2) */
    Value *s = v_num(); fmpz_t t; fmpz_init(t); fmpz_pow_ui(t, d, (ulong)(2 * k - 2 > 0 ? 2 * k - 2 : 0));
    fmpq_t c; fmpq_init(c); fmpz_one(fmpq_numref(c)); fmpz_set(fmpq_denref(c), t); ca_set_fmpq(s->num, c, am_ca);
    fmpq_clear(c); fmpz_clear(t);
    fmpz_mpoly_clear(p, am_mp); fmpz_mpoly_clear(r, am_mp); fmpz_clear(d);
    return v_mul(v, s);
}

/* substitute values for variables in a rational function, term by term */
static Value *mpoly_subs(const fmpz_mpoly_t p, Value **val) {
    Value *sum = v_num();
    slong len = fmpz_mpoly_length(p, am_mp);
    fmpz_t c; fmpz_init(c);
    ulong ex[AM_MAXVARS];
    for (slong t = 0; t < len; t++) {
        fmpz_mpoly_get_term_coeff_fmpz(c, p, t, am_mp);
        fmpz_mpoly_get_term_exp_ui(ex, p, t, am_mp);
        Value *term = v_num(); ca_set_fmpz(term->num, c, am_ca);
        for (int i = 0; i < am_nvars; i++)
            if (ex[i]) {
                Value *e = v_num(); ca_set_ui(e->num, ex[i], am_ca);
                term = v_mul(term, v_pow(val[i], e));
            }
        sum = v_add(sum, term);
    }
    fmpz_clear(c);
    return sum;
}
Value *am_subs_rf(const Value *f, Value **val) {
    if (f->kind != V_RF) return (Value *)f;
    Value *N = mpoly_subs(fmpz_mpoly_q_numref(f->rf), val), *D = mpoly_subs(fmpz_mpoly_q_denref(f->rf), val);
    if (D->kind == V_NUM && ca_check_is_zero(D->num, am_ca) == T_TRUE) am_fail("the substitution makes a denominator 0");
    return v_div(N, D);
}
static Value *b_subs(Value **a, int n) {
    if (n < 2) am_fail("subs takes an expression and x = value (or a list of them)");
    Value *val[AM_MAXVARS];
    for (int i = 0; i < am_nvars; i++) {                         /* each variable stands for itself unless given */
        Value *g = v_rf();
        fmpz_mpoly_gen(fmpz_mpoly_q_numref(g->rf), i, am_mp);
        fmpz_mpoly_one(fmpz_mpoly_q_denref(g->rf), am_mp);
        val[i] = g;
    }
    Value *eqs[64]; int ne = 0;
    int changed[AM_MAXVARS] = {0}, needed[AM_MAXVARS] = {0};
    if (n == 3 && a[1]->kind == V_RF) { int v = var_of(a[1]); val[v] = a[2]; changed[v] = 1; }
    else {
        for (int i = 1; i < n; i++) {
            if (a[i]->kind == V_LIST) for (int j = 0; j < a[i]->n && ne < 64; j++) eqs[ne++] = a[i]->items[j];
            else if (ne < 64) eqs[ne++] = a[i];
        }
        for (int i = 0; i < ne; i++) {
            if (eqs[i]->kind != V_EQ) am_fail("subs: give each substitution as x = value");
            int v = var_of(eqs[i]->items[0]);
            val[v] = eqs[i]->items[1]; changed[v] = 1;
        }
    }
    int n0 = am_nvars;                                           /* only the terms there now: new ones are already substituted */
    {   /* the terms the expression uses, with the terms inside their arguments */
        Value *f = a[0];
        int nf = (f->kind == V_LIST || f->kind == V_EQ) ? f->n : 1;
        for (int k = 0; k < nf; k++) {
            Value *g = (f->kind == V_LIST || f->kind == V_EQ) ? f->items[k] : f;
            if (g->kind == V_RF) { int u[AM_MAXVARS] = {0}; fmpz_mpoly_q_used_vars(u, g->rf, am_mp); for (int i = 0; i < n0; i++) needed[i] |= u[i]; }
        }
        for (int i = n0 - 1; i >= 0; i--) {
            if (!needed[i] || !am_vars[i].kernel || am_vars[i].numval) continue;
            for (int j = 0; j < am_vars[i].nargs; j++) if (am_vars[i].args[j]->kind == V_RF) {
                int u[AM_MAXVARS] = {0}; fmpz_mpoly_q_used_vars(u, am_vars[i].args[j]->rf, am_mp);
                for (int k = 0; k < n0; k++) needed[k] |= u[k];
            }
        }
    }
    for (int i = 0; i < n0; i++) {                               /* function terms: their arguments substituted, then re-evaluated */
        if (!am_vars[i].kernel) continue;
        if (am_vars[i].numval) { val[i] = am_vars[i].numval; continue; }
        if (!needed[i]) continue;
        int touched = 0, vars = 0;                               /* arguments the substitution does not reach: the term stays */
        for (int j = 0; j < am_vars[i].nargs && !touched; j++) if (am_vars[i].args[j]->kind == V_RF) {
            int u[AM_MAXVARS] = {0}; fmpz_mpoly_q_used_vars(u, am_vars[i].args[j]->rf, am_mp);
            for (int k = 0; k < n0; k++) if (u[k]) { vars = 1; if (changed[k]) touched = 1; }
        }
        if (!vars) touched = 1;                                  /* log(2): evaluated again, a number */
        if (!touched) continue;
        changed[i] = 1;
        Value **ka = malloc((size_t)(am_vars[i].nargs ? am_vars[i].nargs : 1) * sizeof *ka);
        for (int j = 0; j < am_vars[i].nargs; j++) ka[j] = am_subs_rf(am_vars[i].args[j], val);
        val[i] = am_call(am_vars[i].head, ka, am_vars[i].nargs);
        free(ka);
    }
    Value *f = a[0];
    if (f->kind == V_LIST || f->kind == V_EQ) {
        Value *r = v_list(f->n); r->kind = f->kind;
        for (int i = 0; i < f->n; i++) r->items[i] = am_subs_rf(f->items[i], val);
        return r;
    }
    return am_subs_rf(f, val);
}

/* ---------------- roots: exact algebraic numbers (qqbar) ---------------- */

static Value *roots_of(Value *p0, int x, int real_only, int as_equations) {
    fmpz_mpoly_t p; fmpz_t d; fmpz_mpoly_init(p, am_mp); fmpz_init(d);
    as_poly(p0, p, d, "roots");
    int vs[AM_MAXVARS], nv = used_vars(p0, vs);
    if (nv > 1 || (nv == 1 && vs[0] != x)) am_fail("roots: the polynomial must be in %s alone", am_varnames[x]);
    fmpz_poly_t u; fmpz_poly_init(u);
    if (!fmpz_mpoly_get_fmpz_poly(u, p, x, am_mp)) am_fail("internal: not univariate");
    slong deg = fmpz_poly_degree(u);
    if (deg < 1) am_fail("roots: the polynomial has no roots (degree %ld)", (long)deg);
    if (deg > 2000) am_fail("roots: degree above 2000");
    qqbar_ptr r = _qqbar_vec_init(deg);
    qqbar_roots_fmpz_poly(r, u, 0);                              /* every root, repeated by multiplicity */
    Value *out = v_list(0);
    Value **items = calloc((size_t)deg, sizeof *items);
    int k = 0, nreal = 0, nrat = 0;
    Str mult = {0, 0, 0}; sput(&mult, "[");
    for (slong i = 0; i < deg; i++) {
        if (i > 0 && qqbar_equal(r + i, r + i - 1)) continue;
        slong m = 1;
        while (i + m < deg && qqbar_equal(r + i + m, r + i)) m++;
        int real = qqbar_is_real(r + i);
        nreal += real;
        if (qqbar_degree(r + i) == 1) nrat++;
        if (real_only && !real) continue;
        Value *v = v_num();
        ca_set_qqbar(v->num, r + i, am_ca);
        if (as_equations) {
            Value *e = v_list(2); e->kind = V_EQ;
            Value *g = v_rf(); fmpz_mpoly_gen(fmpz_mpoly_q_numref(g->rf), x, am_mp); fmpz_mpoly_one(fmpz_mpoly_q_denref(g->rf), am_mp);
            e->items[0] = g; e->items[1] = v; v = e;
        }
        items[k++] = v;
        sputf(&mult, "%s%ld", k > 1 ? "," : "", (long)m);
    }
    sput(&mult, "]");
    out->n = k; free(out->items); out->items = items;
    am_status(S_PROVED, "exact algebraic numbers (qqbar); every root of the polynomial, counted once");
    am_fact("degree", "%ld", (long)deg);
    am_fact("real_roots", "%d", nreal);
    am_fact("rational_roots", "%d", nrat);
    am_fact("multiplicities", "%s", mult.s);
    free(mult.s);
    _qqbar_vec_clear(r, deg);
    fmpz_poly_clear(u); fmpz_mpoly_clear(p, am_mp); fmpz_clear(d);
    return out;
}
static Value *eq_to_expr(Value *e) { return e->kind == V_EQ ? v_sub(e->items[0], e->items[1]) : e; }
static Value *b_roots(Value **a, int n) {
    need(n, 1, 2, "roots");
    Value *p = eq_to_expr(a[0]);
    return roots_of(p, main_var(p, a, n, 1, "roots"), 0, 0);
}
static Value *b_realroots(Value **a, int n) {
    need(n, 1, 2, "realroots");
    Value *p = eq_to_expr(a[0]);
    return roots_of(p, main_var(p, a, n, 1, "realroots"), 1, 0);
}

/* a system: msolve's parametrization, each solution then made exact and checked by substitution */
static Value *gen_value(int i) {
    Value *g = v_rf();
    fmpz_mpoly_gen(fmpz_mpoly_q_numref(g->rf), i, am_mp);
    fmpz_mpoly_one(fmpz_mpoly_q_denref(g->rf), am_mp);
    return g;
}
/* p(t) by Horner's rule. (FLINT 3.3.1's ca_fmpz_poly_evaluate returns 0 for t in a number field; this avoids it.) */
static void ca_horner(ca_t res, const fmpz_poly_t p, const ca_t t) {
    ca_t h; ca_init(h, am_ca);
    for (slong i = fmpz_poly_degree(p); i >= 0; i--) { ca_mul(h, h, t, am_ca); ca_add_fmpz(h, h, p->coeffs + i, am_ca); }
    ca_swap(res, h, am_ca);
    ca_clear(h, am_ca);
}

static Value *solve_system(Value **eqs, int ne, int *vars, int nvar) {
    int is_var[AM_MAXVARS] = {0};
    for (int i = 0; i < nvar; i++) is_var[vars[i]] = 1;
    const char *names[AM_MAXVARS];
    char nbuf[AM_MAXVARS][12];
    for (int i = 0; i < AM_MAXVARS; i++) { snprintf(nbuf[i], sizeof nbuf[i], "p%d", i); names[i] = nbuf[i]; }
    for (int i = 0; i < nvar; i++) { snprintf(nbuf[vars[i]], sizeof nbuf[0], "x%d", i + 1); }
    Str in = {0, 0, 0}; sput(&in, "");
    for (int i = 0; i < nvar; i++) sputf(&in, "%sx%d", i ? "," : "", i + 1);
    sput(&in, "\n0\n");
    int real_eqs = 0;
    for (int i = 0; i < ne; i++) {
        if (eqs[i]->kind == V_NUM) {
            if (ca_check_is_zero(eqs[i]->num, am_ca) == T_TRUE) continue;      /* 0 = 0 */
            am_status(S_PROVED, "an equation reduces to a nonzero constant");
            am_fact("solutions", "0");
            return v_list(0);
        }
        if (eqs[i]->kind != V_RF) am_fail("solve: equations must be polynomial (or rational) in the variables");
        int vs[AM_MAXVARS], k = used_vars(eqs[i], vs);
        for (int j = 0; j < k; j++) if (!is_var[vs[j]]) am_fail("solve: %s is not among the unknowns; parameters in systems are not supported yet", am_varnames[vs[j]]);
        char *ps = fmpz_mpoly_get_str_pretty(fmpz_mpoly_q_numref(eqs[i]->rf), names, am_mp);
        sputf(&in, "%s", real_eqs ? ",\n" : "");
        sput(&in, ps);
        flint_free(ps);
        real_eqs++;
    }
    sput(&in, "\n");
    if (!real_eqs) am_fail("solve: no equations left");
    am_work("msolve: %d equation%s in %d unknown%s", real_eqs, real_eqs > 1 ? "s" : "", nvar, nvar > 1 ? "s" : "");
    MsolveResult R;
    am_msolve(&R, in.s, 60);
    free(in.s);
    const char *rests = "that the list is complete rests on msolve's multi-modular Groebner basis (correct with high probability)";
    if (R.kind == -1) {
        am_status(S_PROBABLE, "no solution, even complex: msolve's Groebner basis is {1} (multi-modular; correct with high probability)");
        am_fact("solutions", "0");
        return v_list(0);
    }
    if (R.kind == 1) {
        am_status(S_PROBABLE, "the solutions form a set of dimension at least 1 (msolve; multi-modular)");
        am_fact("finite", "false");
        return v_str("infinitely many solutions (a curve or larger): not a finite list");
    }
    slong deg = fmpz_poly_degree(R.w);
    am_work("rational parametrization: w(t) of degree %ld; %ld real solutions isolated", (long)deg, R.nreal);
    if (deg > 200) { am_msolve_clear(&R); am_fail("solve: %ld solutions; listing them exactly is limited to 200 for now", (long)deg); }
    /* which of msolve's variables is which of ours */
    int map[AM_MAXVARS + 1];
    for (int i = 0; i < R.nvars; i++) { map[i] = -1; if (R.names[i][0] == 'x') { int k = atoi(R.names[i] + 1); if (k >= 1 && k <= nvar) map[i] = vars[k - 1]; } }
    qqbar_ptr r = _qqbar_vec_init(deg);
    qqbar_roots_fmpz_poly(r, R.w, 0);
    Value *out = v_list(0);
    Value **sols = calloc((size_t)(deg ? deg : 1), sizeof *sols);
    int nsol = 0, excluded = 0, undecided = 0;
    for (slong k = 0; k < deg; k++) {
        if (k > 0 && qqbar_equal(r + k, r + k - 1)) continue;
        ca_t t, wd, vi, x; ca_init(t, am_ca); ca_init(wd, am_ca); ca_init(vi, am_ca); ca_init(x, am_ca);
        ca_set_qqbar(t, r + k, am_ca);
        ca_horner(wd, R.wd, t);
        Value *val[AM_MAXVARS];
        for (int i = 0; i < AM_MAXVARS; i++) val[i] = i < am_nvars ? gen_value(i) : NULL;
        int have[AM_MAXVARS] = {0};
        for (int i = 0; i < R.ncoord; i++) {
            ca_horner(vi, R.v + i, t);
            ca_mul_fmpz(x, wd, R.c + i, am_ca);
            ca_div(x, vi, x, am_ca);
            ca_neg(x, x, am_ca);
            if (map[i] >= 0) { Value *nv = v_num(); ca_set(nv->num, x, am_ca); val[map[i]] = nv; have[map[i]] = 1; }
        }
        int last = R.nvars - 1;
        if (map[last] >= 0 && !have[map[last]]) {               /* t = sum lf_i x_i gives the last one */
            ca_set(x, t, am_ca);
            for (int i = 0; i < last; i++) if (map[i] >= 0 && !fmpq_is_zero(R.lf + i)) {
                ca_mul_fmpq(vi, val[map[i]]->num, R.lf + i, am_ca); ca_sub(x, x, vi, am_ca);
            }
            ca_div_fmpq(x, x, R.lf + last, am_ca);
            Value *nv = v_num(); ca_set(nv->num, x, am_ca); val[map[last]] = nv; have[map[last]] = 1;
        }
        for (int i = 0; i < nvar; i++) if (!have[vars[i]]) am_fail("internal: msolve gave no value for %s", am_varnames[vars[i]]);
        /* check: every equation exactly 0, every denominator not 0 */
        int ok = 1;
        for (int i = 0; i < ne && ok; i++) {
            if (eqs[i]->kind != V_RF) continue;
            Value *D = mpoly_subs(fmpz_mpoly_q_denref(eqs[i]->rf), val);
            if (D->kind == V_NUM && ca_check_is_zero(D->num, am_ca) == T_TRUE) { ok = 0; excluded++; break; }
            Value *N = mpoly_subs(fmpz_mpoly_q_numref(eqs[i]->rf), val);
            truth_t z = N->kind == V_NUM ? ca_check_is_zero(N->num, am_ca) : T_FALSE;
            if (z == T_FALSE) am_fail("internal: a solution from msolve does not satisfy the equations");
            if (z == T_UNKNOWN) undecided++;
        }
        ca_clear(t, am_ca); ca_clear(wd, am_ca); ca_clear(vi, am_ca); ca_clear(x, am_ca);
        if (!ok) continue;
        Value *sol = v_list(nvar);
        for (int i = 0; i < nvar; i++) {
            Value *e = v_list(2); e->kind = V_EQ;
            e->items[0] = gen_value(vars[i]); e->items[1] = val[vars[i]];
            sol->items[i] = e;
        }
        sols[nsol++] = sol;
    }
    /* a fixed order, whatever msolve's random choices: by the real, then imaginary, parts of x1, x2, ... */
    double *key = calloc((size_t)(nsol ? nsol : 1) * (size_t)nvar * 2, sizeof(double));
    for (int k = 0; k < nsol; k++)
        for (int i = 0; i < nvar; i++) {
            acb_t z; acb_init(z);
            ca_get_acb(z, sols[k]->items[i]->items[1]->num, 64, am_ca);
            key[(k * nvar + i) * 2] = arf_get_d(arb_midref(acb_realref(z)), ARF_RND_NEAR);
            key[(k * nvar + i) * 2 + 1] = arf_get_d(arb_midref(acb_imagref(z)), ARF_RND_NEAR);
            acb_clear(z);
        }
    for (int i = 1; i < nsol; i++)
        for (int j = i; j > 0; j--) {
            int c = 0;
            for (int t = 0; t < 2 * nvar && !c; t++) {
                int ti = (t % nvar) * 2 + t / nvar;                 /* all real parts first, then imaginary parts */
                double a = key[(j - 1) * nvar * 2 + ti], b = key[j * nvar * 2 + ti];
                if (a < b - 1e-12) c = -1; else if (a > b + 1e-12) c = 1;
            }
            if (c <= 0) break;
            Value *tv = sols[j]; sols[j] = sols[j - 1]; sols[j - 1] = tv;
            for (int t = 0; t < 2 * nvar; t++) { double d = key[j * nvar * 2 + t]; key[j * nvar * 2 + t] = key[(j - 1) * nvar * 2 + t]; key[(j - 1) * nvar * 2 + t] = d; }
        }
    free(key);
    free(out->items); out->items = sols; out->n = nsol;
    _qqbar_vec_clear(r, deg);
    am_fact("solutions", "%d", nsol);
    am_fact("real_solutions", "%ld", R.nreal);
    if (excluded) am_fact("excluded_by_denominators", "%d", excluded);
    am_work("each solution put back into the equations with exact arithmetic");
    if (undecided) am_status(S_UNKNOWN, "%d check%s could not be decided by exact arithmetic", undecided, undecided > 1 ? "s" : "");
    else am_status(S_PROBABLE, "every solution listed satisfies the equations exactly (checked); %s", rests);
    am_msolve_clear(&R);
    return out;
}

/* solve(equation or list of equations, variable or list of variables) */
static Value *b_solve(Value **a, int n) {
    need(n, 1, 2, "solve");
    Value *eqs[64]; int ne = 0;
    if (a[0]->kind == V_LIST) for (int i = 0; i < a[0]->n && ne < 64; i++) eqs[ne++] = eq_to_expr(a[0]->items[i]);
    else eqs[ne++] = eq_to_expr(a[0]);
    int vars[AM_MAXVARS], nvar = 0;
    if (n > 1) {
        if (a[1]->kind == V_LIST) for (int i = 0; i < a[1]->n; i++) vars[nvar++] = var_of(a[1]->items[i]);
        else vars[nvar++] = var_of(a[1]);
    } else {
        int used[AM_MAXVARS] = {0};
        for (int i = 0; i < ne; i++) { int vs[AM_MAXVARS], k = used_vars(eqs[i], vs); for (int j = 0; j < k; j++) used[vs[j]] = 1; }
        for (int i = 0; i < am_nvars; i++) if (used[i]) vars[nvar++] = i;
    }
    if (ne == 1 && nvar == 1) {
        Value *num = eqs[0]->kind == V_RF ? rf_from_mpoly(fmpz_mpoly_q_numref(eqs[0]->rf)) : eqs[0];
        int vs[AM_MAXVARS], k = used_vars(num, vs);
        if (k == 1 && vs[0] == vars[0] && eqs[0]->kind == V_RF && fmpz_mpoly_is_fmpz(fmpz_mpoly_q_denref(eqs[0]->rf), am_mp))
            return roots_of(num, vars[0], 0, 1);
        return am_solve1(eqs[0], vars[0]);
    }
    return solve_system(eqs, ne, vars, nvar);
}

static Value *b_binomial(Value **a, int n) {
    need(n, 2, 2, "binomial");
    fmpz_t N, K, r; fmpz_init(N); fmpz_init(K); fmpz_init(r);
    if (!get_fmpz(a[0], N) || !get_fmpz(a[1], K) || !fmpz_fits_si(K) || fmpz_sgn(N) < 0 || !fmpz_abs_fits_ui(N)) am_fail("binomial needs whole numbers n >= 0, k");
    slong k = fmpz_get_si(K);
    if (k < 0) fmpz_zero(r); else fmpz_bin_uiui(r, fmpz_get_ui(N), (ulong)k);
    Value *v = v_num(); ca_set_fmpz(v->num, r, am_ca);
    fmpz_clear(N); fmpz_clear(K); fmpz_clear(r);
    return v;
}

Value *b_integrate(Value **a, int n);
Value *b_cofactors(Value **a, int n);
Value *b_dsolve(Value **a, int n);
Value *b_series(Value **a, int n);
Value *b_taylor(Value **a, int n);
Value *b_limit(Value **a, int n);

static Value *b_free(Value **a, int n) {
    need(n, 2, 2, "free");
    return v_bool(am_free_of(a[0], var_of(a[1])));
}

/* ---------------- the table ---------------- */

static const struct { const char *name; Builtin f; const char *sig, *doc; } TABLE[] = {
    {"factor", b_factor, "factor(n) | factor(p)", "prime factors of a whole number or fraction (primes proved); irreducible factors of a polynomial over Q"},
    {"roots", b_roots, "roots(p[, x])", "every complex root of a polynomial in one variable, as exact algebraic numbers, each once"},
    {"realroots", b_realroots, "realroots(p[, x])", "the real roots of a polynomial, exactly"},
    {"solve", b_solve, "solve(eq, x) | solve([eqs], [vars])", "every solution of one equation (polynomials exactly; symbolic coefficients up to degree 2 by formula; exp, log, sqrt and trigonometric terms inverted, with integer parameters n1, n2, ... for periodic families; the fact real_solutions lists the real ones), or of a polynomial system (msolve); each solution checked by substitution; == is read as = here"},
    {"integrate", b_integrate, "integrate(f, x) | integrate(f, x, a, b)", "an antiderivative, checked by differentiating it back (or the definite integral: F(b) - F(a) checked against certified numerical integration, the certified decimal when no antiderivative is found, divergence proved at a pole); rational functions exactly (Hermite, Rothstein-Trager, arctangents), polynomials times exp/sin/cos/log/atan by parts, and the library's rules"},
    {"free", b_free, "free(e, x)", "true when e does not depend on x (looking inside function terms)"},
    {"series", b_series, "series(f, x[, a[, n]])", "the power series (Taylor or Laurent) of f at x = a (default 0) to order n (default 6), exact coefficients, written with O(...); log(x - a) kept as a symbol where it appears; the facts list the coefficients"},
    {"taylor", b_taylor, "taylor(f, x[, a[, n]])", "the terms of the series below order n, as an expression to compute with (no O term)"},
    {"limit", b_limit, "limit(f, x, a[, \"+\" | \"-\"])", "the limit at a (a number, oo or -oo), from the leading term of the series; one-sided with \"+\" or \"-\""},
    {"cofactors", b_cofactors, "cofactors(g, [h1, ..., hk])", "polynomials c_i with g = c_1 h_1 + ... + c_k h_k (so g = 0 follows from the h_i = 0), checked by expansion; with the lean prefix, a Lean 4 proof by linear_combination"},
    {"dsolve", b_dsolve, "dsolve(eq, y, x[, [y(x0) = v0, y'(x0) = v1, ...]])", "linear ordinary differential equations: constant coefficients of any order (with a right-hand side by variation of parameters) and first order; y', y'' for derivatives; the solution is checked by substitution"},
    {"N", b_N, "N(x[, digits])", "a decimal with every digit guaranteed (default 15 digits); works on lists and equations"},
    {"diff", b_diff, "diff(f, x[, n])", "derivative (n-th) with respect to x, through sin, exp, log, f(x), ... by the chain rule"},
    {"subs", b_subs, "subs(f, x = a[, y = b]) | subs(f, [x = a, ...]) | subs(f, x, a)", "substitute values for variables; function terms are re-evaluated"},
    {"gcd", b_gcd, "gcd(a, b, ...)", "greatest common divisor of whole numbers or polynomials"},
    {"resultant", b_resultant, "resultant(p, q, x)", "resultant of two polynomials with respect to x"},
    {"discriminant", b_discriminant, "discriminant(p[, x])", "discriminant of a polynomial with respect to x"},
    {"coeff", b_coeff, "coeff(p, x, k)", "the coefficient of x^k in the polynomial p"},
    {"degree", b_degree, "degree(p[, x])", "total degree, or the degree in x"},
    {"expand", b_expand, "expand(e)", "the expanded form (every polynomial result is already expanded)"},
    {"simplify", b_simplify, "simplify(e)", "a shorter equal form: lowest terms, exponentials combined, trigonometric identities (sin^2 + cos^2 = 1, multiple angles) and sqrt(u)^2 = u applied when they shorten it"},
    {"numer", b_numer, "numer(e)", "numerator of a rational function"},
    {"denom", b_denom, "denom(e)", "denominator of a rational function"},
    {"isprime", b_isprime, "isprime(n)", "true or false, with a proof of primality when one is found"},
    {"binomial", b_binomial, "binomial(n, k)", "the binomial coefficient"},
    {"sqrt", b_sqrt, "sqrt(x)", "square root (principal branch); exact for numbers, a function term for expressions"},
    {"exp", b_exp, "exp(x)", "exponential"}, {"log", b_log, "log(x)", "natural logarithm (principal branch)"},
    {"ln", b_log, "ln(x)", "the same as log"},
    {"sin", b_sin, "sin(x)", "sine"}, {"cos", b_cos, "cos(x)", "cosine"}, {"tan", b_tan, "tan(x)", "tangent"},
    {"atan", b_atan, "atan(x)", "arctangent"}, {"asin", b_asin, "asin(x)", "arcsine"}, {"acos", b_acos, "acos(x)", "arccosine"},
    {"erf", b_erf, "erf(x)", "the error function"},
    {"abs", b_abs, "abs(x)", "absolute value of a number"}, {"re", b_re, "re(x)", "real part"}, {"im", b_im, "im(x)", "imaginary part"},
    {"conj", b_conj, "conj(x)", "complex conjugate"}, {"floor", b_floor, "floor(x)", "largest integer <= x"},
    {"ceil", b_ceil, "ceil(x)", "smallest integer >= x"}, {"gamma", b_gamma, "gamma(x)", "the gamma function"},
    {NULL, NULL, NULL, NULL}};

/* the documentation of the built-ins: i-th entry, or NULL past the end */
int am_builtin_doc(int i, const char **name, const char **sig, const char **doc) {
    int nt = 0; while (TABLE[nt].name) nt++;
    if (i >= nt) {
        int nm = 0; const char *a, *b, *c; while (am_matrix_doc(nm, &a, &b, &c)) nm++;
        if (i - nt < nm) return am_matrix_doc(i - nt, name, sig, doc);
        return am_discrete_doc(i - nt - nm, name, sig, doc);
    }
    *name = TABLE[i].name; *sig = TABLE[i].sig; *doc = TABLE[i].doc;
    return 1;
}

Builtin am_builtin(const char *name, size_t len) {
    for (int i = 0; TABLE[i].name; i++) if (strlen(TABLE[i].name) == len && !strncmp(TABLE[i].name, name, len)) return TABLE[i].f;
    Builtin b = am_matrix_builtin(name, len);
    return b ? b : am_discrete_builtin(name, len);
}
