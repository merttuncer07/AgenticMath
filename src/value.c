/* Values and their arithmetic: exact numbers (Calcium), rational functions over Q (FLINT), lists, equations. */
#include "am.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/fexpr.h>
#include <flint/fexpr_builtin.h>

/* ---------------- the statement's pool of temporaries ---------------- */

static Value **pool;
static int npool, cappool;

static Value *v_new(Kind k) {
    Value *v = calloc(1, sizeof *v);
    if (!v) { fprintf(stderr, "out of memory\n"); exit(2); }
    v->kind = k;
    if (k == V_NUM) ca_init(v->num, am_ca);
    if (k == V_RF) fmpz_mpoly_q_init(v->rf, am_mp);
    if (npool == cappool) { cappool = cappool ? 2 * cappool : 256; pool = realloc(pool, (size_t)cappool * sizeof *pool); }
    pool[npool++] = v;
    return v;
}

static void v_free(Value *v) {
    if (v->kind == V_NUM) ca_clear(v->num, am_ca);
    if (v->kind == V_RF) fmpz_mpoly_q_clear(v->rf, am_mp);
    free(v->items);
    free(v->str);
    free(v);
}

void am_pool_keep(Value *v) {
    for (int i = 0; i < npool; i++) if (pool[i] == v) pool[i] = NULL;
    if (v->kind == V_LIST || v->kind == V_EQ) for (int i = 0; i < v->n; i++) am_pool_keep(v->items[i]);
}

void am_pool_release(void) {
    for (int i = 0; i < npool; i++) if (pool[i]) v_free(pool[i]);
    npool = 0;
}

Value *v_num(void) { return v_new(V_NUM); }
Value *v_rf(void) { return v_new(V_RF); }
Value *v_list(int n) { Value *v = v_new(V_LIST); v->n = n; v->items = calloc((size_t)(n ? n : 1), sizeof(Value *)); return v; }
Value *v_bool(int t) { Value *v = v_new(V_BOOL); v->truth = t; return v; }
Value *v_str(const char *s) { Value *v = v_new(V_STR); v->str = strdup(s); return v; }

Value *v_copy(const Value *a) {
    Value *v;
    switch (a->kind) {
    case V_NUM: v = v_num(); ca_set(v->num, a->num, am_ca); return v;
    case V_RF: v = v_rf(); fmpz_mpoly_q_set(v->rf, a->rf, am_mp); return v;
    case V_LIST: case V_EQ:
        v = v_list(a->n); v->kind = a->kind;
        for (int i = 0; i < a->n; i++) v->items[i] = v_copy(a->items[i]);
        return v;
    case V_BOOL: return v_bool(a->truth);
    case V_STR: return v_str(a->str);
    }
    return NULL;
}

/* ---------------- conversions ---------------- */

int v_is_rational(const Value *v, fmpq_t out) {
    if (v->kind == V_NUM) {
        if (!CA_IS_QQ(v->num, am_ca)) return 0;
        fmpq_set(out, CA_FMPQ(v->num));
        return 1;
    }
    if (v->kind == V_RF) {
        const fmpz_mpoly_struct *n = fmpz_mpoly_q_numref(v->rf), *d = fmpz_mpoly_q_denref(v->rf);
        if (!fmpz_mpoly_is_fmpz(n, am_mp) || !fmpz_mpoly_is_fmpz(d, am_mp)) return 0;
        fmpz_t a, b; fmpz_init(a); fmpz_init(b);
        fmpz_mpoly_get_fmpz(a, n, am_mp); fmpz_mpoly_get_fmpz(b, d, am_mp);
        fmpq_set_fmpz_frac(out, a, b);
        fmpz_clear(a); fmpz_clear(b);
        return 1;
    }
    return 0;
}

Value *v_to_rf(const Value *v) {
    if (v->kind == V_RF) return (Value *)v;
    fmpq_t q; fmpq_init(q);
    if (!v_is_rational(v, q)) {
        fmpq_clear(q);
        if (v->kind == V_NUM) return am_number_kernel(v);   /* sqrt(2) among variables: a generator */
        am_fail("expected a number or a polynomial");
    }
    Value *r = v_rf();
    fmpz_mpoly_q_set_fmpq(r->rf, q, am_mp);
    fmpq_clear(q);
    return r;
}

/* a constant rational function as an exact number */
static Value *rf_to_num_if_const(Value *v) {
    fmpq_t q; fmpq_init(q);
    if (v->kind == V_RF && v_is_rational(v, q)) { Value *r = v_num(); ca_set_fmpq(r->num, q, am_ca); fmpq_clear(q); return r; }
    fmpq_clear(q);
    return v;
}

/* ---------------- arithmetic ---------------- */

typedef enum { OP_ADD, OP_SUB, OP_MUL, OP_DIV } Op;

static Value *arith(const Value *a, const Value *b, Op op) {
    if (a->kind == V_LIST || b->kind == V_LIST) {             /* element by element, or a number with each element */
        if (a->kind == V_LIST && b->kind == V_LIST && a->n != b->n) am_fail("lists of different lengths (%d and %d)", a->n, b->n);
        int n = a->kind == V_LIST ? a->n : b->n;
        Value *r = v_list(n);
        for (int i = 0; i < n; i++)
            r->items[i] = arith(a->kind == V_LIST ? a->items[i] : a, b->kind == V_LIST ? b->items[i] : b, op);
        return r;
    }
    if (a->kind == V_EQ || b->kind == V_EQ) {                 /* both sides of an equation */
        if (a->kind == V_EQ && b->kind == V_EQ) am_fail("cannot combine two equations with an operator");
        Value *r = v_list(2); r->kind = V_EQ;
        for (int i = 0; i < 2; i++) r->items[i] = arith(a->kind == V_EQ ? a->items[i] : a, b->kind == V_EQ ? b->items[i] : b, op);
        return r;
    }
    if (a->kind == V_NUM && b->kind == V_NUM) {
        Value *r = v_num();
        switch (op) {
        case OP_ADD: ca_add(r->num, a->num, b->num, am_ca); break;
        case OP_SUB: ca_sub(r->num, a->num, b->num, am_ca); break;
        case OP_MUL: ca_mul(r->num, a->num, b->num, am_ca); break;
        case OP_DIV:
            if (ca_check_is_zero(b->num, am_ca) == T_TRUE) am_fail("division by zero");
            ca_div(r->num, a->num, b->num, am_ca);
            break;
        }
        return r;
    }
    if ((a->kind != V_NUM && a->kind != V_RF) || (b->kind != V_NUM && b->kind != V_RF)) am_fail("arithmetic needs numbers or polynomials");
    Value *x = v_to_rf(a), *y = v_to_rf(b), *r = v_rf();
    switch (op) {
    case OP_ADD: fmpz_mpoly_q_add(r->rf, x->rf, y->rf, am_mp); break;
    case OP_SUB: fmpz_mpoly_q_sub(r->rf, x->rf, y->rf, am_mp); break;
    case OP_MUL: fmpz_mpoly_q_mul(r->rf, x->rf, y->rf, am_mp); break;
    case OP_DIV:
        if (fmpz_mpoly_q_is_zero(y->rf, am_mp)) am_fail("division by zero");
        fmpz_mpoly_q_div(r->rf, x->rf, y->rf, am_mp);
        break;
    }
    return rf_to_num_if_const(r);
}

Value *v_add(const Value *a, const Value *b) { return arith(a, b, OP_ADD); }
Value *v_sub(const Value *a, const Value *b) { return arith(a, b, OP_SUB); }
Value *v_mul(const Value *a, const Value *b) { return arith(a, b, OP_MUL); }
Value *v_div(const Value *a, const Value *b) { return arith(a, b, OP_DIV); }

Value *v_neg(const Value *a) {
    Value *m = v_num();
    ca_set_si(m->num, -1, am_ca);
    return v_mul(m, a);
}

Value *v_pow(const Value *a, const Value *b) {
    if (a->kind == V_LIST) {
        Value *r = v_list(a->n);
        for (int i = 0; i < a->n; i++) r->items[i] = v_pow(a->items[i], b);
        return r;
    }
    if (a->kind == V_NUM && b->kind == V_NUM) {
        if (ca_check_is_zero(a->num, am_ca) == T_TRUE && ca_check_is_zero(b->num, am_ca) == T_TRUE) am_fail("0^0 is undefined");
        if (ca_check_is_zero(a->num, am_ca) == T_TRUE && CA_IS_QQ(b->num, am_ca) && fmpq_sgn(CA_FMPQ(b->num)) < 0) am_fail("division by zero");
        Value *r = v_num();
        ca_pow(r->num, a->num, b->num, am_ca);
        return r;
    }
    fmpq_t e; fmpq_init(e);
    if (!v_is_rational(b, e) || !fmpz_is_one(fmpq_denref(e))) { fmpq_clear(e); am_fail("a polynomial can only be raised to a whole power"); }
    if (fmpz_cmp_si(fmpq_numref(e), 100000) > 0 || fmpz_cmp_si(fmpq_numref(e), -100000) < 0) { fmpq_clear(e); am_fail("exponent too large"); }
    slong k = fmpz_get_si(fmpq_numref(e));
    fmpq_clear(e);
    Value *x = v_to_rf(a);
    if (k < 0) {
        if (fmpz_mpoly_q_is_zero(x->rf, am_mp)) am_fail("division by zero");
        Value *t = v_rf(); fmpz_mpoly_q_inv(t->rf, x->rf, am_mp); x = t; k = -k;
    }
    Value *r = v_rf();                                        /* the num and den powers stay coprime */
    fmpz_mpoly_pow_ui(fmpz_mpoly_q_numref(r->rf), fmpz_mpoly_q_numref(x->rf), (ulong)k, am_mp);
    fmpz_mpoly_pow_ui(fmpz_mpoly_q_denref(r->rf), fmpz_mpoly_q_denref(x->rf), (ulong)k, am_mp);
    return rf_to_num_if_const(r);
}

/* ---------------- writing values ---------------- */

typedef struct { char *s; size_t n, cap; } Str;
static void sput(Str *b, const char *s) {
    size_t n = strlen(s);
    if (b->n + n + 1 > b->cap) { b->cap = (b->n + n + 1) * 2; b->s = realloc(b->s, b->cap); }
    memcpy(b->s + b->n, s, n + 1);
    b->n += n;
}

/* FLINT writes 2*x^2+3*x*y-1; we write 2*x^2 + 3*x*y - 1 */
static void put_spaced(Str *b, const char *s) {
    char one[2] = {0, 0};
    for (const char *p = s; *p; p++) {
        if ((*p == '+' || *p == '-') && p != s && p[-1] != '(' && p[-1] != '^') sput(b, *p == '+' ? " + " : " - ");
        else { one[0] = *p; sput(b, one); }
    }
}

static int is_sum(const char *s) {          /* more than one term at the top level */
    int depth = 0;
    for (const char *p = s; *p; p++) {
        if (*p == '(') depth++;
        else if (*p == ')') depth--;
        else if (depth == 0 && (*p == '+' || *p == '-') && p != s && p[-1] != '^') return 1;
    }
    return 0;
}

static void put_mpoly(Str *b, const fmpz_mpoly_t p, int paren) {
    char *s = fmpz_mpoly_get_str_pretty(p, am_varnames, am_mp);
    int par = paren && is_sum(s);
    if (par) sput(b, "(");
    put_spaced(b, s);
    if (par) sput(b, ")");
    flint_free(s);
}

/* a Calcium expression tree written in ordinary infix */
static void put_fexpr(Str *b, const fexpr_t e, int prec);
static int fx_prec(const fexpr_t e) {
    if (fexpr_is_builtin_call(e, FEXPR_Add) || fexpr_is_builtin_call(e, FEXPR_Sub)) return 1;
    if (fexpr_is_builtin_call(e, FEXPR_Mul) || fexpr_is_builtin_call(e, FEXPR_Div) || fexpr_is_builtin_call(e, FEXPR_Neg)) return 2;
    if (fexpr_is_builtin_call(e, FEXPR_Pow)) return 3;
    if (fexpr_is_integer(e)) { fmpz_t c; fmpz_init(c); fexpr_get_fmpz(c, e); int neg = fmpz_sgn(c) < 0; fmpz_clear(c); return neg ? 2 : 4; }
    return 4;
}
static void put_args(Str *b, const fexpr_t e, const char *sep, int prec) {
    fexpr_t a; slong n = fexpr_nargs(e);
    for (slong i = 0; i < n; i++) {
        fexpr_view_arg(a, e, i);
        if (i) sput(b, sep);
        put_fexpr(b, a, prec);
    }
}
static void put_fexpr(Str *b, const fexpr_t e, int prec) {
    int p = fx_prec(e), par = p < prec;
    if (par) sput(b, "(");
    fexpr_t a, f;
    static const struct { int id; const char *name; } fn[] = {
        {FEXPR_Sqrt, "sqrt"}, {FEXPR_Exp, "exp"}, {FEXPR_Log, "log"}, {FEXPR_Sin, "sin"}, {FEXPR_Cos, "cos"},
        {FEXPR_Tan, "tan"}, {FEXPR_Atan, "atan"}, {FEXPR_Asin, "asin"}, {FEXPR_Acos, "acos"}, {FEXPR_Abs, "abs"},
        {FEXPR_Gamma, "gamma"}, {FEXPR_Erf, "erf"}, {-1, NULL}};
    if (fexpr_is_integer(e)) {
        fmpz_t c; fmpz_init(c); fexpr_get_fmpz(c, e);
        char *s = fmpz_get_str(NULL, 10, c); sput(b, s); flint_free(s); fmpz_clear(c);
    } else if (fexpr_is_builtin_symbol(e, FEXPR_Pi)) sput(b, "pi");
    else if (fexpr_is_builtin_symbol(e, FEXPR_NumberI)) sput(b, "I");
    else if (fexpr_is_builtin_symbol(e, FEXPR_NumberE)) sput(b, "E");
    else if (fexpr_is_builtin_call(e, FEXPR_Where)) {        /* Where(body, Def(a_1, v_1), ...): put the values in */
        fexpr_t body, d, sym, val, t; fexpr_init(body); fexpr_init(t);
        fexpr_view_arg(a, e, 0); fexpr_set(body, a);
        for (slong i = fexpr_nargs(e) - 1; i >= 1; i--) {
            fexpr_view_arg(d, e, i);
            if (!fexpr_is_builtin_call(d, FEXPR_Def) || fexpr_nargs(d) != 2) continue;
            fexpr_view_arg(sym, d, 0); fexpr_view_arg(val, d, 1);
            fexpr_replace(t, body, sym, val); fexpr_swap(t, body);
        }
        put_fexpr(b, body, prec);
        fexpr_clear(body); fexpr_clear(t);
        if (par) sput(b, ")");
        return;
    } else if (fexpr_is_builtin_call(e, FEXPR_PolynomialRootNearest) && fexpr_nargs(e) == 2) {   /* RootOf(p, near) */
        fexpr_t L, c; fmpz_t z; fmpz_init(z);
        fexpr_view_arg(L, e, 0);
        fmpz_poly_t poly; fmpz_poly_init(poly);
        for (slong i = 0; i < fexpr_nargs(L); i++) { fexpr_view_arg(c, L, i); if (fexpr_get_fmpz(z, c)) fmpz_poly_set_coeff_fmpz(poly, i, z); }
        char *ps = fmpz_poly_get_str_pretty(poly, "x");
        sput(b, "RootOf("); put_spaced(b, ps); sput(b, ", ");
        flint_free(ps); fmpz_poly_clear(poly); fmpz_clear(z);
        fexpr_view_arg(c, e, 1); put_fexpr(b, c, 0);
        sput(b, ")");
    } else if (fexpr_is_builtin_call(e, FEXPR_Decimal) && fexpr_nargs(e) == 1) {
        fexpr_view_arg(a, e, 0);
        char *ds = fexpr_get_string(a); sput(b, ds); flint_free(ds);
    } else if (fexpr_is_builtin_call(e, FEXPR_Add)) put_args(b, e, " + ", 1);
    else if (fexpr_is_builtin_call(e, FEXPR_Sub)) {
        fexpr_view_arg(a, e, 0); put_fexpr(b, a, 1);
        for (slong i = 1; i < fexpr_nargs(e); i++) { sput(b, " - "); fexpr_view_arg(a, e, i); put_fexpr(b, a, 2); }
    } else if (fexpr_is_builtin_call(e, FEXPR_Mul)) put_args(b, e, "*", 2);
    else if (fexpr_is_builtin_call(e, FEXPR_Div)) {
        fexpr_view_arg(a, e, 0); put_fexpr(b, a, 2); sput(b, "/");
        fexpr_view_arg(a, e, 1); put_fexpr(b, a, 3);
    } else if (fexpr_is_builtin_call(e, FEXPR_Neg)) { sput(b, "-"); fexpr_view_arg(a, e, 0); put_fexpr(b, a, 3); }
    else if (fexpr_is_builtin_call(e, FEXPR_Pow)) {
        fexpr_view_arg(a, e, 0); put_fexpr(b, a, 4); sput(b, "^");
        fexpr_view_arg(a, e, 1); put_fexpr(b, a, 4);
    } else {
        int done = 0;
        for (int i = 0; fn[i].name && !done; i++)
            if (fexpr_is_builtin_call(e, fn[i].id)) {
                sput(b, fn[i].name); sput(b, "("); put_args(b, e, ", ", 0); sput(b, ")"); done = 1;
            }
        if (!done) { char *s = fexpr_get_str(e); sput(b, s); flint_free(s); }   /* rarer forms: Calcium's own notation */
        (void)f;
    }
    if (par) sput(b, ")");
}

static void put_value(Str *b, const Value *v) {
    switch (v->kind) {
    case V_NUM: {
        if (CA_IS_QQ(v->num, am_ca)) { char *s = fmpq_get_str(NULL, 10, CA_FMPQ(v->num)); sput(b, s); flint_free(s); break; }
        fexpr_t e; fexpr_init(e);
        qqbar_t q; qqbar_init(q);
        if (ca_get_qqbar(q, v->num, am_ca)) {             /* algebraic: a radical formula, else the polynomial and a root */
            if (qqbar_degree(q) > 4 || !qqbar_get_fexpr_formula(e, q, QQBAR_FORMULA_GAUSSIANS | QQBAR_FORMULA_QUADRATICS))
                qqbar_get_fexpr_root_nearest(e, q);
        } else ca_get_fexpr(e, v->num, 0, am_ca);
        qqbar_clear(q);
        put_fexpr(b, e, 0);
        fexpr_clear(e);
        break;
    }
    case V_RF: {
        const fmpz_mpoly_struct *d = fmpz_mpoly_q_denref(v->rf);
        if (fmpz_mpoly_is_one(d, am_mp)) { put_mpoly(b, fmpz_mpoly_q_numref(v->rf), 0); break; }
        put_mpoly(b, fmpz_mpoly_q_numref(v->rf), 1);
        sput(b, "/");
        char *s = fmpz_mpoly_get_str_pretty(d, am_varnames, am_mp);
        int par = is_sum(s) || strchr(s, '*') || strchr(s, '^');
        flint_free(s);
        if (par) sput(b, "(");
        put_mpoly(b, d, 0);
        if (par) sput(b, ")");
        break;
    }
    case V_LIST:
        sput(b, "[");
        for (int i = 0; i < v->n; i++) { if (i) sput(b, ", "); put_value(b, v->items[i]); }
        sput(b, "]");
        break;
    case V_EQ: put_value(b, v->items[0]); sput(b, " = "); put_value(b, v->items[1]); break;
    case V_BOOL: sput(b, v->truth > 0 ? "true" : v->truth == 0 ? "false" : "unknown"); break;
    case V_STR: sput(b, v->str); break;
    }
}

char *v_str_of(const Value *v) {
    Str b = {0, 0, 0};
    sput(&b, "");
    put_value(&b, v);
    for (char *p; (p = strstr(b.s, " + -")); ) { p[1] = '-'; p[2] = ' '; memmove(p + 3, p + 4, strlen(p + 4) + 1); }   /* a + -b is a - b */
    return b.s;
}
