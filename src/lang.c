/* The language: notation agents already write, read into a tree and evaluated.
 *
 *   statement := ["show"] ( NAME "=" expr | expr )
 *   expr      := sum [ ("=" | "==" | "!=" | "<" | "<=" | ">" | ">=") sum ]   "=" makes an equation, the others a test
 *   sum       := term { ("+" | "-") term }
 *   term      := unary { ("*" | "/") unary | primary }                          2x, 3(x + 1), (x + 1)(x - 1)
 *   unary     := "-" unary | power
 *   power     := postfix [ ("^" | "**") unary ]
 *   postfix   := primary { "!" }
 *   primary   := NUMBER | NAME | NAME "(" [args] ")" | "(" expr ")" | "[" [args] "]"
 *
 * Names are whole words (xy is one variable). A name that is not bound is a variable. pi, E and I are numbers.
 * Decimals are read exactly (0.1 is 1/10). */
#include "am.h"

#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

jmp_buf am_on_error;
static char err_msg[1024];

void am_fail(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(err_msg, sizeof err_msg, fmt, ap);
    va_end(ap);
    longjmp(am_on_error, 1);
}

/* ---------------- contexts and variables ---------------- */

ca_ctx_t am_ca;
fmpz_mpoly_ctx_t am_mp;
const char *am_varnames[AM_MAXVARS];
int am_nvars;

int am_var_index(const char *name, size_t len) {
    for (int i = 0; i < am_nvars; i++) if (strlen(am_varnames[i]) == len && !strncmp(am_varnames[i], name, len)) return i;
    if (am_nvars == AM_MAXVARS) am_fail("more than %d variables", AM_MAXVARS);
    char *s = malloc(len + 1); memcpy(s, name, len); s[len] = 0;
    am_varnames[am_nvars] = s;
    return am_nvars++;
}

void am_init(void) {
    ca_ctx_init(am_ca);
    fmpz_mpoly_ctx_init(am_mp, AM_MAXVARS, ORD_DEGREVLEX);
    static char unused[AM_MAXVARS][8];
    for (int i = 0; i < AM_MAXVARS; i++) { snprintf(unused[i], sizeof unused[i], "_v%d", i); am_varnames[i] = unused[i]; }
}

/* ---------------- names bound with = ---------------- */

typedef struct { char *name; Value *v; } Binding;
static Binding *binds;
static int nbinds;

static Value *lookup(const char *s, size_t len) {
    for (int i = nbinds - 1; i >= 0; i--) if (strlen(binds[i].name) == len && !strncmp(binds[i].name, s, len)) return binds[i].v;
    return NULL;
}
static void bind(const char *s, size_t len, Value *v) {
    am_pool_keep(v);
    for (int i = 0; i < nbinds; i++)
        if (strlen(binds[i].name) == len && !strncmp(binds[i].name, s, len)) { binds[i].v = v; return; }
    binds = realloc(binds, (size_t)(nbinds + 1) * sizeof *binds);
    binds[nbinds].name = malloc(len + 1); memcpy(binds[nbinds].name, s, len); binds[nbinds].name[len] = 0;
    binds[nbinds++].v = v;
}

/* ---------------- tokens ---------------- */

typedef enum { T_NUM, T_NAME, T_OP, T_END } TKind;
typedef struct { TKind k; const char *s; size_t len; int spaced; } Tok;   /* spaced: whitespace before it */
static Tok toks[4096];
static int ntok, pos;

static void lex(const char *p) {
    ntok = pos = 0;
    for (;;) {
        int sp = 0;
        while (*p && isspace((unsigned char)*p)) { p++; sp = 1; }
        if (*p == '#') break;                                  /* a comment to the end of the line */
        if (ntok >= 4095) am_fail("statement too long");
        Tok *t = &toks[ntok++];
        t->s = p; t->spaced = sp;
        if (!*p) { t->k = T_END; t->len = 0; return; }
        if (isdigit((unsigned char)*p) || (*p == '.' && isdigit((unsigned char)p[1]))) {
            while (isdigit((unsigned char)*p)) p++;
            if (*p == '.' && isdigit((unsigned char)p[1])) { p++; while (isdigit((unsigned char)*p)) p++; }
            if ((*p == 'e' || *p == 'E') && (isdigit((unsigned char)p[1]) || ((p[1] == '-' || p[1] == '+') && isdigit((unsigned char)p[2])))) {
                p += 2; while (isdigit((unsigned char)*p)) p++;
            }
            t->k = T_NUM;
        } else if (isalpha((unsigned char)*p) || *p == '_') {
            while (isalnum((unsigned char)*p) || *p == '_') p++;
            t->k = T_NAME;
        } else {
            static const char *two[] = {"**", "==", "!=", "<=", ">=", ":=", NULL};
            t->k = T_OP;
            int n = 1;
            for (int i = 0; two[i]; i++) if (!strncmp(p, two[i], 2)) n = 2;
            if (n == 1 && !strchr("+-*/^()[],=<>!", *p)) am_fail("unexpected character '%c'", *p);
            p += n;
        }
        t->len = (size_t)(p - t->s);
    }
    toks[ntok].k = T_END; ntok++;
}

static Tok *peek(void) { return &toks[pos]; }
static int at_op(const char *op) { Tok *t = peek(); return t->k == T_OP && t->len == strlen(op) && !strncmp(t->s, op, t->len); }
static int at_name(const char *w) { Tok *t = peek(); return t->k == T_NAME && t->len == strlen(w) && !strncmp(t->s, w, t->len); }
static void expect(const char *op) {
    if (!at_op(op)) {
        Tok *t = peek();
        if (t->k == T_END) am_fail("expected '%s' at the end", op);
        am_fail("expected '%s' before '%.*s'", op, (int)t->len, t->s);
    }
    pos++;
}

/* ---------------- the tree ---------------- */

typedef enum { N_NUM, N_NAME, N_CALL, N_LIST, N_NEG, N_BIN, N_FACT } NKind;
typedef struct Node Node;
struct Node { NKind k; const char *s; size_t len; char op[3]; Node **a; int n; };

static Node *mk(NKind k) { Node *n = calloc(1, sizeof *n); n->k = k; return n; }
static void add_arg(Node *n, Node *a) { n->a = realloc(n->a, (size_t)(n->n + 1) * sizeof(Node *)); n->a[n->n++] = a; }
static void free_tree(Node *n) { if (!n) return; for (int i = 0; i < n->n; i++) free_tree(n->a[i]); free(n->a); free(n); }

static Node *expr(void);
static Node *unary(void);

static Node *primary(void) {
    Tok *t = peek();
    if (t->k == T_NUM) { pos++; Node *n = mk(N_NUM); n->s = t->s; n->len = t->len; return n; }
    if (t->k == T_NAME) {
        pos++;
        if (at_op("(") && !peek()->spaced) {                  /* f(x): a call; x (y) is a product */
            pos++;
            Node *n = mk(N_CALL); n->s = t->s; n->len = t->len;
            if (!at_op(")")) for (;;) { add_arg(n, expr()); if (!at_op(",")) break; pos++; }
            expect(")");
            return n;
        }
        Node *n = mk(N_NAME); n->s = t->s; n->len = t->len; return n;
    }
    if (at_op("(")) { pos++; Node *n = expr(); expect(")"); return n; }
    if (at_op("[")) {
        pos++;
        Node *n = mk(N_LIST);
        if (!at_op("]")) for (;;) { add_arg(n, expr()); if (!at_op(",")) break; pos++; }
        expect("]");
        return n;
    }
    if (t->k == T_END) am_fail("the statement ends too early");
    am_fail("unexpected '%.*s'", (int)t->len, t->s);
}

static Node *bin(const char *op, Node *l, Node *r) { Node *n = mk(N_BIN); snprintf(n->op, sizeof n->op, "%s", op); add_arg(n, l); add_arg(n, r); return n; }

static Node *postfix(void) {
    Node *n = primary();
    while (at_op("!") && !(pos + 1 < ntok && toks[pos + 1].k == T_OP && toks[pos + 1].len == 1 && toks[pos + 1].s[0] == '=')) {
        pos++; Node *f = mk(N_FACT); add_arg(f, n); n = f;
    }
    return n;
}
static Node *power(void) {
    Node *b = postfix();
    if (at_op("^") || at_op("**")) { pos++; return bin("^", b, unary()); }
    return b;
}
static Node *unary(void) {
    if (at_op("-")) { pos++; Node *n = mk(N_NEG); add_arg(n, unary()); return n; }
    if (at_op("+")) { pos++; return unary(); }
    return power();
}
static int starts_primary(void) { Tok *t = peek(); return t->k == T_NUM || t->k == T_NAME || at_op("("); }
static Node *term(void) {
    Node *n = unary();
    for (;;) {
        if (at_op("*") ) { pos++; n = bin("*", n, unary()); }
        else if (at_op("/")) { pos++; n = bin("/", n, unary()); }
        else if (starts_primary()) n = bin("*", n, power());   /* side by side multiplies */
        else return n;
    }
}
static Node *sum(void) {
    Node *n = term();
    for (;;) {
        if (at_op("+")) { pos++; n = bin("+", n, term()); }
        else if (at_op("-")) { pos++; n = bin("-", n, term()); }
        else return n;
    }
}
static Node *expr(void) {
    Node *n = sum();
    static const char *rel[] = {"==", "!=", "<=", ">=", "=", "<", ">", NULL};
    for (int i = 0; rel[i]; i++) if (at_op(rel[i])) { pos++; return bin(rel[i], n, sum()); }
    return n;
}

/* ---------------- evaluation ---------------- */

static Value *eval(Node *n);

static Value *number(const char *s, size_t len) {
    char *t = malloc(len + 1); memcpy(t, s, len); t[len] = 0;
    char *e = strpbrk(t, "eE");
    long ex = 0;
    if (e) { ex = strtol(e + 1, NULL, 10); *e = 0; }
    char *dot = strchr(t, '.');
    long scale = 0;
    if (dot) { scale = (long)strlen(dot + 1); memmove(dot, dot + 1, strlen(dot + 1) + 1); }
    if (labs(ex) > 100000) { free(t); am_fail("exponent too large"); }
    fmpz_t num, ten; fmpz_init(num); fmpz_init(ten);
    fmpz_set_str(num, t, 10);
    fmpq_t q; fmpq_init(q);
    long p10 = ex - scale;
    fmpz_set_ui(ten, 10);
    fmpz_pow_ui(ten, ten, (ulong)labs(p10));
    if (p10 >= 0) { fmpz_mul(num, num, ten); fmpq_set_fmpz(q, num); }
    else fmpq_set_fmpz_frac(q, num, ten);
    Value *v = v_num();
    ca_set_fmpq(v->num, q, am_ca);
    fmpq_clear(q); fmpz_clear(num); fmpz_clear(ten); free(t);
    return v;
}

static Value *compare(const char *op, Value *a, Value *b) {
    if (!strcmp(op, "=")) { Value *r = v_list(2); r->kind = V_EQ; r->items[0] = a; r->items[1] = b; return r; }
    Value *d = v_sub(a, b);
    truth_t t;
    if (d->kind == V_RF) {                                     /* polynomials are equal exactly when the difference is 0 */
        if (strcmp(op, "==") && strcmp(op, "!=")) am_fail("'%s' compares numbers, not expressions with variables", op);
        t = fmpz_mpoly_q_is_zero(d->rf, am_mp) ? T_TRUE : T_FALSE;
        am_status(S_PROVED, "the difference is identically 0 as a rational function");
    } else if (d->kind == V_NUM) {
        if (!strcmp(op, "==") || !strcmp(op, "!=")) t = ca_check_is_zero(d->num, am_ca);
        else if (!strcmp(op, "<")) t = ca_check_lt(a->num, b->num, am_ca);
        else if (!strcmp(op, "<=")) t = ca_check_le(a->num, b->num, am_ca);
        else if (!strcmp(op, ">")) t = ca_check_gt(a->num, b->num, am_ca);
        else t = ca_check_ge(a->num, b->num, am_ca);
        if (t == T_UNKNOWN) am_status(S_UNKNOWN, "the exact arithmetic could not decide");
        else am_status(S_PROVED, "decided by exact arithmetic (Calcium)");
    } else am_fail("'%s' compares numbers or expressions", op);
    if (!strcmp(op, "!=") && t != T_UNKNOWN) t = t == T_TRUE ? T_FALSE : T_TRUE;
    return v_bool(t == T_TRUE ? 1 : t == T_FALSE ? 0 : -1);
}

static Value *eval(Node *n) {
    switch (n->k) {
    case N_NUM: return number(n->s, n->len);
    case N_NAME: {
        Value *b = lookup(n->s, n->len);
        if (b) return b;
        if (n->len == 2 && !strncmp(n->s, "pi", 2)) { Value *v = v_num(); ca_pi(v->num, am_ca); return v; }
        if (n->len == 1 && n->s[0] == 'E') { Value *v = v_num(); ca_one(v->num, am_ca); ca_exp(v->num, v->num, am_ca); return v; }
        if (n->len == 1 && n->s[0] == 'I') { Value *v = v_num(); ca_i(v->num, am_ca); return v; }
        if (am_builtin(n->s, n->len)) am_fail("%.*s is a function: write %.*s(...)", (int)n->len, n->s, (int)n->len, n->s);
        int i = am_var_index(n->s, n->len);                   /* an unbound name is a variable */
        Value *v = v_rf();
        fmpz_mpoly_gen(fmpz_mpoly_q_numref(v->rf), i, am_mp);
        fmpz_mpoly_one(fmpz_mpoly_q_denref(v->rf), am_mp);
        return v;
    }
    case N_CALL: {
        Builtin f = am_builtin(n->s, n->len);
        Value **args = calloc((size_t)(n->n ? n->n : 1), sizeof(Value *));
        for (int i = 0; i < n->n; i++) args[i] = eval(n->a[i]);
        if (!f) {
            if (n->n == 1 && n->len == 1 && !lookup(n->s, n->len)) {   /* x(y + 1) with a one-letter x: a product */
                Node nm = {N_NAME, n->s, n->len, "", NULL, 0};
                Value *r = v_mul(eval(&nm), args[0]);
                free(args);
                return r;
            }
            free(args);
            am_fail("unknown function %.*s", (int)n->len, n->s);
        }
        Value *r = f(args, n->n);
        free(args);
        return r;
    }
    case N_LIST: {
        Value *v = v_list(n->n);
        for (int i = 0; i < n->n; i++) v->items[i] = eval(n->a[i]);
        return v;
    }
    case N_NEG: return v_neg(eval(n->a[0]));
    case N_FACT: {
        Value *a = eval(n->a[0]);
        fmpq_t q; fmpq_init(q);
        if (!v_is_rational(a, q) || !fmpz_is_one(fmpq_denref(q)) || fmpz_sgn(fmpq_numref(q)) < 0) am_fail("n! needs a whole number n >= 0");
        if (fmpz_cmp_ui(fmpq_numref(q), 1000000) > 0) am_fail("n! for n above 10^6: too large");
        Value *r = v_num();
        fmpz_t f; fmpz_init(f);
        fmpz_fac_ui(f, fmpz_get_ui(fmpq_numref(q)));
        ca_set_fmpz(r->num, f, am_ca);
        fmpz_clear(f); fmpq_clear(q);
        return r;
    }
    case N_BIN: {
        Value *a = eval(n->a[0]), *b = eval(n->a[1]);
        switch (n->op[0]) {
        case '+': return v_add(a, b);
        case '-': return v_sub(a, b);
        case '*': return v_mul(a, b);
        case '/': return v_div(a, b);
        case '^': return v_pow(a, b);
        default: return compare(n->op, a, b);
        }
    }
    }
    am_fail("internal: unknown node");
}

/* the status of an answer that no function labelled: exact arithmetic, or Calcium's exact numbers */
static void default_status(const Value *v) {
    if (v->kind == V_NUM || v->kind == V_RF) am_status(S_EXACT, "exact arithmetic");
    if (v->kind == V_LIST || v->kind == V_EQ) for (int i = 0; i < v->n; i++) default_status(v->items[i]);
}

char *am_run(const char *line, int *failed) {
    *failed = 0;
    am_show = 0;
    am_account_reset();
    Node *volatile tree = NULL;
    if (setjmp(am_on_error)) {
        *failed = 1;
        free_tree(tree);
        char *out = am_render(line, NULL, err_msg);
        am_pool_release();
        return out;
    }
    lex(line);
    if (peek()->k == T_END) return NULL;
    if (at_name("show")) { pos++; am_show = 1; }
    const char *name = NULL; size_t nlen = 0;
    if (peek()->k == T_NAME && toks[pos + 1].k == T_OP && toks[pos + 1].len == 1 && toks[pos + 1].s[0] == '=') {
        name = peek()->s; nlen = peek()->len; pos += 2;        /* NAME = expr names a value */
    } else if (peek()->k == T_NAME && toks[pos + 1].k == T_OP && toks[pos + 1].len == 2 && !strncmp(toks[pos + 1].s, ":=", 2)) {
        name = peek()->s; nlen = peek()->len; pos += 2;
    }
    if (name && am_builtin(name, nlen)) am_fail("%.*s is a built-in function and cannot be renamed", (int)nlen, name);
    tree = expr();
    if (peek()->k != T_END) am_fail("unexpected '%.*s'", (int)peek()->len, peek()->s);
    Value *v = eval(tree);
    free_tree(tree); tree = NULL;
    if (!am_status_set()) default_status(v);
    char *text = v_str_of(v);
    if (name) {
        bind(name, nlen, v);
        char *t2 = malloc(strlen(text) + nlen + 4);
        sprintf(t2, "%.*s = %s", (int)nlen, name, text);
        free(text); text = t2;
    }
    char *out = am_render(line, text, NULL);
    free(text);
    am_pool_release();
    return out;
}
