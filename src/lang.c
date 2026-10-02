/* The language: notation agents already write, read into a tree and evaluated.
 *
 *   statement  := ["show"] ( definition | NAME "=" expr | expr )
 *   definition := NAME "(" patterns ")" ":=" expr ["if" expr]          also "=" when the patterns are plain names
 *   expr       := conj { "or" conj }
 *   conj       := neg { "and" neg }
 *   neg        := "not" neg | rel
 *   rel        := sum [ ("=" | "==" | "!=" | "<" | "<=" | ">" | ">=") sum ]  "=" makes an equation, the others a test
 *   sum        := term { ("+" | "-") term }
 *   term       := unary { ("*" | "/") unary | primary }                      2x, 3(x + 1), (x + 1)(x - 1)
 *   unary      := "-" unary | power
 *   power      := postfix [ ("^" | "**") unary ]
 *   postfix    := primary { "!" | "[" expr "]" }                          a[1] is the first element
 *   primary    := NUMBER | NAME | NAME "(" [args] ")" | "(" expr ")" | "[" [args] "]"
 *
 * Names are whole words (xy is one variable). A name that is not bound is a variable; a call to a name that is
 * neither defined nor built in stays as a symbolic function term, f(x). pi, E and I are numbers. Decimals are
 * read exactly (0.1 is 1/10).
 *
 * Functions are defined by rules. A rule's patterns are names (match anything), numbers (match that number),
 * calls such as sin(u) (match a function term with that head and bind its arguments), or lists. Rules are tried
 * in the order written; the first whose patterns match and whose condition holds gives the value. A built-in
 * function is tried after the rules for its name, so the library can extend it (diff of sin(u) is a rule). */
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
        if (*p == '#') { while (*p) p++; }                     /* a comment to the end of the line */
        if (ntok >= 4094) am_fail("statement too long");
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
}

static Tok *peek(void) { return &toks[pos]; }
static int is_op(const Tok *t, const char *op) { return t->k == T_OP && t->len == strlen(op) && !strncmp(t->s, op, t->len); }
static int at_op(const char *op) { return is_op(peek(), op); }
static int at_word(const char *w) { Tok *t = peek(); return t->k == T_NAME && t->len == strlen(w) && !strncmp(t->s, w, t->len); }
static void expect(const char *op) {
    if (!at_op(op)) {
        Tok *t = peek();
        if (t->k == T_END) am_fail("expected '%s' at the end", op);
        am_fail("expected '%s' before '%.*s'", op, (int)t->len, t->s);
    }
    pos++;
}

/* ---------------- the tree ---------------- */

typedef enum { N_NUM, N_NAME, N_CALL, N_LIST, N_NEG, N_BIN, N_FACT, N_INDEX, N_AND, N_OR, N_NOT } NKind;
typedef struct Node Node;
struct Node { NKind k; char *s; size_t len; char op[3]; Node **a; int n; };

static Node *mk(NKind k) { Node *n = calloc(1, sizeof *n); n->k = k; return n; }
static Node *mk_tok(NKind k, const Tok *t) { Node *n = mk(k); n->s = strndup(t->s, t->len); n->len = t->len; return n; }
static void add_arg(Node *n, Node *a) { n->a = realloc(n->a, (size_t)(n->n + 1) * sizeof(Node *)); n->a[n->n++] = a; }
static void free_tree(Node *n) { if (!n) return; for (int i = 0; i < n->n; i++) free_tree(n->a[i]); free(n->a); free(n->s); free(n); }

static Node *expr(void);
static Node *unary(void);

static Node *primary(void) {
    Tok *t = peek();
    if (t->k == T_NUM) { pos++; return mk_tok(N_NUM, t); }
    if (t->k == T_NAME) {
        pos++;
        if (at_op("(") && !peek()->spaced) {                  /* f(x): a call; x (y) is a product */
            pos++;
            Node *n = mk_tok(N_CALL, t);
            if (!at_op(")")) for (;;) { add_arg(n, expr()); if (!at_op(",")) break; pos++; }
            expect(")");
            return n;
        }
        return mk_tok(N_NAME, t);
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
    for (;;) {
        if (at_op("!") && !is_op(&toks[pos + 1], "=")) { pos++; Node *f = mk(N_FACT); add_arg(f, n); n = f; }
        else if (at_op("[") && !peek()->spaced) { pos++; Node *f = mk(N_INDEX); add_arg(f, n); add_arg(f, expr()); expect("]"); n = f; }
        else return n;
    }
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
static int starts_primary(void) {
    Tok *t = peek();
    if (t->k == T_NAME && (at_word("and") || at_word("or") || at_word("if") || at_word("not"))) return 0;
    return t->k == T_NUM || t->k == T_NAME || at_op("(");
}
static Node *term(void) {
    Node *n = unary();
    for (;;) {
        if (at_op("*")) { pos++; n = bin("*", n, unary()); }
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
static Node *rel(void) {
    Node *n = sum();
    static const char *ops[] = {"==", "!=", "<=", ">=", "=", "<", ">", NULL};
    for (int i = 0; ops[i]; i++) if (at_op(ops[i])) { pos++; return bin(ops[i], n, sum()); }
    return n;
}
static Node *neg(void) {
    if (at_word("not")) { pos++; Node *n = mk(N_NOT); add_arg(n, neg()); return n; }
    return rel();
}
static Node *conjunction(void) {
    Node *n = neg();
    while (at_word("and")) { pos++; Node *a = mk(N_AND); add_arg(a, n); add_arg(a, neg()); n = a; }
    return n;
}
static Node *expr(void) {
    Node *n = conjunction();
    while (at_word("or")) { pos++; Node *a = mk(N_OR); add_arg(a, n); add_arg(a, conjunction()); n = a; }
    return n;
}

/* ---------------- names, rules and local scope ---------------- */

typedef struct { char *name; Value *v; } Binding;
static Binding *globals;
static int nglobals;

typedef struct Rule { char *name; Node **pat; int np; Node *body, *cond; char *src; } Rule;
static Rule *rules;
static int nrules;

#define MAXLOCAL 64
typedef struct { const char *name[MAXLOCAL]; Value *v[MAXLOCAL]; int n; } Frame;
static Frame *frame;              /* the innermost rule being evaluated, or NULL at top level */
static int depth;

static Value *lookup(const char *s) {
    if (frame) for (int i = frame->n - 1; i >= 0; i--) if (!strcmp(frame->name[i], s)) return frame->v[i];
    for (int i = nglobals - 1; i >= 0; i--) if (!strcmp(globals[i].name, s)) return globals[i].v;
    return NULL;
}
static void bind_global(const char *s, Value *v) {
    am_pool_keep(v);
    for (int i = 0; i < nglobals; i++) if (!strcmp(globals[i].name, s)) { globals[i].v = v; return; }
    globals = realloc(globals, (size_t)(nglobals + 1) * sizeof *globals);
    globals[nglobals].name = strdup(s);
    globals[nglobals++].v = v;
}
int am_rule_count(void) { return nrules; }
const char *am_rule_src(int i, const char **name) { *name = rules[i].name; return rules[i].src; }

static int has_rules(const char *name) { for (int i = 0; i < nrules; i++) if (!strcmp(rules[i].name, name)) return 1; return 0; }

static int same_tree(const Node *a, const Node *b) {
    if (a->k != b->k || a->n != b->n || strcmp(a->op, b->op)) return 0;
    if ((a->s || b->s) && (!a->s || !b->s || strcmp(a->s, b->s))) return 0;
    for (int i = 0; i < a->n; i++) if (!same_tree(a->a[i], b->a[i])) return 0;
    return 1;
}

static void add_rule(const char *name, Node **pat, int np, Node *body, Node *cond, const char *src) {
    for (int i = 0; i < nrules; i++) {                         /* the same patterns again: the new rule replaces it */
        Rule *r = &rules[i];
        if (strcmp(r->name, name) || r->np != np || (r->cond != NULL) != (cond != NULL)) continue;
        int same = 1;
        for (int j = 0; j < np && same; j++) same = same_tree(r->pat[j], pat[j]);
        if (same && cond) same = same_tree(r->cond, cond);
        if (same) { r->body = body; r->cond = cond; free(r->src); r->src = strdup(src); return; }
    }
    rules = realloc(rules, (size_t)(nrules + 1) * sizeof *rules);
    rules[nrules].name = strdup(name); rules[nrules].pat = pat; rules[nrules].np = np;
    rules[nrules].body = body; rules[nrules].cond = cond; rules[nrules].src = strdup(src);
    nrules++;
}

/* ---------------- evaluation ---------------- */

static Value *eval(Node *n);
static int library_loading;
static int in_condition;          /* inside a rule's condition or if/and/or/not: a decided test does not label the answer */

static Value *number(const char *s, size_t len) {
    char *t = strndup(s, len);
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

/* a value with its function terms evaluated again: sqrt(2) as a generator becomes the number, sin(1) a number */
#define reevaluate am_reevaluate

static int truth_of(Value *v, const char *what) {
    if (v->kind != V_BOOL) am_fail("%s must be true or false", what);
    if (v->truth < 0) am_fail("%s could not be decided", what);
    return v->truth;
}

static Value *compare(const char *op, Value *a, Value *b) {
    if (!strcmp(op, "=")) { Value *r = v_list(2); r->kind = V_EQ; r->items[0] = a; r->items[1] = b; return r; }
    Value *d = v_sub(a, b);
    if (d->kind == V_RF) d = reevaluate(d);
    truth_t t;
    if (d->kind == V_RF) {
        if (strcmp(op, "==") && strcmp(op, "!=")) am_fail("'%s' compares numbers, not expressions with variables", op);
        int kernels = 0;
        int used[AM_MAXVARS] = {0};
        fmpz_mpoly_q_used_vars(used, d->rf, am_mp);
        for (int i = 0; i < am_nvars; i++) if (used[i] && am_vars[i].kernel) kernels = 1;
        if (fmpz_mpoly_q_is_zero(d->rf, am_mp)) { t = T_TRUE; if (!in_condition) am_status(S_PROVED, "the difference is identically 0"); }
        else if (!kernels) { t = T_FALSE; if (!in_condition) am_status(S_PROVED, "the difference is a nonzero rational function"); }
        else {
            char where[256];
            int z = am_zero_test(d, where, sizeof where);
            if (z == 1) { t = T_TRUE; if (!in_condition) am_status(S_PROVED, "the difference reduces to 0 (using tan = sin/cos, sin^2 + cos^2 = 1, sqrt(u)^2 = u)"); }
            else if (z == 0) { t = T_FALSE; if (!in_condition) am_status(S_PROVED, "the two sides differ at %s (certified evaluation)", where); }
            else if (z == 2) { t = T_TRUE; if (!in_condition) am_status(S_PROBABLE, "equal at 5 random points (certified evaluation), not proved symbolically"); }
            else { t = T_UNKNOWN; am_status(S_UNKNOWN, "the difference involves function terms that could not be decided"); }
        }
    } else if (d->kind == V_NUM) {
        if (a->kind != V_NUM) a = reevaluate(a);
        if (b->kind != V_NUM) b = reevaluate(b);
        if (!strcmp(op, "==") || !strcmp(op, "!=")) t = ca_check_is_zero(d->num, am_ca);
        else if (a->kind != V_NUM || b->kind != V_NUM) am_fail("'%s' compares numbers", op);
        else if (!strcmp(op, "<")) t = ca_check_lt(a->num, b->num, am_ca);
        else if (!strcmp(op, "<=")) t = ca_check_le(a->num, b->num, am_ca);
        else if (!strcmp(op, ">")) t = ca_check_gt(a->num, b->num, am_ca);
        else t = ca_check_ge(a->num, b->num, am_ca);
        if (t == T_UNKNOWN) am_status(S_UNKNOWN, "the exact arithmetic could not decide");
        else if (!in_condition) am_status(S_PROVED, "decided by exact arithmetic (Calcium)");
    } else if (d->kind == V_LIST) {                           /* lists: equal when every element is */
        t = T_TRUE;
        for (int i = 0; i < d->n; i++) {
            Value *z = v_num();
            Value *c = compare("==", d->items[i], z);
            if (c->truth == 0) { t = T_FALSE; break; }
            if (c->truth < 0) t = T_UNKNOWN;
        }
        if (strcmp(op, "==") && strcmp(op, "!=")) am_fail("'%s' compares numbers", op);
    } else am_fail("'%s' compares numbers or expressions", op);
    if (!strcmp(op, "!=") && t != T_UNKNOWN) t = t == T_TRUE ? T_FALSE : T_TRUE;
    return v_bool(t == T_TRUE ? 1 : t == T_FALSE ? 0 : -1);
}

/* a == b exactly, without touching the statement's status */
static int equal_quiet(Value *a, Value *b) {
    if (a->kind != b->kind && !((a->kind == V_NUM || a->kind == V_RF) && (b->kind == V_NUM || b->kind == V_RF))) return 0;
    if (a->kind == V_LIST || a->kind == V_EQ) {
        if (a->n != b->n) return 0;
        for (int i = 0; i < a->n; i++) if (!equal_quiet(a->items[i], b->items[i])) return 0;
        return 1;
    }
    if (a->kind == V_BOOL) return a->truth == b->truth;
    if (a->kind == V_STR) return !strcmp(a->str, b->str);
    Value *d = v_sub(a, b);
    if (d->kind == V_NUM) return ca_check_is_zero(d->num, am_ca) == T_TRUE;
    return fmpz_mpoly_q_is_zero(d->rf, am_mp);
}

static int match(Node *p, Value *v, Frame *f);

/* a*b*...: each pattern factor that is not a plain name takes one factor of the monomial v (a generator, or a
 * generator to a power); a single plain name, if there is one, takes everything left, numbers included */
static void flatten_product(Node *p, Node **out, int *n) {
    if (p->k == N_BIN && p->op[0] == '*' && !p->op[1]) { flatten_product(p->a[0], out, n); flatten_product(p->a[1], out, n); }
    else if (*n < 8) out[(*n)++] = p;
}
static int match_product(Node *p, Value *v, Frame *f) {
    Node *pf[8]; int np = 0;
    flatten_product(p, pf, &np);
    if (v->kind != V_RF || !fmpz_mpoly_is_one(fmpz_mpoly_q_denref(v->rf), am_mp)) return 0;
    const fmpz_mpoly_struct *N = fmpz_mpoly_q_numref(v->rf);
    if (fmpz_mpoly_length(N, am_mp) != 1) return 0;
    ulong ex[AM_MAXVARS]; fmpz_mpoly_get_term_exp_ui(ex, N, 0, am_mp);
    fmpz_t c; fmpz_init(c); fmpz_mpoly_get_term_coeff_fmpz(c, N, 0, am_mp);
    int gens[AM_MAXVARS], ng = 0;
    for (int i = 0; i < am_nvars; i++) if (ex[i]) gens[ng++] = i;
    int rest = -1, nfix = 0;
    for (int i = 0; i < np; i++) { if (pf[i]->k == N_NAME && rest < 0) rest = i; else nfix++; }
    if (nfix > ng) { fmpz_clear(c); return 0; }
    /* try every assignment of the fixed pattern factors to distinct generators */
    int choice[8], ok = 0;
    for (int i = 0; i < 8; i++) choice[i] = 0;
    long total = 1;
    for (int i = 0; i < nfix; i++) total *= ng;
    for (long code = 0; code < total && !ok; code++) {
        long cc = code; int usedg[AM_MAXVARS] = {0}, distinct = 1;
        for (int i = 0; i < nfix; i++) { choice[i] = gens[cc % ng]; cc /= ng; if (usedg[choice[i]]++) distinct = 0; }
        if (!distinct) continue;
        Frame save = *f;
        int good = 1, k = 0;
        ulong left[AM_MAXVARS]; memcpy(left, ex, sizeof left);
        for (int i = 0; i < np && good; i++) {
            if (i == rest) continue;
            int g = choice[k++];
            Value *e = v_num(); ca_set_ui(e->num, ex[g], am_ca);
            Value *piece = v_pow(am_gen(g), e);
            good = match(pf[i], piece, f);
            left[g] = 0;
        }
        if (good) {
            Value *r = v_num(); ca_set_fmpz(r->num, c, am_ca);
            for (int i = 0; i < am_nvars; i++) if (left[i]) { Value *e = v_num(); ca_set_ui(e->num, left[i], am_ca); r = v_mul(r, v_pow(am_gen(i), e)); }
            if (rest >= 0) good = match(pf[rest], r, f);
            else good = r->kind == V_NUM && ca_check_is_one(r->num, am_ca) == T_TRUE;
        }
        if (good) ok = 1; else *f = save;
    }
    fmpz_clear(c);
    return ok;
}

/* does pattern p match v? binds names into f */
static int match(Node *p, Value *v, Frame *f) {
    switch (p->k) {
    case N_NAME: {
        for (int i = 0; i < f->n; i++)
            if (!strcmp(f->name[i], p->s)) return equal_quiet(f->v[i], v);
        if (f->n == MAXLOCAL) am_fail("too many names in a rule");
        f->name[f->n] = p->s; f->v[f->n++] = v;
        return 1;
    }
    case N_NUM: case N_NEG: {
        Frame *save = frame; frame = NULL;
        Value *w = eval(p);
        frame = save;
        fmpq_t a, b; fmpq_init(a); fmpq_init(b);
        int ok = v_is_rational(v, a) && v_is_rational(w, b) && fmpq_equal(a, b);
        fmpq_clear(a); fmpq_clear(b);
        return ok;
    }
    case N_CALL: {                                            /* sin(u) matches the function term sin(...) */
        int g = am_gen_of(v);
        if (g < 0 || !am_vars[g].head || strcmp(am_vars[g].head, p->s) || am_vars[g].nargs != p->n) return 0;
        for (int i = 0; i < p->n; i++) if (!match(p->a[i], am_vars[g].args[i], f)) return 0;
        return 1;
    }
    case N_BIN:
        if (p->op[0] == '^' && !p->op[1]) {                   /* u^n matches a single generator to a power */
            if (v->kind != V_RF || !fmpz_mpoly_is_one(fmpz_mpoly_q_denref(v->rf), am_mp)) return 0;
            const fmpz_mpoly_struct *N = fmpz_mpoly_q_numref(v->rf);
            if (fmpz_mpoly_length(N, am_mp) != 1) return 0;
            fmpz_t c; fmpz_init(c); fmpz_mpoly_get_term_coeff_fmpz(c, N, 0, am_mp);
            int one = fmpz_is_one(c); fmpz_clear(c);
            if (!one) return 0;
            ulong ex[AM_MAXVARS]; fmpz_mpoly_get_term_exp_ui(ex, N, 0, am_mp);
            int g = -1, cnt = 0;
            for (int i = 0; i < am_nvars; i++) if (ex[i]) { g = i; cnt++; }
            if (cnt != 1 || ex[g] < 2) return 0;
            Value *e = v_num(); ca_set_ui(e->num, ex[g], am_ca);
            return match(p->a[0], am_gen(g), f) && match(p->a[1], e, f);
        }
        if (p->op[0] == '*' && !p->op[1]) return match_product(p, v, f);
        return 0;
    case N_LIST:
        if (v->kind != V_LIST || v->n != p->n) return 0;
        for (int i = 0; i < p->n; i++) if (!match(p->a[i], v->items[i], f)) return 0;
        return 1;
    default:
        am_fail("a rule's patterns are names, numbers, calls such as sin(u), or lists");
    }
}

/* a call to a name with no rules and no built-in: said in the facts, so a misspelled name is noticed */
static void note_undefined(const char *name) {
    if (library_loading) return;
    char *js = am_json_str(name);
    am_fact("undefined_function", "%s", js);
    free(js);
    const char *s = am_suggest(name);
    if (s) { js = am_json_str(s); am_fact("did_you_mean", "%s", js); free(js); }
}

Value *am_call(const char *name, Value **args, int n) {
    for (int r = 0; r < nrules; r++) {
        Rule *R = &rules[r];
        if (strcmp(R->name, name) || R->np != n) continue;
        Frame *f = calloc(1, sizeof *f);
        int ok = 1;
        for (int i = 0; i < n && ok; i++) ok = match(R->pat[i], args[i], f);
        if (ok) {
            if (++depth > 2000) { depth = 0; free(f); am_fail("%s: more than 2000 nested calls", name); }
            Frame *save = frame; frame = f;
            if (R->cond) {
                in_condition++;
                Value *c = eval(R->cond);
                in_condition--;
                if (c->kind == V_BOOL && c->truth < 0) am_fail("the condition of the rule %s could not be decided", R->src);
                ok = c->kind == V_BOOL && c->truth == 1;
            }
            if (ok) {
                if (!library_loading) am_work("%s", R->src);
                Value *v = eval(R->body);
                frame = save; depth--; free(f);
                return v;
            }
            frame = save; depth--;
        }
        free(f);
    }
    Builtin b = am_builtin(name, strlen(name));
    if (b) return b(args, n);
    if (has_rules(name)) {                                    /* rules exist, none applies: the call stays as it is */
        if (!library_loading && strcmp(name, "antiderivative")) { char *js = am_json_str(name); am_fact("unevaluated", "%s", js); free(js); }
        return am_kernel_value(name, args, n);
    }
    note_undefined(name);
    return am_kernel_value(name, args, n);                   /* an undefined function stays symbolic: f(x) */
}

/* re-evaluate the generators of a rational function: numbers back to numbers, function terms by their rules */
Value *am_reevaluate(Value *v) {
    if (v->kind == V_LIST || v->kind == V_EQ) {
        Value *r = v_list(v->n); r->kind = v->kind;
        for (int i = 0; i < v->n; i++) r->items[i] = reevaluate(v->items[i]);
        return r;
    }
    if (v->kind != V_RF) return v;
    int used[AM_MAXVARS] = {0}, any = 0;
    fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
    for (int i = 0; i < am_nvars; i++) if (used[i] && am_vars[i].kernel) any = 1;
    if (!any) return v;
    Value *val[AM_MAXVARS];
    for (int i = 0; i < am_nvars; i++) {
        val[i] = am_gen(i);
        if (!used[i] || !am_vars[i].kernel) continue;
        if (am_vars[i].numval) val[i] = am_vars[i].numval;
        else {
            Value **a = malloc((size_t)(am_vars[i].nargs ? am_vars[i].nargs : 1) * sizeof *a);
            for (int j = 0; j < am_vars[i].nargs; j++) a[j] = reevaluate(am_vars[i].args[j]);
            val[i] = am_call(am_vars[i].head, a, am_vars[i].nargs);
            free(a);
        }
    }
    return am_subs_rf(v, val);
}

static Value *eval_call(Node *n) {
    /* special forms: their arguments are not all evaluated first */
    if (!strcmp(n->s, "if")) {
        if (n->n != 3) am_fail("if(condition, then, else) takes three arguments");
        in_condition++;
        int t = truth_of(eval(n->a[0]), "the condition of if");
        in_condition--;
        return t ? eval(n->a[1]) : eval(n->a[2]);
    }
    if (!strcmp(n->s, "help")) {                              /* help() or help(factor): the reference */
        if (n->n > 1 || (n->n == 1 && n->a[0]->k != N_NAME && n->a[0]->k != N_CALL)) am_fail("help() or help(name)");
        char *r = am_reference(n->n ? n->a[0]->s : NULL);
        Value *v = v_str(r);
        free(r);
        return v;
    }
    if (!strcmp(n->s, "map")) {
        if (n->n != 2 || n->a[0]->k != N_NAME) am_fail("map(f, list) takes a function name and a list");
        Value *l = eval(n->a[1]);
        if (l->kind != V_LIST) am_fail("map needs a list");
        Value *r = v_list(l->n);
        for (int i = 0; i < l->n; i++) r->items[i] = am_call(n->a[0]->s, &l->items[i], 1);
        return r;
    }
    Value **args = calloc((size_t)(n->n ? n->n : 1), sizeof(Value *));
    for (int i = 0; i < n->n; i++) args[i] = eval(n->a[i]);
    if (n->n == 1 && !has_rules(n->s) && !am_builtin(n->s, n->len)) {   /* x(x + 1) where x is a variable or a value */
        Value *b = lookup(n->s);
        int plain = 0;
        for (int i = 0; i < am_nvars && !b; i++) if (!am_vars[i].kernel && !strcmp(am_varnames[i], n->s)) plain = 1;
        if (b || plain) { Value *r = v_mul(b ? b : am_gen(am_var_index(n->s, n->len)), args[0]); free(args); return r; }
    }
    Value *r = am_call(n->s, args, n->n);
    free(args);
    return r;
}

static Value *eval(Node *n) {
    switch (n->k) {
    case N_NUM: return number(n->s, n->len);
    case N_NAME: {
        Value *b = lookup(n->s);
        if (b) return b;
        if (!strcmp(n->s, "pi")) { Value *v = v_num(); ca_pi(v->num, am_ca); return v; }
        if (!strcmp(n->s, "E")) { Value *v = v_num(); ca_one(v->num, am_ca); ca_exp(v->num, v->num, am_ca); return v; }
        if (!strcmp(n->s, "I")) { Value *v = v_num(); ca_i(v->num, am_ca); return v; }
        if (!strcmp(n->s, "true")) return v_bool(1);
        if (!strcmp(n->s, "false")) return v_bool(0);
        if (am_builtin(n->s, n->len) || has_rules(n->s)) am_fail("%s is a function: write %s(...)", n->s, n->s);
        return am_gen(am_var_index(n->s, n->len));            /* an unbound name is a variable */
    }
    case N_CALL: return eval_call(n);
    case N_LIST: {
        Value *v = v_list(n->n);
        for (int i = 0; i < n->n; i++) v->items[i] = eval(n->a[i]);
        return v;
    }
    case N_INDEX: {
        Value *l = eval(n->a[0]), *i = eval(n->a[1]);
        fmpq_t q; fmpq_init(q);
        if (l->kind != V_LIST && l->kind != V_EQ) am_fail("only a list can be indexed");
        if (!v_is_rational(i, q) || !fmpz_is_one(fmpq_denref(q)) || fmpz_cmp_si(fmpq_numref(q), 1) < 0 || fmpz_cmp_si(fmpq_numref(q), l->n) > 0)
            am_fail("index out of range: the list has %d elements (the first is [1])", l->n);
        slong k = fmpz_get_si(fmpq_numref(q));
        fmpq_clear(q);
        return l->items[k - 1];
    }
    case N_NEG: return v_neg(eval(n->a[0]));
    case N_NOT: { in_condition++; Value *a = eval(n->a[0]); in_condition--; return v_bool(a->kind == V_BOOL && a->truth >= 0 ? !a->truth : (truth_of(a, "not's argument"), -1)); }
    case N_AND: case N_OR: {
        in_condition++;
        int want = n->k == N_OR, t = truth_of(eval(n->a[0]), "a side of and/or");
        if (t != want) t = truth_of(eval(n->a[1]), "a side of and/or");
        in_condition--;
        if (!in_condition) am_status(S_PROVED, "decided by exact arithmetic");
        return v_bool(t);
    }
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

/* the status of an answer that no function labelled: exact arithmetic */
static void default_status(const Value *v) {
    if (v->kind == V_NUM || v->kind == V_RF) am_status(S_EXACT, "exact arithmetic");
    if (v->kind == V_LIST || v->kind == V_EQ) for (int i = 0; i < v->n; i++) default_status(v->items[i]);
}

/* NAME ( ... ) followed by := (or by = with plain-name patterns): a definition */
static int definition_ahead(int *assign_at) {
    if (peek()->k != T_NAME || !is_op(&toks[pos + 1], "(") || toks[pos + 1].spaced) return 0;
    int d = 0, i = pos + 1;
    for (; toks[i].k != T_END; i++) {
        if (is_op(&toks[i], "(")) d++;
        else if (is_op(&toks[i], ")") && --d == 0) break;
    }
    if (toks[i].k == T_END) return 0;
    if (is_op(&toks[i + 1], ":=")) { *assign_at = i + 1; return 1; }
    if (is_op(&toks[i + 1], "=")) {                           /* f(x, y) = ...: only with plain names inside */
        for (int j = pos + 2; j < i; j++) if (!(toks[j].k == T_NAME || is_op(&toks[j], ","))) return 0;
        if (am_builtin(toks[pos].s, toks[pos].len)) return 0;
        *assign_at = i + 1; return 1;
    }
    return 0;
}

static char *run_statement(const char *line, Node *volatile *tree) {
    lex(line);
    if (peek()->k == T_END) return NULL;
    if (at_word("show")) { pos++; am_show = 1; }
    int at;
    if (definition_ahead(&at)) {                              /* f(patterns) := body [if condition] */
        Tok name = *peek();
        pos += 2;
        Node **pat = NULL; int np = 0;
        if (!at_op(")")) for (;;) { pat = realloc(pat, (size_t)(np + 1) * sizeof *pat); pat[np++] = expr(); if (!at_op(",")) break; pos++; }
        expect(")");
        pos = at + 1;
        Node *body = expr(), *cond = NULL;
        if (at_word("if")) { pos++; cond = expr(); }
        if (peek()->k != T_END) am_fail("unexpected '%.*s'", (int)peek()->len, peek()->s);
        char *nm = strndup(name.s, name.len);
        const char *src = line;
        while (*src == ' ') src++;
        char *s = strdup(src);
        size_t L = strlen(s);
        while (L && (s[L - 1] == '\n' || s[L - 1] == '\r')) s[--L] = 0;
        add_rule(nm, pat, np, body, cond, s);
        char *out = malloc(strlen(s) + 32);
        sprintf(out, "defined %s", s);
        free(nm); free(s);
        return out;
    }
    const char *name = NULL; size_t nlen = 0;
    if (peek()->k == T_NAME && (is_op(&toks[pos + 1], "=") || is_op(&toks[pos + 1], ":="))) {
        name = peek()->s; nlen = peek()->len; pos += 2;        /* NAME = expr names a value */
        if (am_builtin(name, nlen)) am_fail("%.*s is a built-in function and cannot be renamed", (int)nlen, name);
    }
    *tree = expr();
    if (peek()->k != T_END) am_fail("unexpected '%.*s'", (int)peek()->len, peek()->s);
    Value *v = eval(*tree);
    if (!am_status_set()) default_status(v);
    char *text = v_str_of(v);
    if (name) {
        char *nm = strndup(name, nlen);
        bind_global(nm, v);
        char *t2 = malloc(strlen(text) + nlen + 4);
        sprintf(t2, "%s = %s", nm, text);
        free(nm); free(text); text = t2;
    }
    return text;
}

char *am_run(const char *line, int *failed) {
    *failed = 0;
    am_show = 0;
    frame = NULL; depth = 0; in_condition = 0;
    am_account_reset();
    Node *volatile tree = NULL;
    if (setjmp(am_on_error)) {
        *failed = 1;
        free_tree(tree);
        frame = NULL; depth = 0;
        char *out = am_render(line, NULL, err_msg);
        am_pool_release();
        return out;
    }
    char *text = run_statement(line, &tree);
    free_tree(tree);
    if (!text) { am_pool_release(); return NULL; }
    char *out = am_render(line, text, NULL);
    free(text);
    am_pool_release();
    return out;
}

/* the library, written in the language and compiled into the program */
extern const char *am_lib_names[], *am_lib_texts[];
void am_load_library(void) {
    library_loading = 1;
    for (int i = 0; am_lib_names[i]; i++) {
        const char *p = am_lib_texts[i];
        int lineno = 0;
        while (*p) {
            const char *e = strchr(p, '\n');
            size_t n = e ? (size_t)(e - p) : strlen(p);
            char *line = strndup(p, n);
            lineno++;
            int failed;
            char *out = am_run(line, &failed);
            if (failed) { fprintf(stderr, "amath: library %s line %d: %s\n", am_lib_names[i], lineno, out); exit(2); }
            free(out); free(line);
            p += n + (e ? 1 : 0);
        }
    }
    library_loading = 0;
}
