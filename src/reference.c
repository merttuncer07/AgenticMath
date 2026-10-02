/* The language reference, written for an agent: the notation, what the statuses mean, every function. Also the
 * nearest known name to a misspelled one. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char *GUIDE =
    "AgenticMath: exact and certified mathematics. One statement per line; definitions persist.\n"
    "\n"
    "Notation: x^2 or x**2, 2x, 3(x + 1), sqrt, pi, E, I, lists [a, b], a[1] (first element), equations x^2 = 2,\n"
    "tests == != < <= > >=, and or not, names a = 5. Decimals are exact (0.1 is 1/10). Multi-letter names are one\n"
    "variable (xy). A call to an unknown name stays symbolic: f(x).\n"
    "\n"
    "Definitions are rules: f(x) := x^2 + 1;  fact(0) := 1;  fact(n) := n*fact(n - 1) if n > 0;\n"
    "patterns: g(exp(u)) := u.  Rules are tried in order; a rule for a built-in name extends it.\n"
    "if(c, a, b), map(f, list). Prefix a statement with 'show' to see every rule and step applied.\n"
    "\n"
    "Every answer has a status: proved (a complete argument was carried out), exact (exact arithmetic),\n"
    "certified (every digit guaranteed), probable (rests on a randomized step), numeric (no guarantee),\n"
    "unknown (could not be decided). An answer is only as sure as its weakest step. Facts are things the\n"
    "computation produced anyway (degrees, multiplicities, numbers of roots or solutions).\n";

int am_rule_count(void);
const char *am_rule_src(int i, const char **name);

typedef struct { char *s; size_t n, cap; } Str;
static void sput(Str *b, const char *s) {
    size_t n = strlen(s);
    if (b->n + n + 1 > b->cap) { b->cap = (b->n + n + 1) * 2 + 256; b->s = realloc(b->s, b->cap); }
    memcpy(b->s + b->n, s, n + 1);
    b->n += n;
}

char *am_reference(const char *topic) {
    Str b = {0, 0, 0};
    sput(&b, "");
    const char *name, *sig, *doc;
    if (!topic || !*topic) {
        sput(&b, GUIDE);
        sput(&b, "\nFunctions:\n");
        for (int i = 0; am_builtin_doc(i, &name, &sig, &doc); i++) { sput(&b, "  "); sput(&b, sig); sput(&b, "  -- "); sput(&b, doc); sput(&b, "\n"); }
        sput(&b, "\nLibrary rules (written in the language):\n");
        for (int i = 0; i < am_rule_count(); i++) { const char *n; sput(&b, "  "); sput(&b, am_rule_src(i, &n)); sput(&b, "\n"); }
        return b.s;
    }
    int found = 0;
    for (int i = 0; am_builtin_doc(i, &name, &sig, &doc); i++)
        if (!strcmp(name, topic)) { sput(&b, sig); sput(&b, "  -- "); sput(&b, doc); found = 1; }
    for (int i = 0; i < am_rule_count(); i++) {
        const char *n, *src = am_rule_src(i, &n);
        if (!strcmp(n, topic)) { sput(&b, found ? "\n" : ""); sput(&b, "rule: "); sput(&b, src); found = 1; }
    }
    if (!found) {
        const char *s = am_suggest(topic);
        sput(&b, "no function named "); sput(&b, topic);
        if (s) { sput(&b, "; did you mean "); sput(&b, s); sput(&b, "?"); }
    }
    return b.s;
}

/* edit distance, for short names */
static int dist(const char *a, const char *b) {
    int la = (int)strlen(a), lb = (int)strlen(b);
    if (la > 40 || lb > 40) return 99;
    int d[41][41];
    for (int i = 0; i <= la; i++) d[i][0] = i;
    for (int j = 0; j <= lb; j++) d[0][j] = j;
    for (int i = 1; i <= la; i++)
        for (int j = 1; j <= lb; j++) {
            int c = d[i - 1][j - 1] + (a[i - 1] != b[j - 1]);
            if (d[i - 1][j] + 1 < c) c = d[i - 1][j] + 1;
            if (d[i][j - 1] + 1 < c) c = d[i][j - 1] + 1;
            if (i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] && d[i - 2][j - 2] + 1 < c) c = d[i - 2][j - 2] + 1;
            d[i][j] = c;
        }
    return d[la][lb];
}

/* common names from other systems, and what they are called here */
static const char *ALIASES[][2] = {
    {"integrate", "integrate"}, {"solveset", "solve"}, {"nsolve", "solve"}, {"evalf", "N"}, {"Factor", "factor"},
    {"Solve", "solve"}, {"D", "diff"}, {"derivative", "diff"}, {"differentiate", "diff"}, {"Roots", "roots"},
    {"nroots", "roots"}, {"factorint", "factor"}, {"is_prime", "isprime"}, {"Expand", "expand"},
    {"Simplify", "simplify"}, {"numerator", "numer"}, {"denominator", "denom"}, {"subst", "subs"},
    {"substitute", "subs"}, {"ReplaceAll", "subs"}, {"comb", "binomial"}, {"choose", "binomial"},
    {"Sqrt", "sqrt"}, {"Exp", "exp"}, {"Log", "log"}, {NULL, NULL}};

const char *am_suggest(const char *name) {
    for (int i = 0; ALIASES[i][0]; i++) if (!strcmp(ALIASES[i][0], name) && am_builtin(ALIASES[i][1], strlen(ALIASES[i][1]))) return ALIASES[i][1];
    const char *best = NULL, *n, *sig, *doc;
    int bd = 99, limit = strlen(name) <= 4 ? 1 : 2;
    for (int i = 0; am_builtin_doc(i, &n, &sig, &doc); i++) { int d = dist(name, n); if (d < bd) { bd = d; best = n; } }
    for (int i = 0; i < am_rule_count(); i++) { am_rule_src(i, &n); int d = dist(name, n); if (d < bd) { bd = d; best = n; } }
    return bd > 0 && bd <= limit ? best : NULL;
}
