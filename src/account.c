/* The account a statement gives of itself: how sure the answer is (status and verdict), facts the computation
 * produced anyway, and the steps actually taken. Rendered as text for a person or as one JSON line for a program.
 * Nothing is computed here. */
#include "am.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int am_json, am_show, am_fact_mute;

typedef struct { char *s; size_t n, cap; } Buf;
static Buf facts, work;
static Status status;
static char verdict[512];

static void put(Buf *b, const char *s, size_t n) {
    if (b->n + n + 1 > b->cap) {
        b->cap = (b->n + n + 1) * 2;
        b->s = realloc(b->s, b->cap);
        if (!b->s) { fprintf(stderr, "out of memory\n"); exit(2); }
    }
    memcpy(b->s + b->n, s, n);
    b->n += n;
    b->s[b->n] = 0;
}
static void puts_(Buf *b, const char *s) { put(b, s, strlen(s)); }

static void put_json_str(Buf *b, const char *s) {
    put(b, "\"", 1);
    for (; *s; s++) {
        char e[8];
        if (*s == '"' || *s == '\\') { e[0] = '\\'; e[1] = *s; put(b, e, 2); }
        else if (*s == '\n') put(b, "\\n", 2);
        else if ((unsigned char)*s < 0x20) { snprintf(e, sizeof e, "\\u%04x", *s); put(b, e, 6); }
        else put(b, s, 1);
    }
    put(b, "\"", 1);
}

char *am_json_str(const char *s) { Buf b = {0, 0, 0}; put_json_str(&b, s); return b.s; }

static char *vfmt(const char *fmt, va_list ap) {
    va_list cp;
    va_copy(cp, ap);
    int n = vsnprintf(NULL, 0, fmt, cp);
    va_end(cp);
    char *s = malloc((size_t)n + 1);
    vsnprintf(s, (size_t)n + 1, fmt, ap);
    return s;
}

void am_account_reset(void) {
    facts.n = work.n = 0;
    if (facts.s) facts.s[0] = 0;
    if (work.s) work.s[0] = 0;
    status = S_NONE;
    verdict[0] = 0;
}

/* strength of a status: an answer is only as sure as its weakest part */
static int rank(Status s) {
    switch (s) {
    case S_PROVED: return 6;
    case S_EXACT: return 5;
    case S_CERTIFIED: return 4;
    case S_PROBABLE: return 3;
    case S_NUMERIC: return 2;
    case S_UNKNOWN: return 1;
    default: return 99;
    }
}
static const char *status_name(Status s) {
    switch (s) {
    case S_PROVED: return "proved";
    case S_EXACT: return "exact";
    case S_CERTIFIED: return "certified";
    case S_PROBABLE: return "probable";
    case S_NUMERIC: return "numeric";
    case S_UNKNOWN: return "unknown";
    default: return NULL;
    }
}

int am_status_set(void) { return status != S_NONE; }
Status am_status_get(void) { return status; }
void am_status_clear(void) { status = S_NONE; verdict[0] = 0; }

void am_status(Status s, const char *fmt, ...) {
    if (rank(s) >= rank(status) && status != S_NONE) return;
    status = s;
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(verdict, sizeof verdict, fmt, ap);
    va_end(ap);
}

void am_fact(const char *key, const char *json_fmt, ...) {
    if (am_fact_mute) return;
    Buf k = {0, 0, 0};
    put_json_str(&k, key);
    put(&k, ":", 1);
    int dup = facts.n && strstr(facts.s, k.s) != NULL;     /* a key is given once: the first stands */
    if (!dup) {
        va_list ap;
        va_start(ap, json_fmt);
        char *val = vfmt(json_fmt, ap);
        va_end(ap);
        if (facts.n) put(&facts, ",", 1);
        puts_(&facts, k.s);
        puts_(&facts, val);
        free(val);
    }
    free(k.s);
}

void am_work(const char *fmt, ...) {
    if (!am_show) return;
    va_list ap;
    va_start(ap, fmt);
    char *line = vfmt(fmt, ap);
    va_end(ap);
    if (work.n) put(&work, "\n", 1);
    puts_(&work, line);
    free(line);
}

long am_max_chars;
static char *cut_buf;

/* a long answer is cut, and the facts say how long it was */
static const char *cut(const char *answer) {
    size_t n = strlen(answer);
    if (am_max_chars <= 0 || n <= (size_t)am_max_chars) return answer;
    free(cut_buf);
    cut_buf = malloc((size_t)am_max_chars + 96);
    memcpy(cut_buf, answer, (size_t)am_max_chars);
    sprintf(cut_buf + am_max_chars, " ... [cut: %zu characters in all]", n);
    am_fact("cut", "{\"characters\":%zu,\"shown\":%ld}", n, am_max_chars);
    return cut_buf;
}

char *am_render(const char *input, const char *answer, const char *error) {
    Buf b = {0, 0, 0};
    const char *st = status_name(status);
    if (!am_json) {
        if (work.n) {                                 /* the steps, indented, before the answer */
            const char *p = work.s;
            while (*p) {
                const char *e = strchr(p, '\n');
                size_t n = e ? (size_t)(e - p) : strlen(p);
                puts_(&b, "  "); put(&b, p, n); puts_(&b, "\n");
                p += n + (e ? 1 : 0);
            }
        }
        if (am_show && facts.n) { puts_(&b, "  facts: {"); puts_(&b, facts.s); puts_(&b, "}\n"); }
        if (error) { puts_(&b, "error: "); puts_(&b, error); return b.s; }
        answer = cut(answer);
        puts_(&b, answer);
        if (st) {
            puts_(&b, "  [");
            puts_(&b, st);
            if (verdict[0]) { puts_(&b, ": "); puts_(&b, verdict); }
            puts_(&b, "]");
        }
        return b.s;
    }
    char *in = strdup(input);
    size_t n = strlen(in);
    while (n && (in[n - 1] == '\n' || in[n - 1] == '\r')) in[--n] = 0;
    puts_(&b, "{\"input\":"); put_json_str(&b, in);
    free(in);
    if (error) { puts_(&b, ",\"error\":"); put_json_str(&b, error); }
    else {
        answer = cut(answer);
        puts_(&b, ",\"answer\":"); put_json_str(&b, answer);
        if (st) { puts_(&b, ",\"status\":"); put_json_str(&b, st); }
        if (verdict[0]) { puts_(&b, ",\"verdict\":"); put_json_str(&b, verdict); }
    }
    if (facts.n) { puts_(&b, ",\"facts\":{"); puts_(&b, facts.s); puts_(&b, "}"); }
    if (work.n) {
        puts_(&b, ",\"work\":[");
        const char *p = work.s;
        int first = 1;
        while (*p) {
            const char *e = strchr(p, '\n');
            size_t k = e ? (size_t)(e - p) : strlen(p);
            char *line = malloc(k + 1); memcpy(line, p, k); line[k] = 0;
            if (!first) puts_(&b, ",");
            put_json_str(&b, line);
            free(line);
            first = 0;
            p += k + (e ? 1 : 0);
        }
        puts_(&b, "]");
    }
    puts_(&b, "}");
    return b.s;
}
