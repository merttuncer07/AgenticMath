/* amath --mcp: a Model Context Protocol server on stdin/stdout (JSON-RPC 2.0, one message per line).
 * Two tools: evaluate (statements in a session that keeps its definitions) and reference (the language). */
#include "am.h"
#include "json.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define AM_VERSION "0.2"

static const char *EVALUATE_DESC =
    "Exact and certified mathematics. Give one or more statements, one per line; definitions and names persist "
    "for the session. Notation: x^2, 2x, sqrt, pi, E, I, [lists], equations x^2 = 2, tests ==. Examples: "
    "factor(x^4 - 1); roots(x^3 - x - 1); solve([x^2 + y^2 = 5, x - y = 1], [x, y]); N(pi, 50); "
    "diff(sin(x)^2, x); f(x) := x^2 + 1. Each statement returns one JSON object: answer, status (proved | exact | "
    "certified | probable | numeric | unknown: how far the answer can be trusted), verdict (why), facts (things the "
    "computation established: degrees, numbers of roots, multiplicities ...), work (the steps, with show), or error "
    "(why it failed). Call the reference tool for the full list of functions.";

static const char *REFERENCE_DESC =
    "The AgenticMath language reference: notation, statuses, every function with its signature, and the library "
    "rules. Give a topic (a function name) for one entry, or nothing for everything.";

static void reply(const char *id, const char *result) {
    printf("{\"jsonrpc\":\"2.0\",\"id\":%s,\"result\":%s}\n", id, result);
    fflush(stdout);
}
static void reply_error(const char *id, int code, const char *msg) {
    char *m = am_json_str(msg);
    printf("{\"jsonrpc\":\"2.0\",\"id\":%s,\"error\":{\"code\":%d,\"message\":%s}}\n", id, code, m);
    fflush(stdout);
    free(m);
}

typedef struct { char *s; size_t n, cap; } Str;
static void sput(Str *b, const char *s) {
    size_t n = strlen(s);
    if (b->n + n + 1 > b->cap) { b->cap = (b->n + n + 1) * 2 + 256; b->s = realloc(b->s, b->cap); }
    memcpy(b->s + b->n, s, n + 1);
    b->n += n;
}

static void tool_result(const char *id, const char *text, int is_error) {
    char *t = am_json_str(text);
    Str r = {0, 0, 0};
    sput(&r, "{\"content\":[{\"type\":\"text\",\"text\":");
    sput(&r, t);
    sput(&r, "}],\"isError\":");
    sput(&r, is_error ? "true}" : "false}");
    reply(id, r.s);
    free(t); free(r.s);
}

static void evaluate(const char *id, JNode *args) {
    JNode *code = json_get(args, "code"), *show = json_get(args, "show"), *maxc = json_get(args, "max_chars");
    if (!code || code->type != J_STRING) { tool_result(id, "evaluate needs a string argument 'code'", 1); return; }
    int sh = show && show->type == J_BOOL && show->num;
    am_max_chars = maxc && maxc->type == J_NUMBER && maxc->num > 0 ? (long)maxc->num : 4000;
    Str out = {0, 0, 0};
    sput(&out, "");
    int failures = 0, statements = 0;
    const char *p = code->str;
    while (*p) {
        const char *e = strchr(p, '\n');
        size_t n = e ? (size_t)(e - p) : strlen(p);
        char *line = malloc(n + 8);
        sprintf(line, "%s%.*s", sh ? "show " : "", (int)n, p);
        const char *t = line + (sh ? 5 : 0);
        while (*t == ' ' || *t == '\t' || *t == '\r') t++;
        if (*t && *t != '#') {
            int failed;
            char *r = am_run(sh && !strncmp(t, "show ", 5) ? t : line, &failed);
            if (r) { if (out.n) sput(&out, "\n"); sput(&out, r); free(r); statements++; failures += failed; }
        }
        free(line);
        p += n + (e ? 1 : 0);
    }
    am_max_chars = 0;
    if (!statements) { tool_result(id, "no statements given", 1); free(out.s); return; }
    tool_result(id, out.s, failures == statements);
    free(out.s);
}

static void tools_list(const char *id) {
    char *ed = am_json_str(EVALUATE_DESC), *rd = am_json_str(REFERENCE_DESC);
    Str r = {0, 0, 0};
    sput(&r, "{\"tools\":[{\"name\":\"evaluate\",\"description\":"); sput(&r, ed);
    sput(&r, ",\"inputSchema\":{\"type\":\"object\",\"properties\":{"
             "\"code\":{\"type\":\"string\",\"description\":\"statements, one per line\"},"
             "\"show\":{\"type\":\"boolean\",\"description\":\"also return the steps and rules applied\"},"
             "\"max_chars\":{\"type\":\"integer\",\"description\":\"cut answers longer than this (default 4000)\"}},"
             "\"required\":[\"code\"]}},");
    sput(&r, "{\"name\":\"reference\",\"description\":"); sput(&r, rd);
    sput(&r, ",\"inputSchema\":{\"type\":\"object\",\"properties\":{"
             "\"topic\":{\"type\":\"string\",\"description\":\"a function name, or empty for the whole reference\"}}}}]}");
    reply(id, r.s);
    free(ed); free(rd); free(r.s);
}

int am_mcp(void) {
    am_json = 1;
    char *line = NULL;
    size_t cap = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        JNode *m = json_parse(line);
        JNode *method = json_get(m, "method"), *idn = json_get(m, "id"), *params = json_get(m, "params");
        const char *id = idn ? idn->raw : NULL;
        if (!method || method->type != J_STRING) {
            if (id) reply_error(id, -32600, "invalid request");
            json_free(m);
            continue;
        }
        const char *mt = method->str;
        if (!id) { json_free(m); continue; }                     /* a notification: no reply */
        if (!strcmp(mt, "initialize")) {
            JNode *pv = json_get(params, "protocolVersion");
            char *v = am_json_str(pv && pv->type == J_STRING ? pv->str : "2025-06-18");
            char *ins = am_json_str("Use evaluate for any exact computation: factoring, roots, systems, derivatives, "
                                    "certified decimals. Trust an answer as far as its status says.");
            Str r = {0, 0, 0};
            sput(&r, "{\"protocolVersion\":"); sput(&r, v);
            sput(&r, ",\"capabilities\":{\"tools\":{\"listChanged\":false}},\"serverInfo\":{\"name\":\"agenticmath\",\"version\":\"" AM_VERSION "\"},\"instructions\":");
            sput(&r, ins); sput(&r, "}");
            reply(id, r.s);
            free(v); free(ins); free(r.s);
        } else if (!strcmp(mt, "ping")) reply(id, "{}");
        else if (!strcmp(mt, "tools/list")) tools_list(id);
        else if (!strcmp(mt, "tools/call")) {
            JNode *name = json_get(params, "name"), *args = json_get(params, "arguments");
            if (!name || name->type != J_STRING) reply_error(id, -32602, "tools/call needs a tool name");
            else if (!strcmp(name->str, "evaluate")) evaluate(id, args);
            else if (!strcmp(name->str, "reference")) {
                JNode *t = json_get(args, "topic");
                char *r = am_reference(t && t->type == J_STRING ? t->str : NULL);
                tool_result(id, r, 0);
                free(r);
            } else reply_error(id, -32602, "unknown tool");
        } else reply_error(id, -32601, "method not found");
        json_free(m);
    }
    free(line);
    return 0;
}
