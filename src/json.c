/* A small JSON reader, enough for the MCP messages amath receives. */
#include "json.h"

#include <ctype.h>
#include <stdlib.h>
#include <string.h>

static const char *p;

static void ws(void) { while (*p && isspace((unsigned char)*p)) p++; }

static void put(char **s, size_t *n, size_t *cap, char c) {
    if (*n + 2 > *cap) { *cap = *cap ? 2 * *cap : 64; *s = realloc(*s, *cap); }
    (*s)[(*n)++] = c; (*s)[*n] = 0;
}

static void put_utf8(char **s, size_t *n, size_t *cap, unsigned u) {
    if (u < 0x80) put(s, n, cap, (char)u);
    else if (u < 0x800) { put(s, n, cap, (char)(0xC0 | (u >> 6))); put(s, n, cap, (char)(0x80 | (u & 0x3F))); }
    else { put(s, n, cap, (char)(0xE0 | (u >> 12))); put(s, n, cap, (char)(0x80 | ((u >> 6) & 0x3F))); put(s, n, cap, (char)(0x80 | (u & 0x3F))); }
}

static char *string(void) {                   /* at the opening quote */
    p++;
    char *s = NULL; size_t n = 0, cap = 0;
    put(&s, &n, &cap, 0); n = 0;
    while (*p && *p != '"') {
        if (*p == '\\') {
            p++;
            switch (*p) {
            case 'n': put(&s, &n, &cap, '\n'); break;
            case 't': put(&s, &n, &cap, '\t'); break;
            case 'r': put(&s, &n, &cap, '\r'); break;
            case 'b': put(&s, &n, &cap, '\b'); break;
            case 'f': put(&s, &n, &cap, '\f'); break;
            case 'u': {
                unsigned u = 0;
                for (int i = 1; i <= 4 && isxdigit((unsigned char)p[i]); i++) u = u * 16 + (unsigned)(isdigit((unsigned char)p[i]) ? p[i] - '0' : (tolower((unsigned char)p[i]) - 'a' + 10));
                p += 4;
                put_utf8(&s, &n, &cap, u);
                break;
            }
            default: if (*p) put(&s, &n, &cap, *p);
            }
            if (*p) p++;
        } else put(&s, &n, &cap, *p++);
    }
    if (*p == '"') p++;
    return s;
}

static JNode *value(void) {
    ws();
    JNode *j = calloc(1, sizeof *j);
    const char *start = p;
    if (*p == '{' || *p == '[') {
        int obj = *p == '{';
        j->type = obj ? J_OBJECT : J_ARRAY;
        p++; ws();
        while (*p && *p != (obj ? '}' : ']')) {
            j->keys = realloc(j->keys, (size_t)(j->n + 1) * sizeof *j->keys);
            j->kids = realloc(j->kids, (size_t)(j->n + 1) * sizeof *j->kids);
            j->keys[j->n] = NULL;
            if (obj) { ws(); j->keys[j->n] = *p == '"' ? string() : strdup(""); ws(); if (*p == ':') p++; }
            j->kids[j->n++] = value();
            ws();
            if (*p == ',') p++;
            ws();
        }
        if (*p) p++;
    } else if (*p == '"') { j->type = J_STRING; j->str = string(); }
    else if (!strncmp(p, "true", 4)) { j->type = J_BOOL; j->num = 1; p += 4; }
    else if (!strncmp(p, "false", 5)) { j->type = J_BOOL; p += 5; }
    else if (!strncmp(p, "null", 4)) { j->type = J_NULL; p += 4; }
    else {
        j->type = J_NUMBER;
        j->num = strtod(p, (char **)&p);
        if (p == start) p++;                          /* skip something unreadable */
    }
    j->raw = strndup(start, (size_t)(p - start));
    return j;
}

JNode *json_parse(const char *s) { p = s; return value(); }

JNode *json_get(const JNode *j, const char *key) {
    if (!j || j->type != J_OBJECT) return NULL;
    for (int i = 0; i < j->n; i++) if (j->keys[i] && !strcmp(j->keys[i], key)) return j->kids[i];
    return NULL;
}

void json_free(JNode *j) {
    if (!j) return;
    for (int i = 0; i < j->n; i++) { json_free(j->kids[i]); free(j->keys[i]); }
    free(j->kids); free(j->keys); free(j->str); free(j->raw); free(j);
}
