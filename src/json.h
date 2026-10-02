/* A small JSON reader for MCP messages. */
#ifndef AM_JSON_H
#define AM_JSON_H

typedef enum { J_NULL, J_BOOL, J_NUMBER, J_STRING, J_ARRAY, J_OBJECT } JType;
typedef struct JNode JNode;
struct JNode {
    JType type;
    double num;           /* J_NUMBER; J_BOOL: 0 or 1 */
    char *str;            /* J_STRING, unescaped */
    char *raw;            /* the value as written (used to echo an id) */
    int n; char **keys; JNode **kids;
};

JNode *json_parse(const char *s);
JNode *json_get(const JNode *j, const char *key);
void json_free(JNode *j);

#endif
