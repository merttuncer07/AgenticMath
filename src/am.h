/* AgenticMath: shared declarations. */
#ifndef AM_H
#define AM_H

#include <setjmp.h>
#include <stddef.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpq.h>
#include <flint/fmpz_mpoly.h>
#include <flint/fmpz_mpoly_q.h>
#include <flint/ca.h>

/* ---- errors: am_fail longjmps to the statement runner ---- */
extern jmp_buf am_on_error;
void am_fail(const char *fmt, ...) __attribute__((noreturn, format(printf, 1, 2)));

/* ---- the engines' contexts ---- */
#define AM_MAXVARS 64
extern ca_ctx_t am_ca;                       /* exact numbers */
extern fmpz_mpoly_ctx_t am_mp;               /* polynomials in the variables and kernels met so far */
extern const char *am_varnames[AM_MAXVARS];
extern int am_nvars;

/* ---- values ---- */
typedef enum { V_NUM, V_RF, V_LIST, V_EQ, V_BOOL, V_STR } Kind;

typedef struct Value Value;
struct Value {
    Kind kind;
    ca_t num;                  /* V_NUM: an exact complex number (Calcium) */
    fmpz_mpoly_q_t rf;         /* V_RF: a rational function over Q in the variables */
    Value **items; int n;      /* V_LIST; V_EQ has items[0] = items[1] */
    int truth;                 /* V_BOOL: 1 true, 0 false, -1 unknown */
    char *str;                 /* V_STR */
};

Value *v_num(void);            /* fresh 0 */
Value *v_rf(void);
Value *v_list(int n);
Value *v_bool(int t);
Value *v_str(const char *s);
Value *v_copy(const Value *a);
void am_pool_keep(Value *v);   /* survive the end of the statement (a named value) */
void am_pool_release(void);    /* free the statement's temporaries */

int v_is_rational(const Value *v, fmpq_t out);   /* a rational number (as V_NUM or a constant V_RF) */
Value *v_to_rf(const Value *v);                  /* a V_NUM that is rational, or a V_RF */
Value *v_add(const Value *a, const Value *b);
Value *v_sub(const Value *a, const Value *b);
Value *v_mul(const Value *a, const Value *b);
Value *v_div(const Value *a, const Value *b);
Value *v_neg(const Value *a);
Value *v_pow(const Value *a, const Value *b);
char *v_str_of(const Value *v);                  /* the answer as text (malloc'd) */

/* ---- variables and kernels (kernel.c): sin(x), f(x), sqrt(2) among variables, as generators ---- */
typedef struct {
    char *name;
    int kernel;                /* 0: a plain variable */
    char *head; Value **args; int nargs;    /* a function term head(args) */
    Value *numval;             /* an irrational number used as a generator */
} AmVar;
extern AmVar am_vars[AM_MAXVARS];
int am_var_index(const char *name, size_t len);   /* a plain variable, registered on first use */
Value *am_gen(int i);
int am_gen_of(const Value *v);                     /* the generator v is exactly, or -1 */
Value *am_kernel_value(const char *head, Value **args, int n);
Value *am_number_kernel(const Value *num);

/* ---- the account of a statement: status, verdict, facts, work ---- */
typedef enum { S_NONE, S_EXACT, S_PROVED, S_CERTIFIED, S_PROBABLE, S_NUMERIC, S_UNKNOWN } Status;
extern int am_json, am_show;
void am_account_reset(void);
void am_status(Status s, const char *fmt, ...) __attribute__((format(printf, 2, 3)));   /* weakest status wins */
int am_status_set(void);
void am_fact(const char *key, const char *json_fmt, ...) __attribute__((format(printf, 2, 3)));
void am_work(const char *fmt, ...) __attribute__((format(printf, 1, 2)));
char *am_json_str(const char *s);               /* malloc'd JSON string literal */
char *am_render(const char *input, const char *answer, const char *error);   /* malloc'd output */

/* ---- the language ---- */
char *am_run(const char *line, int *failed);    /* one statement; the rendered output, malloc'd, or NULL */
void am_init(void);
void am_load_library(void);                     /* the library written in the language (lib/ *.am, built in) */
Value *am_call(const char *name, Value **args, int n);
Value *am_reevaluate(Value *v);                 /* function terms evaluated again: numbers back to numbers */
Value *am_subs_rf(const Value *f, Value **val);  /* values for the generators */
int am_free_of(const Value *v, int x);   /* rules first, then the built-in, else a kernel */

/* ---- built-in functions ---- */
typedef Value *(*Builtin)(Value **args, int n);
Builtin am_builtin(const char *name, size_t len);

#endif
