/* The result of msolve on a polynomial system, as read from its output. */
#ifndef MSOLVE_BRIDGE_H
#define MSOLVE_BRIDGE_H

#include <flint/fmpz_poly.h>
#include <flint/fmpq_vec.h>

typedef struct {
    int kind;                    /* 0 finitely many solutions, 1 infinitely many (dimension > 0), -1 none */
    int nvars;                   /* msolve's variables; it may add one, named A, for genericity */
    char **names;
    fmpq *lf;                    /* t = sum lf_i x_i */
    fmpz_poly_t w, wd;           /* w(t) = 0; wd plays the part of w'(t) */
    int ncoord;                  /* x_i = -v_i(t) / (c_i wd(t)) for the first ncoord variables */
    fmpz_poly_struct *v;
    fmpz *c;
    long nreal;                  /* real solutions isolated by msolve */
} MsolveResult;

void am_msolve(MsolveResult *R, const char *input, int seconds);
void am_msolve_clear(MsolveResult *R);

#endif
