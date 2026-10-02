/* Matrices: a list of rows, each a list of the same length. Exact linear algebra over our values (numbers,
 * algebraic numbers, rational functions in symbols): Gaussian elimination with exact zero tests for the pivots. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int am_is_matrix(const Value *v, int *rows, int *cols) {
    if (v->kind != V_LIST || v->n == 0) return 0;
    int c = -1;
    for (int i = 0; i < v->n; i++) {
        if (v->items[i]->kind != V_LIST) return 0;
        if (c < 0) c = v->items[i]->n; else if (v->items[i]->n != c) return 0;
        for (int j = 0; j < c; j++) { Kind k = v->items[i]->items[j]->kind; if (k != V_NUM && k != V_RF) return 0; }
    }
    if (c <= 0) return 0;
    if (rows) *rows = v->n;
    if (cols) *cols = c;
    return 1;
}

static Value *E(Value *m, int i, int j) { return m->items[i]->items[j]; }
static Value *zero(void) { return v_num(); }
static Value *one(void) { Value *v = v_num(); ca_one(v->num, am_ca); return v; }

static Value *new_matrix(int r, int c) {
    Value *m = v_list(r);
    for (int i = 0; i < r; i++) { m->items[i] = v_list(c); for (int j = 0; j < c; j++) m->items[i]->items[j] = zero(); }
    return m;
}
static Value *copy_matrix(Value *a, int r, int c) {
    Value *m = new_matrix(r, c);
    for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) m->items[i]->items[j] = E(a, i, j);
    return m;
}

static int need_matrix(Value *v, int *r, int *c, const char *f) {
    if (!am_is_matrix(v, r, c)) am_fail("%s needs a matrix: a list of rows of the same length, e.g. [[1, 2], [3, 4]]", f);
    return 1;
}

/* is an entry zero? exact when possible; undecided entries stop the computation */
static int zero_entry(Value *v) {
    if (v->kind == V_NUM) {
        truth_t t = ca_check_is_zero(v->num, am_ca);
        if (t != T_UNKNOWN) return t == T_TRUE;
    } else if (v->kind == V_RF) {
        if (fmpz_mpoly_q_is_zero(v->rf, am_mp)) return 1;
        int used[AM_MAXVARS] = {0}, k = 0;
        fmpz_mpoly_q_used_vars(used, v->rf, am_mp);
        for (int i = 0; i < am_nvars; i++) if (used[i] && am_vars[i].kernel) k = 1;
        if (!k) return 0;
    }
    int z = am_zero_test(v, NULL, 0);
    if (z == 1) return 1;
    if (z == 0) return 0;
    am_fail("matrix: cannot decide whether a pivot is zero");
}

Value *am_matmul(Value *a, Value *b) {
    int ra, ca_, rb, cb;
    need_matrix(a, &ra, &ca_, "matrix product"); need_matrix(b, &rb, &cb, "matrix product");
    if (ca_ != rb) am_fail("matrix product: %dx%d times %dx%d (the inner sizes differ)", ra, ca_, rb, cb);
    Value *m = new_matrix(ra, cb);
    for (int i = 0; i < ra; i++)
        for (int j = 0; j < cb; j++) {
            Value *s = zero();
            for (int k = 0; k < ca_; k++) s = v_add(s, v_mul(E(a, i, k), E(b, k, j)));
            m->items[i]->items[j] = s;
        }
    return m;
}

/* the matrix times a vector (a flat list) */
Value *am_matvec(Value *a, Value *v) {
    int r, c;
    need_matrix(a, &r, &c, "matrix times vector");
    if (v->n != c) am_fail("matrix times vector: %dx%d times a vector of length %d", r, c, v->n);
    Value *out = v_list(r);
    for (int i = 0; i < r; i++) { Value *s = zero(); for (int k = 0; k < c; k++) s = v_add(s, v_mul(E(a, i, k), v->items[k])); out->items[i] = s; }
    return out;
}

static Value *identity(int n) { Value *m = new_matrix(n, n); for (int i = 0; i < n; i++) m->items[i]->items[i] = one(); return m; }

/* reduced row echelon form in place; returns the rank, pivot columns in piv; det receives the determinant when
 * the matrix is square (product of pivots and row swaps) */
static int rref(Value *m, int r, int c, int ncols_elim, int *piv, Value **det) {
    int rank = 0;
    Value *d = one();
    for (int col = 0; col < ncols_elim && rank < r; col++) {
        int p = -1;
        for (int i = rank; i < r && p < 0; i++) if (!zero_entry(E(m, i, col))) p = i;
        if (p < 0) { d = zero(); continue; }
        if (p != rank) { Value *t = m->items[p]; m->items[p] = m->items[rank]; m->items[rank] = t; d = v_neg(d); }
        Value *pv = E(m, rank, col);
        d = v_mul(d, pv);
        for (int j = 0; j < c; j++) m->items[rank]->items[j] = v_div(E(m, rank, j), pv);
        for (int i = 0; i < r; i++) {
            if (i == rank) continue;
            Value *f = E(m, i, col);
            if (zero_entry(f)) continue;
            for (int j = 0; j < c; j++) m->items[i]->items[j] = v_sub(E(m, i, j), v_mul(f, E(m, rank, j)));
        }
        if (piv) piv[rank] = col;
        rank++;
    }
    if (det) *det = rank == r ? d : zero();
    return rank;
}

static Value *b_det(Value **a, int n) {
    if (n != 1) am_fail("det(A)");
    int r, c; need_matrix(a[0], &r, &c, "det");
    if (r != c) am_fail("det: the matrix is %dx%d, not square", r, c);
    Value *m = copy_matrix(a[0], r, c), *d;
    rref(m, r, c, c, NULL, &d);
    am_status(S_EXACT, "exact Gaussian elimination");
    return d;
}

static Value *b_inverse(Value **a, int n) {
    if (n != 1) am_fail("inverse(A)");
    int r, c; need_matrix(a[0], &r, &c, "inverse");
    if (r != c) am_fail("inverse: the matrix is %dx%d, not square", r, c);
    Value *m = new_matrix(r, 2 * c);
    for (int i = 0; i < r; i++) { for (int j = 0; j < c; j++) m->items[i]->items[j] = E(a[0], i, j); m->items[i]->items[c + i] = one(); }
    Value *d;
    int rank = rref(m, r, 2 * c, c, NULL, &d);
    if (rank < r) { am_status(S_PROVED, "the determinant is 0 (rank %d of %d)", rank, r); am_fail("inverse: the matrix is singular (rank %d of %d)", rank, r); }
    Value *inv = new_matrix(r, c);
    for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) inv->items[i]->items[j] = E(m, i, c + j);
    am_status(S_EXACT, "exact Gauss-Jordan elimination");
    return inv;
}

Value *am_matpow(Value *a, Value *e) {
    int r, c; need_matrix(a, &r, &c, "matrix power");
    if (r != c) am_fail("matrix power: the matrix is not square");
    fmpq_t q; fmpq_init(q);
    if (!v_is_rational(e, q) || !fmpz_is_one(fmpq_denref(q)) || fmpz_cmp_si(fmpq_numref(q), 100000) > 0 || fmpz_cmp_si(fmpq_numref(q), -100000) < 0)
        am_fail("matrix power: the exponent must be a whole number");
    slong k = fmpz_get_si(fmpq_numref(q));
    fmpq_clear(q);
    Value *b = a;
    if (k < 0) { b = b_inverse(&a, 1); k = -k; }
    Value *res = identity(r);
    while (k) { if (k & 1) res = am_matmul(res, b); k >>= 1; if (k) b = am_matmul(b, b); }
    return res;
}

static Value *b_transpose(Value **a, int n) {
    if (n != 1) am_fail("transpose(A)");
    int r, c; need_matrix(a[0], &r, &c, "transpose");
    Value *m = new_matrix(c, r);
    for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) m->items[j]->items[i] = E(a[0], i, j);
    return m;
}

static Value *b_rref(Value **a, int n) {
    if (n != 1) am_fail("rref(A)");
    int r, c; need_matrix(a[0], &r, &c, "rref");
    Value *m = copy_matrix(a[0], r, c);
    int piv[256];
    if (r > 256) am_fail("rref: more than 256 rows");
    int rank = rref(m, r, c, c, piv, NULL);
    am_fact("rank", "%d", rank);
    am_status(S_EXACT, "exact Gauss-Jordan elimination");
    return m;
}

static Value *b_rank(Value **a, int n) {
    if (n != 1) am_fail("rank(A)");
    int r, c; need_matrix(a[0], &r, &c, "rank");
    Value *m = copy_matrix(a[0], r, c);
    Value *v = v_num(); ca_set_si(v->num, rref(m, r, c, c, NULL, NULL), am_ca);
    am_status(S_EXACT, "exact Gaussian elimination");
    return v;
}

/* a basis of {x : A x = 0} */
static Value *nullspace(Value *A, int r, int c) {
    Value *m = copy_matrix(A, r, c);
    int piv[256], isp[256] = {0};
    if (r > 256 || c > 256) am_fail("nullspace: at most 256 rows and columns");
    int rank = rref(m, r, c, c, piv, NULL);
    for (int i = 0; i < rank; i++) isp[piv[i]] = 1;
    Value *basis = v_list(c - rank);
    int k = 0;
    for (int f = 0; f < c; f++) {
        if (isp[f]) continue;
        Value *v = v_list(c);
        for (int j = 0; j < c; j++) v->items[j] = zero();
        v->items[f] = one();
        for (int i = 0; i < rank; i++) v->items[piv[i]] = v_neg(E(m, i, f));
        basis->items[k++] = v;
    }
    return basis;
}

static Value *b_nullspace(Value **a, int n) {
    if (n != 1) am_fail("nullspace(A)");
    int r, c; need_matrix(a[0], &r, &c, "nullspace");
    Value *b = nullspace(a[0], r, c);
    am_fact("dimension", "%d", b->n);
    am_status(S_EXACT, "exact Gauss-Jordan elimination");
    return b;
}

/* linsolve(A, b): the solutions of A x = b, as [x1, x2, ...] with free parameters t1, t2, ... when not unique */
static Value *b_linsolve(Value **a, int n) {
    if (n != 2 || a[1]->kind != V_LIST) am_fail("linsolve(A, b): a matrix and a vector (list)");
    int r, c; need_matrix(a[0], &r, &c, "linsolve");
    if (a[1]->n != r) am_fail("linsolve: A has %d rows but b has %d entries", r, a[1]->n);
    if (r > 256 || c > 255) am_fail("linsolve: at most 256 rows and 255 columns");
    Value *m = new_matrix(r, c + 1);
    for (int i = 0; i < r; i++) { for (int j = 0; j < c; j++) m->items[i]->items[j] = E(a[0], i, j); m->items[i]->items[c] = a[1]->items[i]; }
    int piv[256], isp[256] = {0};
    int rank = rref(m, r, c + 1, c, piv, NULL);
    for (int i = rank; i < r; i++)
        if (!zero_entry(E(m, i, c))) {
            am_status(S_PROVED, "the elimination reaches 0 = %s: no solution", v_str_of(E(m, i, c)));
            am_fact("solutions", "0");
            return v_list(0);
        }
    for (int i = 0; i < rank; i++) isp[piv[i]] = 1;
    Value *x = v_list(c);
    int nfree = 0;
    for (int j = 0; j < c; j++) if (!isp[j]) { char nm[16]; snprintf(nm, sizeof nm, "t%d", ++nfree); x->items[j] = am_gen(am_var_index(nm, strlen(nm))); }
    for (int i = 0; i < rank; i++) {
        Value *s = E(m, i, c);
        for (int j = 0; j < c; j++) if (!isp[j]) s = v_sub(s, v_mul(E(m, i, j), x->items[j]));
        x->items[piv[i]] = s;
    }
    am_fact("free_parameters", "%d", nfree);
    am_status(S_EXACT, nfree ? "exact elimination; every solution, with free parameters t1, t2, ..." : "exact elimination; the unique solution");
    return x;
}

static Value *b_charpoly(Value **a, int n) {
    if (n != 2) am_fail("charpoly(A, x): the matrix and the variable");
    int r, c; need_matrix(a[0], &r, &c, "charpoly");
    if (r != c) am_fail("charpoly: the matrix is not square");
    Value *m = new_matrix(r, c);
    for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) m->items[i]->items[j] = i == j ? v_sub(a[1], E(a[0], i, j)) : v_neg(E(a[0], i, j));
    return b_det(&m, 1);
}

static Value *b_eigenvals(Value **a, int n) {
    if (n != 1) am_fail("eigenvals(A)");
    int r, c; need_matrix(a[0], &r, &c, "eigenvals");
    if (r != c) am_fail("eigenvals: the matrix is not square");
    Value *lam = am_gen(am_var_index("lambda_", 7));
    Value *args[2] = {a[0], lam};
    Value *p = b_charpoly(args, 2);
    am_status_clear();
    Value *ra[2] = {p, lam};
    return am_call("roots", ra, 2);
}

static Value *b_eigenvects(Value **a, int n) {
    if (n != 1) am_fail("eigenvects(A)");
    int r, c; need_matrix(a[0], &r, &c, "eigenvects");
    Value *ev = b_eigenvals(a, 1);
    Value *out = v_list(ev->n);
    for (int k = 0; k < ev->n; k++) {
        Value *m = new_matrix(r, c);
        for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) m->items[i]->items[j] = i == j ? v_sub(E(a[0], i, j), ev->items[k]) : E(a[0], i, j);
        Value *pair = v_list(2);
        pair->items[0] = ev->items[k];
        pair->items[1] = nullspace(m, r, c);
        out->items[k] = pair;
    }
    am_status_clear();
    am_status(S_PROVED, "eigenvalues exact (roots of the characteristic polynomial); each eigenspace by exact elimination");
    return out;
}

static Value *b_trace(Value **a, int n) {
    if (n != 1) am_fail("trace(A)");
    int r, c; need_matrix(a[0], &r, &c, "trace");
    if (r != c) am_fail("trace: the matrix is not square");
    Value *s = zero();
    for (int i = 0; i < r; i++) s = v_add(s, E(a[0], i, i));
    return s;
}

static Value *b_identity(Value **a, int n) {
    fmpq_t q; fmpq_init(q);
    if (n != 1 || !v_is_rational(a[0], q) || !fmpz_is_one(fmpq_denref(q)) || fmpz_cmp_si(fmpq_numref(q), 1) < 0 || fmpz_cmp_si(fmpq_numref(q), 1000) > 0)
        am_fail("identity(n): n from 1 to 1000");
    int k = (int)fmpz_get_si(fmpq_numref(q));
    fmpq_clear(q);
    return identity(k);
}

static Value *b_dot(Value **a, int n) {
    if (n != 2 || a[0]->kind != V_LIST || a[1]->kind != V_LIST || a[0]->n != a[1]->n) am_fail("dot(u, v): two lists of the same length");
    Value *s = zero();
    for (int i = 0; i < a[0]->n; i++) s = v_add(s, v_mul(a[0]->items[i], a[1]->items[i]));
    return s;
}

static Value *b_cross(Value **a, int n) {
    if (n != 2 || a[0]->kind != V_LIST || a[1]->kind != V_LIST || a[0]->n != 3 || a[1]->n != 3) am_fail("cross(u, v): two lists of length 3");
    Value **u = a[0]->items, **v = a[1]->items, *r = v_list(3);
    r->items[0] = v_sub(v_mul(u[1], v[2]), v_mul(u[2], v[1]));
    r->items[1] = v_sub(v_mul(u[2], v[0]), v_mul(u[0], v[2]));
    r->items[2] = v_sub(v_mul(u[0], v[1]), v_mul(u[1], v[0]));
    return r;
}

static const struct { const char *name; Builtin f; const char *sig, *doc; } MTABLE[] = {
    {"det", b_det, "det(A)", "determinant (exact)"},
    {"inverse", b_inverse, "inverse(A)", "inverse matrix (exact); A^-1 also works"},
    {"transpose", b_transpose, "transpose(A)", "transpose"},
    {"rref", b_rref, "rref(A)", "reduced row echelon form"},
    {"rank", b_rank, "rank(A)", "rank"},
    {"nullspace", b_nullspace, "nullspace(A)", "a basis of the solutions of A x = 0"},
    {"linsolve", b_linsolve, "linsolve(A, b)", "all solutions of A x = b, with free parameters t1, t2, ... when not unique; [] when none"},
    {"charpoly", b_charpoly, "charpoly(A, x)", "characteristic polynomial det(x I - A)"},
    {"eigenvals", b_eigenvals, "eigenvals(A)", "eigenvalues, exactly (algebraic numbers)"},
    {"eigenvects", b_eigenvects, "eigenvects(A)", "[[eigenvalue, [basis of its eigenspace]], ...]"},
    {"trace", b_trace, "trace(A)", "trace"},
    {"identity", b_identity, "identity(n)", "the n x n identity matrix"},
    {"dot", b_dot, "dot(u, v)", "dot product"},
    {"cross", b_cross, "cross(u, v)", "cross product in 3 dimensions"},
    {NULL, NULL, NULL, NULL}};

Builtin am_matrix_builtin(const char *name, size_t len) {
    for (int i = 0; MTABLE[i].name; i++) if (strlen(MTABLE[i].name) == len && !strncmp(MTABLE[i].name, name, len)) return MTABLE[i].f;
    return NULL;
}
int am_matrix_doc(int i, const char **name, const char **sig, const char **doc) {
    if (!MTABLE[i].name) return 0;
    *name = MTABLE[i].name; *sig = MTABLE[i].sig; *doc = MTABLE[i].doc;
    return 1;
}
