#define _GNU_SOURCE
/* Certificates that another system can check.
 *
 * cofactors(g, [h1, ..., hk]): polynomials c_i with g = c_1 h_1 + ... + c_k h_k, which shows that g = 0 follows from
 * h_1 = 0, ..., h_k = 0 (g lies in the ideal they generate). Found by linear algebra over Q on the coefficients
 * (a Macaulay matrix), degree by degree; checked by expanding the sum. In Lean this is exactly what
 * linear_combination checks, so with the `lean` prefix the facts carry a Lean 4 proof.
 *
 * The `lean` prefix also gives Lean 4 proofs for factorizations and identities (ring), equalities of rational
 * functions (field_simp; ring) and primality (norm_num). They are generated here; Lean itself is not run. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#include <flint/fmpq_mat.h>
#include <flint/fmpq_vec.h>

int am_lean;

/* with AMATH_LEAN_PROJECT set to a Lean project that has Mathlib, run Lean on the certificate: in a child process,
 * the source in a memory file, nothing written to disk. 1 accepted, 0 rejected (msg filled), -1 not run */
static int lean_check(const char *code, char *msg, size_t mlen) {
    const char *proj = getenv("AMATH_LEAN_PROJECT");
    if (!proj || !*proj) return -1;
    int in = memfd_create("amath-lean", 0), out = memfd_create("amath-lean-out", 0);
    if (in < 0 || out < 0) return -1;
    const char *head = "import Mathlib.Tactic.LinearCombination\nimport Mathlib.Tactic.Ring\nimport Mathlib.Tactic.NormNum.Prime\n\n";
    if (write(in, head, strlen(head)) < 0 || write(in, code, strlen(code)) < 0 || write(in, "\n", 1) < 0) { close(in); close(out); return -1; }
    fflush(stdout);
    pid_t pid = fork();
    if (pid < 0) { close(in); close(out); return -1; }
    if (pid == 0) {
        alarm(120);
        if (chdir(proj) != 0) _exit(127);
        dup2(out, 1); dup2(out, 2);
        char path[64]; snprintf(path, sizeof path, "/proc/self/fd/%d", in);
        execlp("lake", "lake", "env", "lean", path, (char *)NULL);
        _exit(127);
    }
    int st; waitpid(pid, &st, 0);
    close(in);
    off_t n = lseek(out, 0, SEEK_END); lseek(out, 0, SEEK_SET);
    size_t k = (size_t)n < mlen - 1 ? (size_t)n : mlen - 1;
    ssize_t got = read(out, msg, k); msg[got > 0 ? got : 0] = 0;
    close(out);
    if (WIFEXITED(st) && WEXITSTATUS(st) == 127) return -1;
    return WIFEXITED(st) && WEXITSTATUS(st) == 0 && !strstr(msg, "error") ? 1 : 0;
}

void am_lean_fact(const char *code) {
    if (!am_lean) return;
    char *js = am_json_str(code);
    am_fact("lean", "%s", js);
    free(js);
    char msg[2048];
    int r = lean_check(code, msg, sizeof msg);
    if (r == 1) am_fact("lean_checked", "true");
    else if (r == 0) { am_fact("lean_checked", "false"); char *m = am_json_str(msg); am_fact("lean_message", "%s", m); free(m); }
}

/* the variables (plain, not function terms) of a list of values; 0 if a function term or irrational appears */
static int poly_vars(Value **v, int n, int *vars) {
    int used[AM_MAXVARS] = {0}, k = 0;
    for (int i = 0; i < n; i++) {
        if (v[i]->kind == V_NUM) continue;
        if (v[i]->kind != V_RF) return -1;
        if (!fmpz_mpoly_is_fmpz(fmpz_mpoly_q_denref(v[i]->rf), am_mp)) return -1;
        int u[AM_MAXVARS] = {0};
        fmpz_mpoly_q_used_vars(u, v[i]->rf, am_mp);
        for (int j = 0; j < am_nvars; j++) if (u[j]) { if (am_vars[j].kernel) return -1; used[j] = 1; }
    }
    for (int j = 0; j < am_nvars; j++) if (used[j]) vars[k++] = j;
    return k;
}

char *am_lean_vars(int *vars, int nv) {
    size_t cap = 32;
    for (int i = 0; i < nv; i++) cap += strlen(am_varnames[vars[i]]) + 1;
    char *s = malloc(cap), *o = s;
    if (!nv) { strcpy(s, ""); return s; }
    o += sprintf(o, "(");
    for (int i = 0; i < nv; i++) o += sprintf(o, "%s%s", i ? " " : "", am_varnames[vars[i]]);
    sprintf(o, " : ℚ) ");
    return s;
}

/* monomials of total degree <= d in nv variables, as exponent rows */
static int monomials(int nv, int d, ulong **out) {
    int cap = 64, n = 0;
    ulong *m = malloc((size_t)cap * (size_t)(nv ? nv : 1) * sizeof(ulong));
    ulong e[AM_MAXVARS] = {0};
    for (;;) {
        if (n == cap) { cap *= 2; m = realloc(m, (size_t)cap * (size_t)(nv ? nv : 1) * sizeof(ulong)); }
        memcpy(m + (size_t)n * (size_t)nv, e, (size_t)nv * sizeof(ulong));
        n++;
        if (n > 20000) am_fail("cofactors: too many monomials");
        int i = 0, tot = 0;                                   /* the next exponent vector of total degree <= d */
        for (int j = 0; j < nv; j++) tot += (int)e[j];
        while (i < nv) {
            if (tot < d) { e[i]++; break; }
            tot -= (int)e[i]; e[i] = 0; i++;
        }
        if (i == nv) break;
    }
    *out = m;
    return n;
}

/* p as integer coefficients over a common denominator, read at an exponent vector in the given variables */
static void coeff_at(fmpq_t c, const Value *p, const int *vars, int nv, const ulong *e) {
    if (p->kind == V_NUM) {
        int zero = 1;
        for (int i = 0; i < nv; i++) if (e[i]) zero = 0;
        fmpq_zero(c);
        if (zero) { fmpq_t q; fmpq_init(q); if (CA_IS_QQ(p->num, am_ca)) fmpq_set(c, CA_FMPQ(p->num)); fmpq_clear(q); }
        return;
    }
    ulong full[AM_MAXVARS] = {0};
    for (int i = 0; i < nv; i++) full[vars[i]] = e[i];
    fmpz_t a, d; fmpz_init(a); fmpz_init(d);
    fmpz_mpoly_get_coeff_fmpz_ui(a, fmpz_mpoly_q_numref(p->rf), full, am_mp);
    fmpz_mpoly_get_fmpz(d, fmpz_mpoly_q_denref(p->rf), am_mp);
    fmpq_set_fmpz_frac(c, a, d);
    fmpz_clear(a); fmpz_clear(d);
}

static slong tdeg(const Value *p) { return p->kind == V_RF ? fmpz_mpoly_total_degree_si(fmpz_mpoly_q_numref(p->rf), am_mp) : 0; }

static Value *eq_expr(Value *e) { return e->kind == V_EQ ? v_sub(e->items[0], e->items[1]) : e; }

Value *b_cofactors(Value **a, int n) {
    if (n != 2 || a[1]->kind != V_LIST) am_fail("cofactors(g, [h1, ..., hk]): g and the h's are polynomials or equations");
    int k = a[1]->n;
    if (k < 1 || k > 20) am_fail("cofactors: between 1 and 20 hypotheses");
    Value **all = malloc((size_t)(k + 1) * sizeof(Value *));
    all[0] = eq_expr(a[0]);
    for (int i = 0; i < k; i++) all[i + 1] = eq_expr(a[1]->items[i]);
    int vars[AM_MAXVARS];
    int nv = poly_vars(all, k + 1, vars);
    if (nv < 0) am_fail("cofactors: polynomials with rational coefficients only (no sqrt, sin, ... )");
    slong dg = tdeg(all[0]), dmax = dg;
    for (int i = 1; i <= k; i++) if (tdeg(all[i]) > dmax) dmax = tdeg(all[i]);
    Value **cof = NULL;
    slong used_D = -1;
    for (slong D = dmax; D <= dmax + 6 && !cof; D++) {
        ulong *rows; int nr = monomials(nv, (int)D, &rows);
        /* unknowns: for each h_i, a coefficient for each monomial of degree <= D - deg(h_i) */
        int *off = malloc((size_t)(k + 1) * sizeof(int)), nu = 0;
        ulong **um = malloc((size_t)k * sizeof(ulong *)); int *un = malloc((size_t)k * sizeof(int));
        for (int i = 0; i < k; i++) {
            off[i] = nu;
            slong di = D - tdeg(all[i + 1]);
            if (di < 0) { un[i] = 0; um[i] = NULL; continue; }
            un[i] = monomials(nv, (int)di, &um[i]);
            nu += un[i];
        }
        off[k] = nu;
        if ((long)nr * (nu + 1) > 4000000) { free(rows); for (int i = 0; i < k; i++) free(um[i]); free(um); free(un); free(off); break; }
        fmpq_mat_t M; fmpq_mat_init(M, nr, nu + 1);
        ulong e[AM_MAXVARS];
        fmpq_t c; fmpq_init(c);
        for (int r = 0; r < nr; r++) {
            const ulong *re = rows + (size_t)r * (size_t)nv;
            for (int i = 0; i < k; i++)
                for (int j = 0; j < un[i]; j++) {                /* the coefficient of re in m_j * h_i */
                    const ulong *me = um[i] + (size_t)j * (size_t)nv;
                    int ok = 1;
                    for (int t = 0; t < nv && ok; t++) { if (re[t] < me[t]) ok = 0; else e[t] = re[t] - me[t]; }
                    if (!ok) continue;
                    coeff_at(c, all[i + 1], vars, nv, e);
                    fmpq_set(fmpq_mat_entry(M, r, off[i] + j), c);
                }
            coeff_at(c, all[0], vars, nv, re);
            fmpq_set(fmpq_mat_entry(M, r, nu), c);
        }
        fmpq_mat_rref(M, M);
        int consistent = 1;
        for (int r = 0; r < nr && consistent; r++) {           /* a row 0 ... 0 | b with b != 0: no solution */
            int lead = -1;
            for (int j = 0; j <= nu && lead < 0; j++) if (!fmpq_is_zero(fmpq_mat_entry(M, r, j))) lead = j;
            if (lead == nu) consistent = 0;
        }
        if (consistent) {
            fmpq *sol = _fmpq_vec_init(nu ? nu : 1);
            for (int r = 0; r < nr; r++) {
                int lead = -1;
                for (int j = 0; j < nu && lead < 0; j++) if (!fmpq_is_zero(fmpq_mat_entry(M, r, j))) lead = j;
                if (lead >= 0) fmpq_set(sol + lead, fmpq_mat_entry(M, r, nu));
            }
            cof = malloc((size_t)k * sizeof(Value *));
            for (int i = 0; i < k; i++) {
                Value *ci = v_num();
                for (int j = 0; j < un[i]; j++) {
                    if (fmpq_is_zero(sol + off[i] + j)) continue;
                    Value *t = v_num(); ca_set_fmpq(t->num, sol + off[i] + j, am_ca);
                    const ulong *me = um[i] + (size_t)j * (size_t)nv;
                    for (int q = 0; q < nv; q++) if (me[q]) { Value *ev = v_num(); ca_set_ui(ev->num, me[q], am_ca); t = v_mul(t, v_pow(am_gen(vars[q]), ev)); }
                    ci = v_add(ci, t);
                }
                cof[i] = ci;
            }
            _fmpq_vec_clear(sol, nu ? nu : 1);
            used_D = D;
        }
        fmpq_clear(c); fmpq_mat_clear(M);
        free(rows); for (int i = 0; i < k; i++) free(um[i]); free(um); free(un); free(off);
    }
    if (!cof) {
        am_status(S_UNKNOWN, "no cofactors up to degree %ld (g may not follow from the hypotheses, or needs higher degree)", (long)(dmax + 6));
        am_fact("found", "false");
        free(all);
        return v_str("no certificate found");
    }
    /* the check: g = sum c_i h_i exactly */
    Value *sum = v_num();
    for (int i = 0; i < k; i++) sum = v_add(sum, v_mul(cof[i], all[i + 1]));
    Value *d = v_sub(sum, all[0]);
    int zero = (d->kind == V_NUM && ca_check_is_zero(d->num, am_ca) == T_TRUE) || (d->kind == V_RF && fmpz_mpoly_q_is_zero(d->rf, am_mp));
    if (!zero) am_fail("internal: the cofactors do not reproduce g");
    am_status(S_PROVED, "g = c_1 h_1 + ... + c_k h_k, checked by expanding; so g = 0 wherever every h_i = 0");
    am_fact("degree_bound", "%ld", (long)used_D);
    Value *out = v_list(k);
    for (int i = 0; i < k; i++) out->items[i] = cof[i];
    if (am_lean) {                                              /* the Lean 4 proof */
        char *vs = am_lean_vars(vars, nv);
        size_t cap = 4096;
        char *L = malloc(cap); size_t len = 0;
        #define LPUT(...) do { int n_ = snprintf(NULL, 0, __VA_ARGS__); while (len + (size_t)n_ + 1 > cap) { cap *= 2; L = realloc(L, cap); } len += (size_t)sprintf(L + len, __VA_ARGS__); } while (0)
        LPUT("example %s", vs);
        for (int i = 0; i < k; i++) {
            Value *h = a[1]->items[i];
            char *ls = v_str_of(h->kind == V_EQ ? h->items[0] : h), *rs = h->kind == V_EQ ? v_str_of(h->items[1]) : strdup("0");
            LPUT("(h%d : %s = %s) ", i + 1, ls, rs);
            free(ls); free(rs);
        }
        char *gl = v_str_of(a[0]->kind == V_EQ ? a[0]->items[0] : a[0]), *gr = a[0]->kind == V_EQ ? v_str_of(a[0]->items[1]) : strdup("0");
        LPUT(":\n    %s = %s := by\n  linear_combination ", gl, gr);
        free(gl); free(gr);
        int first = 1;
        for (int i = 0; i < k; i++) {
            if (cof[i]->kind == V_NUM && ca_check_is_zero(cof[i]->num, am_ca) == T_TRUE) continue;
            char *cs = v_str_of(cof[i]);
            LPUT("%s(%s) * h%d", first ? "" : " + ", cs, i + 1);
            free(cs);
            first = 0;
        }
        if (first) LPUT("0");
        #undef LPUT
        am_lean_fact(L);
        free(L); free(vs);
    }
    free(cof); free(all);
    return out;
}
