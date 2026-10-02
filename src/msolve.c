/* Polynomial systems with msolve (Berthomieu, Eder, Safey El Din): Groebner bases by F4 over prime fields,
 * multi-modular lifting, and a rational parametrization of the solutions:
 *     w(t) = 0,   x_i = -v_i(t) / (c_i w'(t)).
 * msolve's own command-line entry is linked into this program and run in a child process, with its input and
 * output in memory files: a failure or a time limit in msolve cannot take this process down, and nothing is
 * written to disk. */
#define _GNU_SOURCE
#include "am.h"

#include <ctype.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#include "msolve_bridge.h"

int msolve_main(int argc, char **argv);

/* run msolve on `input`; its output, malloc'd */
static char *run(const char *input, int seconds) {
    int in = memfd_create("amath-msolve-in", 0), out = memfd_create("amath-msolve-out", 0);
    if (in < 0 || out < 0) am_fail("solve: cannot create memory files for msolve");
    size_t len = strlen(input);
    if (write(in, input, len) != (ssize_t)len) am_fail("solve: cannot pass the system to msolve");
    fflush(stdout);
    pid_t pid = fork();
    if (pid < 0) am_fail("solve: cannot start msolve");
    if (pid == 0) {
        alarm((unsigned)seconds);
        int devnull = open("/dev/null", 1);
        if (devnull >= 0) { dup2(devnull, 1); dup2(devnull, 2); }
        char fin[64], fout[64];
        snprintf(fin, sizeof fin, "/proc/self/fd/%d", in);
        snprintf(fout, sizeof fout, "/proc/self/fd/%d", out);
        char *argv[] = {"msolve", "-f", fin, "-o", fout, "-P", "1", NULL};
        _exit(msolve_main(7, argv) == 0 ? 0 : 3);
    }
    int st;
    waitpid(pid, &st, 0);
    close(in);
    if (WIFSIGNALED(st)) {
        close(out);
        if (WTERMSIG(st) == SIGALRM) am_fail("solve: msolve did not finish within %d s", seconds);
        am_fail("solve: msolve stopped (signal %d)", WTERMSIG(st));
    }
    if (!WIFEXITED(st) || WEXITSTATUS(st) != 0) { close(out); am_fail("solve: msolve could not handle this system"); }
    off_t n = lseek(out, 0, SEEK_END);
    lseek(out, 0, SEEK_SET);
    char *s = malloc((size_t)n + 1);
    ssize_t got = read(out, s, (size_t)n);
    s[got > 0 ? got : 0] = 0;
    close(out);
    return s;
}

/* ---------------- msolve's output: nested lists of integers, a / 2^k, a/b, and 'names' ---------------- */

typedef struct MNode MNode;
struct MNode { int list; MNode **kids; int n; fmpq_t q; char *name; };

static const char *mp;
static void ws(void) { while (*mp && isspace((unsigned char)*mp)) mp++; }
static MNode *mnode(void) {
    ws();
    MNode *m = calloc(1, sizeof *m);
    fmpq_init(m->q);
    if (*mp == '[') {
        mp++; m->list = 1; ws();
        while (*mp && *mp != ']') {
            m->kids = realloc(m->kids, (size_t)(m->n + 1) * sizeof *m->kids);
            m->kids[m->n++] = mnode();
            ws();
            if (*mp == ',') mp++;
            ws();
        }
        if (*mp == ']') mp++;
        return m;
    }
    if (*mp == '\'') {
        const char *e = strchr(mp + 1, '\'');
        if (!e) am_fail("solve: unreadable msolve output");
        m->name = strndup(mp + 1, (size_t)(e - mp - 1));
        mp = e + 1;
        return m;
    }
    const char *st = mp;
    if (*mp == '-') mp++;
    while (isdigit((unsigned char)*mp)) mp++;
    if (mp == st) am_fail("solve: unreadable msolve output near '%.20s'", st);
    char *num = strndup(st, (size_t)(mp - st));
    fmpz_t a, b; fmpz_init(a); fmpz_init_set_ui(b, 1);
    fmpz_set_str(a, num, 10); free(num);
    ws();
    if (*mp == '/') {
        mp++; ws();
        if (mp[0] == '2' && mp[1] == '^') { mp += 2; long k = strtol(mp, (char **)&mp, 10); fmpz_mul_2exp(b, b, (ulong)k); }
        else { const char *s2 = mp; while (isdigit((unsigned char)*mp)) mp++; char *d = strndup(s2, (size_t)(mp - s2)); fmpz_set_str(b, d, 10); free(d); }
    }
    fmpq_set_fmpz_frac(m->q, a, b);
    fmpz_clear(a); fmpz_clear(b);
    return m;
}
static void mfree(MNode *m) {
    if (!m) return;
    for (int i = 0; i < m->n; i++) mfree(m->kids[i]);
    free(m->kids); free(m->name); fmpq_clear(m->q); free(m);
}
static MNode *kid(MNode *m, int i) {
    if (!m || !m->list || i >= m->n) am_fail("solve: unexpected shape of msolve output");
    return m->kids[i];
}
static void to_poly(fmpz_poly_t p, MNode *pair) {          /* [deg, [c0, c1, ...]] */
    MNode *c = kid(pair, 1);
    fmpz_poly_zero(p);
    for (int i = 0; i < c->n; i++) fmpz_poly_set_coeff_fmpz(p, i, fmpq_numref(c->kids[i]->q));
}

void am_msolve(MsolveResult *R, const char *input, int seconds) {
    memset(R, 0, sizeof *R);
    char *out = run(input, seconds);
    mp = out;
    MNode *root = mnode();
    free(out);
    int dim = fmpz_get_si(fmpq_numref(kid(root, 0)->q));
    if (dim == -1) { R->kind = -1; mfree(root); return; }
    if (dim > 0) { R->kind = 1; mfree(root); return; }
    MNode *P = kid(root, 1), *reals = root->n > 2 ? kid(root, 2) : NULL;
    R->nvars = (int)fmpz_get_si(fmpq_numref(kid(P, 1)->q));
    MNode *names = kid(P, 3), *lf = kid(P, 4), *body = kid(kid(P, 5), 1);
    R->names = calloc((size_t)R->nvars, sizeof(char *));
    R->lf = _fmpq_vec_init(R->nvars);
    for (int i = 0; i < R->nvars; i++) { R->names[i] = strdup(kid(names, i)->name ? kid(names, i)->name : "?"); fmpq_set(R->lf + i, kid(lf, i)->q); }
    fmpz_poly_init(R->w); fmpz_poly_init(R->wd);
    to_poly(R->w, kid(body, 0));
    to_poly(R->wd, kid(body, 1));
    MNode *co = kid(body, 2);
    R->ncoord = co->n;
    R->v = calloc((size_t)(co->n ? co->n : 1), sizeof(fmpz_poly_struct));
    R->c = _fmpz_vec_init(co->n ? co->n : 1);
    for (int i = 0; i < co->n; i++) {
        fmpz_poly_init(R->v + i);
        to_poly(R->v + i, kid(kid(co, i), 0));
        fmpz_set(R->c + i, fmpq_numref(kid(kid(co, i), 1)->q));
    }
    R->nreal = reals && reals->n > 1 ? kid(reals, 1)->n : 0;
    mfree(root);
}

void am_msolve_clear(MsolveResult *R) {
    if (R->kind != 0) return;
    for (int i = 0; i < R->nvars; i++) free(R->names[i]);
    free(R->names);
    _fmpq_vec_clear(R->lf, R->nvars);
    fmpz_poly_clear(R->w); fmpz_poly_clear(R->wd);
    for (int i = 0; i < R->ncoord; i++) fmpz_poly_clear(R->v + i);
    free(R->v);
    _fmpz_vec_clear(R->c, R->ncoord ? R->ncoord : 1);
}
