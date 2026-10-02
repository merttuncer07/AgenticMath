/* amath: run statements from a file, from -e, or line by line; -j writes one JSON line per statement. */
#include "am.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static int run_stream(FILE *in, int interactive) {
    char *line = NULL;
    size_t cap = 0;
    int errors = 0;
    for (;;) {
        if (interactive) { fputs("> ", stdout); fflush(stdout); }
        if (getline(&line, &cap, in) < 0) break;
        int failed;
        char *out = am_run(line, &failed);
        if (out) { puts(out); free(out); }
        fflush(stdout);
        errors += failed;
    }
    free(line);
    if (interactive) putchar('\n');
    return errors;
}

int main(int argc, char **argv) {
    am_init();
    int i = 1;
    for (; i < argc && argv[i][0] == '-' && argv[i][1]; i++) {
        if (!strcmp(argv[i], "-j") || !strcmp(argv[i], "--json")) am_json = 1;
        else if (!strcmp(argv[i], "-e") && i + 1 < argc) {
            int failed;
            char *out = am_run(argv[++i], &failed);
            if (out) { puts(out); free(out); }
            return failed;
        } else {
            fprintf(stderr, "usage: amath [-j] [file | -e \"statement\"]\n  -j  one JSON line per statement\n");
            return 2;
        }
    }
    if (i < argc) {
        FILE *f = fopen(argv[i], "r");
        if (!f) { perror(argv[i]); return 2; }
        int errors = run_stream(f, 0);
        fclose(f);
        return errors ? 1 : 0;
    }
    return run_stream(stdin, isatty(0)) ? 1 : 0;
}
