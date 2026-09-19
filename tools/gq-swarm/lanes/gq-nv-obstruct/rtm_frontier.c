/* rtm_frontier.c -- for candidate machines (lines "PASS mask=M beta=b0,b1,..." on stdin), simulate on a
 * Z-tape and print the first-visit times of new cells (the frontier), to detect hierarchical crossing times.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_frontier n g steps < survivors.txt
 * For each machine and each start (state s, phase), tape: all 0 except cell 0 = 1 (anchor), head at 0.
 * Prints: machine, start, and the times at which the right frontier reaches cells 1,2,3,... (up to 24),
 * and the successive ratios t(k+1)/t(k).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]); long steps = atol(argv[3]);
    int m = n * g;
    char line[4096];
    int W = 1 << 22; /* tape width */
    unsigned char *tape = malloc(W);
    while (fgets(line, sizeof line, stdin)) {
        if (strncmp(line, "PASS", 4)) continue;
        line[strcspn(line, "\n")] = 0;
        int mask; char *b = strstr(line, "beta="); if (!b) continue;
        sscanf(line, "PASS mask=%d", &mask);
        int perm[64]; char *p = b + 5;
        for (int i = 0; i < m; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
        int dir[8]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
        for (int st = 0; st < n; st++) for (int ph = 0; ph < 2; ph++) {
            memset(tape, 0, W);
            long h = W / 2; tape[h] = 1; int s = st, phase = ph;
            long maxr = h, minl = h; long tr[64]; int nr = 0; long tl[64]; int nl = 0;
            for (long t = 0; t < steps; t++) {
                if (phase == 1) { h += dir[s]; phase = 0; }
                else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
                if (h <= 1 || h >= W - 2) break;
                if (h > maxr) { maxr = h; if (nr < 64) tr[nr++] = t + 1; }
                if (h < minl) { minl = h; if (nl < 64) tl[nl++] = t + 1; }
            }
            printf("mask=%d beta=%s start=(%d,%d) right:", mask, b + 5, st, ph);
            /* strip newline in beta printing */
            for (int i = 0; i < nr && i < 24; i++) printf(" %ld", tr[i]);
            printf(" | left:");
            for (int i = 0; i < nl && i < 24; i++) printf(" %ld", tl[i]);
            printf("\n");
        }
    }
    printf("RTM_FRONTIER_DONE\n");
    return 0;
}
