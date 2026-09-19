/* rtm_gaps.c -- per-level gap profile of the induced map. Simulate from the anchored zero tape with Y = the local
 * types listed in yt.txt (one "ph st a l r" per line). At every right-frontier event (new rightmost head cell)
 * print: the level, the time, the induced index, the largest gap between consecutive Y-times since the previous
 * right-frontier event, the head extent (left, right) relative to the start cell, and, if print_tape is 1,
 * the visited tape with the head cell bracketed and the state.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_gaps n g mask beta start_state start_phase steps print_tape
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]), mask = atoi(argv[3]); const char *bs = argv[4];
    int s = atoi(argv[5]), phase = atoi(argv[6]); long steps = atol(argv[7]); int pt = atoi(argv[8]);
    int perm[128]; const char *p = bs; for (int i = 0; i < n * g; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
    int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
    int NT = 2 * n * g * g * g; int *inY = calloc(NT, sizeof(int));
    FILE *f = fopen("yt.txt", "r"); int ph, st, a, l, rr, ny = 0;
    while (fscanf(f, "%d %d %d %d %d", &ph, &st, &a, &l, &rr) == 5) { inY[(((ph * n + st) * g + a) * g + l) * g + rr] = 1; ny++; }
    long W = 1L << 20; unsigned char *tape = calloc(W, 1); long h0 = W / 2, h = h0; tape[h] = 1;
    long yi = 0, lastY = -1, gap = 0, maxr = h, minl = h; int lev = 0;
    printf("Y types read: %d\n", ny);
    for (long t = 0; t < steps; t++) {
        int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
        if (inY[tau]) { if (lastY >= 0 && t - lastY > gap) gap = t - lastY; lastY = t; yi++; }
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int x = tape[h]; int idx = s * g + x; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
        if (h <= 64 || h >= W - 64) break;
        if (h < minl) minl = h;
        if (h > maxr) {
            maxr = h; lev++;
            printf("lev=%d t=%ld Y=%ld maxgap=%ld extent=[%ld,%ld]", lev, t + 1, yi, gap, minl - h0, maxr - h0);
            if (pt) { printf(" state=(%d,%d) tape=", phase, s); for (long c = minl; c <= maxr; c++) printf(c == h ? "[%d]" : "%d", tape[c]); }
            printf("\n"); gap = 0;
        }
    }
    printf("RTM_GAPS_DONE\n");
    return 0;
}
