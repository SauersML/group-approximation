/* rtm_certcheck.c -- independent check of a phase-conflict certificate: re-simulate the machine from the
 * anchored zero tape and print, at times t1 and t2, the state and the cells within radius r of the head, and
 * the number of Y-times strictly before each (the induced index). Y is given as an explicit list of local types
 * (phase,state,head,left,right) read from a file "yt.txt" (one "ph st a l r" per line).
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_certcheck n g mask beta start_state start_phase t1 t2 r
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]), mask = atoi(argv[3]); const char *bs = argv[4];
    int s = atoi(argv[5]), phase = atoi(argv[6]); long t1 = atol(argv[7]), t2 = atol(argv[8]); int r = atoi(argv[9]);
    int perm[128]; const char *p = bs; for (int i = 0; i < n * g; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
    int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
    int NT = 2 * n * g * g * g; int *inY = calloc(NT, sizeof(int));
    FILE *f = fopen("yt.txt", "r"); int ph, st, a, l, rr, ny = 0;
    while (fscanf(f, "%d %d %d %d %d", &ph, &st, &a, &l, &rr) == 5) { inY[(((ph * n + st) * g + a) * g + l) * g + rr] = 1; ny++; }
    long W = 1L << 23; unsigned char *tape = calloc(W, 1); long h = W / 2; tape[h] = 1; long yi = 0;
    printf("Y types read: %d\n", ny);
    for (long t = 0; t <= t2; t++) {
        int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
        if (t == t1 || t == t2) {
            printf("t=%ld inY=%d induced_index=%ld mod4=%ld mod8=%ld state=(%d,%d) window:", t, inY[tau], yi, yi % 4, yi % 8, phase, s);
            for (long c = h - r; c <= h + r; c++) printf("%d", tape[c]); printf("\n");
        }
        if (inY[tau]) yi++;
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int x = tape[h]; int idx = s * g + x; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
    }
    printf("RTM_CERTCHECK_DONE\n");
    return 0;
}
