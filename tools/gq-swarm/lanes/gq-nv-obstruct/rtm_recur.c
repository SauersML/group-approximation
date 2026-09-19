/* rtm_recur.c -- return-time test for a continuous m-adic phase. Simulate from the anchored zero tape; take
 * the configuration y at the first Y-time >= t1 (Y = local types listed in yt.txt), and print every later
 * Y-time whose (state, cells within radius r) equals y's, with the induced index difference n and n mod m^j.
 * If U^n y -> y along returns with n not tending to 0 m-adically, U has no continuous m^j-th-root eigenvalue.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_recur n g mask beta start_state start_phase steps t1 r m maxprint
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]), mask = atoi(argv[3]); const char *bs = argv[4];
    int s = atoi(argv[5]), phase = atoi(argv[6]); long steps = atol(argv[7]), t1 = atol(argv[8]);
    int r = atoi(argv[9]), m = atoi(argv[10]), maxp = atoi(argv[11]);
    int perm[128]; const char *p = bs; for (int i = 0; i < n * g; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
    int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
    int NT = 2 * n * g * g * g; int *inY = calloc(NT, sizeof(int));
    FILE *f = fopen("yt.txt", "r"); int ph, st, a, l, rr, ny = 0;
    while (fscanf(f, "%d %d %d %d %d", &ph, &st, &a, &l, &rr) == 5) { inY[(((ph * n + st) * g + a) * g + l) * g + rr] = 1; ny++; }
    long W = 1L << 24; unsigned char *tape = calloc(W, 1); long h = W / 2; tape[h] = 1; long yi = 0;
    unsigned char *ref = malloc(2 * r + 1); int refstate = -1; long refyi = -1, reft = -1; int printed = 0;
    printf("Y types: %d  radius %d  modulus base %d\n", ny, r, m);
    for (long t = 0; t < steps; t++) {
        int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
        if (inY[tau]) {
            int cur = phase * n + s;
            if (refstate < 0 && t >= t1) { refstate = cur; memcpy(ref, tape + h - r, 2 * r + 1); refyi = yi; reft = t; printf("reference t=%ld induced=%ld\n", t, yi); }
            else if (refstate == cur && memcmp(ref, tape + h - r, 2 * r + 1) == 0) {
                long d = yi - refyi; long mj = 1; printf("return t=%ld n=%ld", t, d);
                for (int j = 1; j <= 6; j++) { mj *= m; printf(" mod%ld=%ld", mj, d % mj); }
                printf("\n");
                if (++printed >= maxp) break;
            }
            yi++;
        }
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int x = tape[h]; int idx = s * g + x; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
        if (h <= r + 2 || h >= W - r - 2) break;
    }
    printf("RTM_RECUR_DONE\n");
    return 0;
}
