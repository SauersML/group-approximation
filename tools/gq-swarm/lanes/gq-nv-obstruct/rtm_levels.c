/* rtm_levels.c -- for one machine, run from an anchored zero tape and tabulate, for each local type
 * tau = (phase, state, head symbol, left symbol, right symbol), the counts n_j(tau) of steps of that type in
 * the prefix [0, t_j), where t_j is the j-th first-visit time of a new cell on the growth side.
 * Then v_j(tau) = n_{j+1}(tau) - 2 n_j(tau) measures the per-level overhead of that type.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_levels n g mask beta_csv start_state start_phase steps
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]), mask = atoi(argv[3]);
    const char *bs = argv[4]; int s = atoi(argv[5]), phase = atoi(argv[6]); long steps = atol(argv[7]);
    int m = n * g, perm[128]; const char *p = bs;
    for (int i = 0; i < m; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
    int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
    long W = 1L << 23; unsigned char *tape = calloc(W, 1); long h = W / 2; tape[h] = 1;
    int NT = 2 * n * g * g * g; long *cnt = calloc(NT, sizeof(long));
    long maxr = h, minl = h; int side = 0; long tj[64], tjl[64]; int nj = 0, njl = 0;
    long (*snap)[4096] = malloc(64 * sizeof *snap); /* counts snapshot at each t_j (NT <= 4096) */
    long (*snapl)[4096] = malloc(64 * sizeof *snapl);
    for (long t = 0; t < steps; t++) {
        int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
        cnt[tau]++;
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
        if (h <= 2 || h >= W - 3) break;
        if (h > maxr) { maxr = h; if (nj < 64) { tj[nj] = t + 1; memcpy(snap[nj], cnt, NT * sizeof(long)); nj++; } }
        if (h < minl) { minl = h; if (njl < 64) { tjl[njl] = t + 1; memcpy(snapl[njl], cnt, NT * sizeof(long)); njl++; } }
    }
    if (njl > nj) { nj = njl; memcpy(tj, tjl, sizeof tj); memcpy(snap, snapl, 64 * sizeof *snap); side = -1; } else side = 1;
    printf("frontier(%s side):", side > 0 ? "right" : "left");
    for (int j = 0; j < nj; j++) printf(" %ld", tj[j]); printf("\n");
    /* overhead vectors */
    for (int tau = 0; tau < NT; tau++) {
        if (snap[nj - 1][tau] == 0) continue;
        int ph = tau / (n * g * g * g), rest = tau % (n * g * g * g);
        int st = rest / (g * g * g), a = (rest / (g * g)) % g, l = (rest / g) % g, r = rest % g;
        printf("tau ph=%d st=%d a=%d l=%d r=%d  n_last=%ld  v:", ph, st, a, l, r, snap[nj - 1][tau]);
        for (int j = 2; j + 1 < nj; j++) printf(" %ld", snap[j + 1][tau] - 2 * snap[j][tau]);
        printf("\n");
    }
    printf("RTM_LEVELS_DONE\n");
    return 0;
}
