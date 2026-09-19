/* rtm_levels_batch.c -- rank machines (lines "PASS mask=M beta=..." on stdin) by the growth of per-local-type
 * level overheads v_j(tau) = n_{j+1}(tau) - 2 n_j(tau) (binary) on the anchored zero tape, for the start with
 * the most frontier advances. A hierarchy with bounded junctions gives bounded v; linear walks give growing v.
 * Output: "RANK maxv_late=<max |v| over the last 3 levels> maxv_mid=<max |v| over 3 levels, 4 earlier>
 *          ratio=<t_last/t_prev> mask=.. beta=..".  Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_levels_batch n g steps
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXJ 40
int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]); long steps = atol(argv[3]);
    int m = n * g, NT = 2 * n * g * g * g;
    long W = 1L << 21; unsigned char *tape = malloc(W);
    long *cnt = malloc(NT * sizeof(long));
    long (*snap)[1024] = malloc(MAXJ * sizeof *snap), (*snapl)[1024] = malloc(MAXJ * sizeof *snapl);
    long (*best)[1024] = malloc(MAXJ * sizeof *best);
    char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        if (strncmp(line, "PASS", 4)) continue;
        line[strcspn(line, "\n")] = 0;
        int mask; char *b = strstr(line, "beta="); if (!b) continue; sscanf(line, "PASS mask=%d", &mask);
        int perm[128]; char *p = b + 5;
        for (int i = 0; i < m; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
        int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
        int bestn = 0; long bt[MAXJ];
        for (int st = 0; st < n; st++) for (int ph0 = 0; ph0 < 2; ph0++) {
            memset(tape, 0, W); memset(cnt, 0, NT * sizeof(long));
            long h = W / 2; tape[h] = 1; int s = st, phase = ph0;
            long maxr = h, minl = h; int nj = 0, njl = 0; long tj[MAXJ], tjl[MAXJ];
            for (long t = 0; t < steps; t++) {
                int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
                cnt[tau]++;
                if (phase == 1) { h += dir[s]; phase = 0; }
                else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
                if (h <= 2 || h >= W - 3) break;
                if (h > maxr) { maxr = h; if (nj < MAXJ) { tj[nj] = t + 1; memcpy(snap[nj], cnt, NT * sizeof(long)); nj++; } }
                if (h < minl) { minl = h; if (njl < MAXJ) { tjl[njl] = t + 1; memcpy(snapl[njl], cnt, NT * sizeof(long)); njl++; } }
            }
            if (nj > bestn) { bestn = nj; memcpy(bt, tj, sizeof tj); memcpy(best, snap, MAXJ * sizeof *snap); }
            if (njl > bestn) { bestn = njl; memcpy(bt, tjl, sizeof tjl); memcpy(best, snapl, MAXJ * sizeof *snapl); }
        }
        if (bestn < 10) continue;
        long late = 0, mid = 0;
        for (int j = bestn - 4; j < bestn - 1; j++) for (int tau = 0; tau < NT; tau++) {
            long v = best[j + 1][tau] - 2 * best[j][tau]; if (v < 0) v = -v; if (v > late) late = v; }
        for (int j = bestn - 8; j < bestn - 5; j++) for (int tau = 0; tau < NT; tau++) {
            long v = best[j + 1][tau] - 2 * best[j][tau]; if (v < 0) v = -v; if (v > mid) mid = v; }
        printf("RANK maxv_late=%ld maxv_mid=%ld ratio=%.3f levels=%d mask=%d beta=%s\n", late, mid,
               (double)bt[bestn - 1] / bt[bestn - 2], bestn, mask, b + 5);
        fflush(stdout);
    }
    printf("RTM_LEVELS_BATCH_DONE\n");
    return 0;
}
