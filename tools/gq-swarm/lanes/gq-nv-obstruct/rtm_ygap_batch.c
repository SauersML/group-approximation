/* rtm_ygap_batch.c -- the bounded-junction filter, for every candidate (lines "PASS mask=M beta=... start=S" on
 * stdin), independent of the overhead of non-Y types. Run the scanned start from the anchored zero tape; take the
 * frontier side with ratio about 2 and the most advances; let Y = the local types whose overhead
 * n_{j+1} - 2 n_j vanishes on the last L levels (and which occur); then from the stored type sequence compute the
 * largest gap between consecutive Y-times inside each frontier interval.
 * Output (only when Y is nonempty): "YGAP ny=<|Y|> late=<max gap, last 3 intervals> early=<max gap, the 3
 * intervals before> levels=<advances> mask=.. beta=.. start=..". Last line: "YGAP_DONE seen=.. withY=..".
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Optional D (default 3): the early window is the 3 intervals ending D intervals before the last.
 * Usage: rtm_ygap_batch n g steps L [D]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXJ 40
int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]); long steps = atol(argv[3]); int L = atoi(argv[4]), D = argc > 5 ? atoi(argv[5]) : 3;
    int m = n * g, NT = 2 * n * g * g * g;
    long W = 1L << 21; unsigned char *tape = malloc(W);
    long *cnt = malloc(NT * sizeof(long)); unsigned short *seq = malloc(steps * sizeof(unsigned short));
    long (*snap)[1024] = malloc(MAXJ * sizeof *snap), (*snapl)[1024] = malloc(MAXJ * sizeof *snapl);
    char *inY = malloc(NT); long seen = 0, withY = 0;
    char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        if (strncmp(line, "PASS", 4)) continue;
        line[strcspn(line, "\n")] = 0;
        int mask; char *b = strstr(line, "beta="); if (!b) continue; sscanf(line, "PASS mask=%d", &mask);
        int perm[128]; char *p = b + 5;
        for (int i = 0; i < m; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
        int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
        int st = 0; { char *q = strstr(line, "start="); if (q) st = atoi(q + 6); }
        seen++;
        memset(tape, 0, W); memset(cnt, 0, NT * sizeof(long));
        long h = W / 2; tape[h] = 1; int s = st, phase = 0;
        long maxr = h, minl = h; int nj = 0, njl = 0; long tj[MAXJ], tjl[MAXJ], T = 0;
        for (long t = 0; t < steps; t++) {
            int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
            cnt[tau]++; seq[t] = (unsigned short)tau; T = t + 1;
            if (phase == 1) { h += dir[s]; phase = 0; }
            else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
            if (h <= 2 || h >= W - 3) break;
            if (h > maxr) { maxr = h; if (nj < MAXJ) { tj[nj] = t + 1; memcpy(snap[nj], cnt, NT * sizeof(long)); nj++; } }
            if (h < minl) { minl = h; if (njl < MAXJ) { tjl[njl] = t + 1; memcpy(snapl[njl], cnt, NT * sizeof(long)); njl++; } }
        }
        int okr = nj >= 10 && (double)tj[nj-1]/tj[nj-2] > 1.8 && (double)tj[nj-1]/tj[nj-2] < 2.25;
        int okl = njl >= 10 && (double)tjl[njl-1]/tjl[njl-2] > 1.8 && (double)tjl[njl-1]/tjl[njl-2] < 2.25;
        long *bt; long (*bs)[1024]; int bn;
        if (okr && (!okl || nj >= njl)) { bt = tj; bs = snap; bn = nj; }
        else if (okl) { bt = tjl; bs = snapl; bn = njl; }
        else continue;
        int ny = 0;
        for (int tau = 0; tau < NT; tau++) {
            int ok = bs[bn - 1][tau] > 0;
            for (int j = bn - 1 - L; j < bn - 1 && ok; j++) if (bs[j + 1][tau] - 2 * bs[j][tau] != 0) ok = 0;
            inY[tau] = ok; ny += ok;
        }
        if (!ny) continue;
        withY++;
        long late = 0, early = 0, lastY = -1; int k = 0;   /* k = index of the frontier interval containing t */
        for (long t = 0; t < T; t++) {
            while (k < bn && t >= bt[k]) k++;
            if (!inY[seq[t]]) continue;
            if (lastY >= 0) { long gp = t - lastY;
                if (k >= bn - 3 && k < bn && gp > late) late = gp;
                if (k >= bn - 3 - D && k < bn - D && gp > early) early = gp; }
            lastY = t;
        }
        printf("YGAP ny=%d late=%ld early=%ld levels=%d mask=%d beta=%s\n", ny, late, early, bn, mask, b + 5);
        fflush(stdout);
    }
    printf("YGAP_DONE seen=%ld withY=%ld\n", seen, withY);
    return 0;
}
