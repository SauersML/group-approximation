/* rtm_scan_sym.c -- fast scan of mirror-symmetric reversible TMs (SMART format, n even, alphabet g) for
 * BINARY frontier timing on an anchored zero tape, without the cyclic completeness filter.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only; single core.
 * For each machine and each start (state 0 or 2, phase 0), run up to S steps on a tape that is 0 except
 * cell 0 = 1, record first-visit times t_1 < t_2 < ... of new cells (either side, whichever grows).
 * Candidate: at least J advances, and the last 4 ratios t_{j+1}/t_j lie in [1.8, 2.25].
 * Early exit: the head is more than R cells from 0 (linear motion), or no new cell for 4*(t_last+50) steps.
 * Usage: rtm_scan_sym n g S J R [ord_first_filter]   ord_first_filter splits the enumeration (value of ord[0]).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, g;
static int dir[16], betaS[128], betaB[128];

static int next_perm(int *a, int m) {
    int i = m - 2; while (i >= 0 && a[i] >= a[i + 1]) i--; if (i < 0) return 0;
    int j = m - 1; while (a[j] <= a[i]) j--; int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = m - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
    return 1;
}

#define W 4096
static unsigned char tape[W];

static int scan(long S, int J, int R, int st0, long *tj, int *njout) {
    memset(tape, 0, W);
    int h = W / 2; tape[h] = 1; int s = st0, phase = 0;
    int maxr = h, minl = h, nr = 0, nl = 0; long tr[64], tl[64]; long lastnew = 0;
    for (long t = 0; t < S; t++) {
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int a = tape[h]; int idx = s * g + a; tape[h] = betaB[idx]; s = betaS[idx]; phase = 1; }
        if (h - W / 2 > R || W / 2 - h > R) return 0;
        if (h > maxr) { maxr = h; if (nr < 64) tr[nr++] = t + 1; lastnew = t; }
        if (h < minl) { minl = h; if (nl < 64) tl[nl++] = t + 1; lastnew = t; }
        if (t - lastnew > 4 * (lastnew + 50)) break;
    }
    long *T = nr >= nl ? tr : tl; int nj = nr >= nl ? nr : nl;
    if (nj < J) return 0;
    for (int j = nj - 4; j < nj; j++) {
        double r = (double)T[j] / T[j - 1];
        if (r < 1.8 || r > 2.25) return 0;
    }
    for (int j = 0; j < nj; j++) tj[j] = T[j];
    *njout = nj;
    return 1;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); g = atoi(argv[2]); long S = atol(argv[3]); int J = atoi(argv[4]); int R = atoi(argv[5]);
    int f0 = argc > 6 ? atoi(argv[6]) : -1;
    int f1 = argc > 7 ? atoi(argv[7]) : -1;
    int h = n / 2, m = h * g;
    long tried = 0, cand = 0; int ord[64];
    for (int i = 0; i < h; i++) { dir[2 * i] = +1; dir[2 * i + 1] = -1; } /* one mask suffices up to relabeling */
    for (int i = 0; i < m; i++) ord[i] = i;
    do {
        if (f0 >= 0 && ord[0] != f0) continue;
        if (f1 >= 0 && ord[1] != f1) continue;
        for (int bits = 0; bits < (1 << m); bits++) {
            for (int e = 0; e < m; e++) {
                int i = e / g, a = e % g, orb = ord[e], j = orb / g, b = orb % g, jj = 2 * j + ((bits >> e) & 1);
                betaS[(2 * i) * g + a] = jj;       betaB[(2 * i) * g + a] = b;
                betaS[(2 * i + 1) * g + a] = jj ^ 1; betaB[(2 * i + 1) * g + a] = b;
            }
            tried++;
            for (int st0 = 0; st0 < n; st0 += 2) {
                long tj[64]; int nj;
                if (scan(S, J, R, st0, tj, &nj)) {
                    cand++;
                    printf("PASS mask=%d beta=", 0x5555 & ((1 << n) - 1));
                    for (int x = 0; x < n * g; x++) printf("%d%s", betaS[x] * g + betaB[x], x + 1 < n * g ? "," : "");
                    printf("  start=%d t:", st0);
                    for (int j = 0; j < nj && j < 20; j++) printf(" %ld", tj[j]);
                    printf("\n"); fflush(stdout);
                    break;
                }
            }
        }
    } while (next_perm(ord, m));
    printf("scan n=%d g=%d S=%ld tried=%ld cand=%ld\nRTM_SCAN_DONE\n", n, g, S, tried, cand);
    return 0;
}
