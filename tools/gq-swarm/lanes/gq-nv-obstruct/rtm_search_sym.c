/* rtm_search_sym.c -- as rtm_search.c, restricted to space-symmetric machines (like SMART):
 * states come in mirror pairs (2i, 2i+1) with opposite directions, and beta commutes with the mirror
 * iota(state) = state ^ 1 (symbols unchanged). Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_search_sym n g Lmax   (n even)
 * Output lines "PASS mask=M beta=..." in the same format as rtm_search.c (full beta over all n*g inputs).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, g, Lmax;
static int dir[16];
static int betaS[128], betaB[128];
static unsigned char *seen;
static int cyclen[64];

static long ipow(int b, int e) { long r = 1; while (e--) r *= b; return r; }

static long step(long cfg, int L, long T, const long *pw) {
    long tape = cfg % T; cfg /= T;
    int pos = cfg % L; cfg /= L;
    int st = cfg % n; int ph = cfg / n;
    if (ph == 1) { pos = (pos + dir[st] + L) % L; return ((0L * n + st) * L + pos) * T + tape; }
    int a = (tape / pw[pos]) % g; int idx = st * g + a;
    int j = betaS[idx], b = betaB[idx];
    tape += (long)(b - a) * pw[pos];
    return ((1L * n + j) * L + pos) * T + tape;
}

static int test(int L, int verbose) {
    long T = ipow(g, L), N = 2L * n * L * T;
    long pw[16]; for (int c = 0; c < L; c++) pw[c] = ipow(g, c);
    memset(seen, 0, N);
    int ncyc = 0; long minlen = N;
    for (long s = 0; s < N; s++) {
        if (seen[s]) continue;
        long c = s, len = 0;
        while (!seen[c]) { seen[c] = 1; len++; c = step(c, L, T, pw); }
        if (c != s) return 0;
        if (len < minlen) minlen = len;
        if (ncyc < 64) cyclen[ncyc] = (int)len;
        if (++ncyc > n) return 0;
    }
    if (minlen < L * T) return 0;
    if (verbose) { printf("   L=%d cycles=%d lens:", L, ncyc); for (int i = 0; i < ncyc && i < 64; i++) printf(" %d", cyclen[i]); printf("\n"); }
    return 1;
}

static int next_perm(int *a, int m) {
    int i = m - 2; while (i >= 0 && a[i] >= a[i + 1]) i--; if (i < 0) return 0;
    int j = m - 1; while (a[j] <= a[i]) j--; int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = m - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
    return 1;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); g = atoi(argv[2]); Lmax = atoi(argv[3]);
    int onlydm = argc > 4 ? atoi(argv[4]) : -1;
    int h = n / 2, m = h * g; /* even inputs (2i, a), i < h; output orbits {(2j,b),(2j+1,b)} */
    seen = malloc(2L * n * Lmax * ipow(g, Lmax));
    long tried = 0, passed = 0;
    int ord[64];
    for (int dm = 0; dm < (1 << h); dm++) {
        if (onlydm >= 0 && dm != onlydm) continue;
        for (int i = 0; i < h; i++) { dir[2 * i] = (dm >> i & 1) ? +1 : -1; dir[2 * i + 1] = -dir[2 * i]; }
        for (int i = 0; i < m; i++) ord[i] = i;
        do {
            for (int bits = 0; bits < (1 << m); bits++) {
                for (int e = 0; e < m; e++) {
                    int i = e / g, a = e % g;            /* even input (2i, a) */
                    int orb = ord[e], j = orb / g, b = orb % g;
                    int pick = bits >> e & 1;           /* which element of the output orbit */
                    int jj = 2 * j + pick;
                    betaS[(2 * i) * g + a] = jj;         betaB[(2 * i) * g + a] = b;
                    betaS[(2 * i + 1) * g + a] = jj ^ 1; betaB[(2 * i + 1) * g + a] = b;
                }
                tried++;
                int ok = 1;
                for (int L = 1; L <= Lmax && ok; L++) ok = test(L, 0);
                if (ok) {
                    passed++;
                    int mask = 0; for (int i = 0; i < n; i++) if (dir[i] > 0) mask |= 1 << i;
                    printf("PASS mask=%d beta=", mask);
                    for (int x = 0; x < n * g; x++) printf("%d%s", betaS[x] * g + betaB[x], x + 1 < n * g ? "," : "");
                    printf("\n");
                    test(Lmax, 1); fflush(stdout);
                }
            }
        } while (next_perm(ord, m));
    }
    printf("sym n=%d g=%d Lmax=%d tried=%ld passed=%ld\nRTM_SEARCH_DONE\n", n, g, Lmax, tried, passed);
    return 0;
}
