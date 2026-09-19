/* rtm_search.c -- search small reversible Turing machines (Kari--Ollinger model, SMART's format)
 * for "complete counter" behaviour on cyclic tapes, as candidates for a binary SMART analogue.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only; single core.
 *
 * Model: n move states q2_i (i < n) with direction dir[i] in {+1,-1}: q2_i --dir--> q1_i;
 *        n symbol states q1_i: bijection beta: (i, a) -> (j, b) meaning q1_i reads a, writes b, goes to q2_j.
 *        Alphabet size g. Configuration on a cyclic tape of length L: (phase, state, pos, tape).
 * Test: for L = 1..Lmax the induced permutation on the 2*n*L*g^L configurations has all cycles of length
 *        >= L*g^L (so every cycle visits at least as many configurations as (pos, tape) pairs), and
 *        at most n cycles. SMART (n = 4, g = 3) passes with exactly 4 cycles of length 2*L*3^L.
 * Output: machines passing up to Lmax, with the cycle lengths at Lmax.
 * Usage: rtm_search n g Lmax [dirmask_filter]   (enumerates all dir masks and all beta permutations)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, g, Lmax;
static int dir[8];
static int betaS[64], betaB[64]; /* index i*g+a -> (state j, write b) */
static int perm[64];
static unsigned char *seen;
static int *cyclen;

static long ipow(int b, int e) { long r = 1; while (e--) r *= b; return r; }

/* config encoding: ((phase*n + state)*L + pos)*T + tape, tape in base g, cell c digit = (tape / g^c) % g */
static long step(long cfg, int L, long T, const long *pw) {
    long tape = cfg % T; cfg /= T;
    int pos = cfg % L; cfg /= L;
    int st = cfg % n; int ph = cfg / n;
    if (ph == 1) { /* move state */
        pos = (pos + dir[st] + L) % L;
        return ((0L * n + st) * L + pos) * T + tape;
    } else {
        int a = (tape / pw[pos]) % g;
        int idx = st * g + a;
        int j = betaS[idx], b = betaB[idx];
        tape += (long)(b - a) * pw[pos];
        return ((1L * n + j) * L + pos) * T + tape;
    }
}

static int test(int L, int verbose) {
    long T = ipow(g, L);
    long N = 2L * n * L * T;
    long pw[16]; for (int c = 0; c < L; c++) pw[c] = ipow(g, c);
    memset(seen, 0, N);
    int ncyc = 0; long minlen = N;
    for (long s = 0; s < N; s++) {
        if (seen[s]) continue;
        long c = s, len = 0;
        while (!seen[c]) { seen[c] = 1; len++; c = step(c, L, T, pw); }
        if (c != s) return 0; /* not a permutation (should not happen for bijective beta) */
        if (len < minlen) minlen = len;
        if (ncyc < 64) cyclen[ncyc] = (int)len;
        ncyc++;
        if (ncyc > n) return 0;
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
    int onlymask = argc > 4 ? atoi(argv[4]) : -1;
    const char *calib = argc > 5 ? argv[5] : NULL;
    int m = n * g;
    long maxN = 2L * n * Lmax * ipow(g, Lmax);
    seen = malloc(maxN); cyclen = malloc(64 * sizeof(int));
    long tried = 0, passed = 0;
    for (int mask = 0; mask < (1 << n); mask++) {
        if (onlymask >= 0 && mask != onlymask) continue;
        for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
        for (int i = 0; i < m; i++) perm[i] = i;
        if (calib) { const char *p = calib; for (int i = 0; i < m; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; } }
        do {
            for (int i = 0; i < m; i++) { betaS[i] = perm[i] / g; betaB[i] = perm[i] % g; }
            tried++;
            int ok = 1;
            for (int L = 1; L <= Lmax && ok; L++) ok = test(L, 0);
            if (ok) {
                passed++;
                printf("PASS mask=%d beta=", mask);
                for (int i = 0; i < m; i++) printf("%d%s", perm[i], i + 1 < m ? "," : "");
                printf("\n");
                test(Lmax, 1);
                fflush(stdout);
            }
        } while (!calib && next_perm(perm, m));
    }
    printf("n=%d g=%d Lmax=%d tried=%ld passed=%ld\nRTM_SEARCH_DONE\n", n, g, Lmax, tried, passed);
    return 0;
}
