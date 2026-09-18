/* Mean distance from a uniformly random word xi in {-1,1}^(2^k) to the
 * signed first-order Reed-Muller code RM(1,k), i.e. the quantity
 *
 *   delta_k = E_xi[ d(xi, RM(1,k)) ] / 2^k = 1/2 - E_xi[ max_i |W_i| ] / 2^(k+1),
 *   W_i = sum_a xi_a (-1)^(a.i),
 *
 * that enters the decoder-adversary bound R*(k) <= 1 + delta_k (3 - 2^(2-k))
 * of hadamard-gadget-deletion-ratio-window (item 3).  Also the punctured
 * version (positions a != 0 only, the (2^k-1)-ary Had'_k), normalised by
 * 2^k - 1.
 *
 * Exact mode (k <= 5): max_i |W_i| is invariant under multiplying xi by a
 * signed character (that permutes the |W_i|), and the positions
 * {0, e_1, ..., e_k} form an information set of RM(1,k), so every coset of
 * RM(1,k) has exactly one representative with xi = +1 there.  We enumerate
 * the 2^(2^k - k - 1) representatives by a Gray code, updating all W_i per
 * flip.  The punctured code is handled the same way with xi = +1 fixed on
 * {e_1..e_k} only (position 0 is absent): exactly two codewords are +1 there,
 * so each coset is hit twice, and the average is still exact because for
 * uniform xi the free part of xi*c (c the codeword matching xi on the e_c) is
 * uniform.  In both cases the average over the enumerated words equals the
 * average over all xi.
 *
 * Output: exact integer sums and the value as a fraction numerator /
 * denominator, then the kill test delta_k < 1/(3 - 4/K).
 *
 * Monte-Carlo mode (k = 6, 7; argument "mc"): an ESTIMATE only, with its
 * standard error.  Not used as proof of anything.
 *
 * Build: gcc -O2 -o rm1 rm1_mean_distance.c ; run: ./rm1 3 ; ./rm1 4 ; ./rm1 5
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static int parity(unsigned v) { return __builtin_popcount(v) & 1; }

static void exact(int k, int punct) {
    int K = 1 << k;
    int free_pos[64], nfree = 0;
    for (int a = 0; a < K; a++) {
        if (a == 0) continue;              /* in info set (full) or absent (punct) */
        if (__builtin_popcount((unsigned)a) == 1) continue;   /* e_c */
        free_pos[nfree++] = a;
    }
    int W[64];
    /* start: xi = +1 on all present positions */
    for (int i = 0; i < K; i++) {
        int s = 0;
        for (int a = punct ? 1 : 0; a < K; a++) s += parity(a & i) ? -1 : 1;
        W[i] = s;
    }
    int xi[64];
    for (int a = 0; a < K; a++) xi[a] = 1;
    uint64_t total = 0, count = 0;
    uint64_t hist[65];
    memset(hist, 0, sizeof hist);
    uint64_t n = 1ULL << nfree;
    for (uint64_t g = 0;; g++) {
        int m = 0;
        for (int i = 0; i < K; i++) { int v = W[i] < 0 ? -W[i] : W[i]; if (v > m) m = v; }
        total += (uint64_t)m; count++; hist[m]++;
        if (g + 1 == n) break;
        int b = __builtin_ctzll(g + 1);
        int a = free_pos[b];
        int d = -2 * xi[a];
        xi[a] = -xi[a];
        for (int i = 0; i < K; i++) W[i] += parity(a & i) ? -d : d;
    }
    int L = punct ? K - 1 : K;             /* code length */
    /* E[d] = (L - E[max|W|]) / 2 ; delta = E[d] / L */
    /* delta = (L*count - total) / (2 L count) */
    uint64_t num = (uint64_t)L * count - total, den = 2ULL * (uint64_t)L * count;
    uint64_t x = num, y = den; while (y) { uint64_t t = x % y; x = y; y = t; }
    double delta = (double)num / (double)den;
    double thr = 1.0 / (3.0 - 4.0 / K);
    printf("k=%d %s: length %d, cosets %llu, sum max|W| = %llu, E[max|W|] = %.10f\n",
           k, punct ? "punctured (Had'_k)" : "full (Had_k, Def 2.24)", L,
           (unsigned long long)count, (unsigned long long)total, (double)total / count);
    printf("   delta_k = %llu/%llu = %.10f ; bound 1+delta(3-4/K) = %.10f ; kill threshold 1/(3-4/K) = %.10f ; kill: %s\n",
           (unsigned long long)(num / x), (unsigned long long)(den / x), delta,
           1.0 + delta * (3.0 - 4.0 / K), thr, delta < thr ? "YES" : "no");
    printf("   distribution of max|W| over cosets:");
    for (int v = 0; v <= K; v++) if (hist[v]) printf(" %d:%llu", v, (unsigned long long)hist[v]);
    printf("\n");
}

static uint64_t rng = 0x9E3779B97F4A7C15ULL;
static uint64_t next64(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void mc(int k, long trials) {
    int K = 1 << k;
    double s = 0, s2 = 0;
    int xi[128], W[128];
    for (long t = 0; t < trials; t++) {
        for (int a = 0; a < K; a += 64) {
            uint64_t r = next64();
            for (int b = 0; b < 64 && a + b < K; b++) xi[a + b] = (r >> b) & 1 ? -1 : 1;
        }
        memcpy(W, xi, sizeof(int) * K);
        for (int h = 1; h < K; h <<= 1)
            for (int i = 0; i < K; i += 2 * h)
                for (int j = i; j < i + h; j++) { int u = W[j], v = W[j + h]; W[j] = u + v; W[j + h] = u - v; }
        int m = 0;
        for (int i = 0; i < K; i++) { int v = W[i] < 0 ? -W[i] : W[i]; if (v > m) m = v; }
        s += m; s2 += (double)m * m;
    }
    double mean = s / trials, var = s2 / trials - mean * mean;
    double se = sqrt(var / trials);
    double delta = 0.5 - mean / (2.0 * K), dse = se / (2.0 * K);
    double thr = 1.0 / (3.0 - 4.0 / K);
    printf("k=%d MC ESTIMATE (%ld trials): E[max|W|] = %.4f +- %.4f ; delta_k = %.5f +- %.5f ; bound %.5f ; threshold %.5f\n",
           k, trials, mean, se, delta, dse, 1.0 + delta * (3.0 - 4.0 / K), thr);
}

int main(int argc, char **argv) {
    int k = argc > 1 ? atoi(argv[1]) : 3;
    if (argc > 2 && strcmp(argv[2], "mc") == 0) {
        mc(k, argc > 3 ? atol(argv[3]) : 10000000L);
        return 0;
    }
    if (k > 5) { fprintf(stderr, "exact mode needs k <= 5\n"); return 1; }
    exact(k, 0);
    exact(k, 1);
    return 0;
}
