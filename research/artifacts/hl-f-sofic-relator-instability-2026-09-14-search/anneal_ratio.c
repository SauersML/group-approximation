/* Heuristic search for permutation pairs with small relator-defect / commutator-separation ratio.
 * Objective: minimize rho = max(m1,m2) / mc (and track (m1+m2)/mc), subject to mc >= floor(frac*n)
 * (so the separation stays a fixed fraction; this probes the envelope, not tiny separations).
 * m1, m2, mc = moved-point counts of R1 = bAABaaBAba, R2 = bAAABaaaBAAbaa, C = abAB (last letter
 * acts first; capitals are inverses). Moves: A <- A o (i j) or B <- B o (i j), Metropolis on
 * log-ratio with geometric cooling. Evidence only: nothing here is a proof.
 * usage: anneal_ratio n frac steps seed
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n;
static unsigned long long rs;
static inline unsigned long long rng(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}

static int moved(const char *w, const int *a, const int *ai, const int *b, const int *bi) {
    int L = (int)strlen(w), cnt = 0;
    for (int x = 0; x < n; x++) {
        int y = x;
        for (int k = L - 1; k >= 0; k--) {
            char c = w[k];
            y = c == 'a' ? a[y] : c == 'A' ? ai[y] : c == 'b' ? b[y] : bi[y];
        }
        cnt += (y != x);
    }
    return cnt;
}

static const char *R1 = "bAABaaBAba", *R2 = "bAAABaaaBAAbaa", *CW = "abAB";

static double score(const int *a, const int *ai, const int *b, const int *bi, int minmc,
                    int *m1o, int *m2o, int *mco) {
    int mc = moved(CW, a, ai, b, bi);
    int m1 = moved(R1, a, ai, b, bi), m2 = moved(R2, a, ai, b, bi);
    *m1o = m1; *m2o = m2; *mco = mc;
    int mx = m1 > m2 ? m1 : m2;
    double pen = mc < minmc ? 10.0 * (minmc - mc) : 0.0;
    return log((mx + 0.5) / (mc + 0.5)) + pen;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: anneal_ratio n frac steps seed\n"); return 1; }
    n = atoi(argv[1]);
    double frac = atof(argv[2]);
    long steps = atol(argv[3]);
    rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[4]);
    int minmc = (int)floor(frac * n);
    int *a = malloc(n * sizeof(int)), *ai = malloc(n * sizeof(int));
    int *b = malloc(n * sizeof(int)), *bi = malloc(n * sizeof(int));
    int *ba = malloc(n * sizeof(int)), *bb = malloc(n * sizeof(int));
    for (int i = 0; i < n; i++) { a[i] = i; b[i] = i; }
    if (argc >= 6) {
        /* seed file: lines "A=i,j,..." and "B=i,j,..." on n0 <= n points, padded by fixed points */
        FILE *fp = fopen(argv[5], "r");
        char line[1 << 16];
        while (fp && fgets(line, sizeof line, fp)) {
            int *p = line[0] == 'A' ? a : line[0] == 'B' ? b : NULL;
            if (!p || line[1] != '=') continue;
            char *q = line + 2; int k = 0;
            while (*q && k < n) { p[k++] = (int)strtol(q, &q, 10); if (*q == ',') q++; else break; }
        }
        if (fp) fclose(fp);
    } else {
        for (int i = n - 1; i > 0; i--) { int j = (int)(rng() % (i + 1)); int t = a[i]; a[i] = a[j]; a[j] = t; }
        for (int i = n - 1; i > 0; i--) { int j = (int)(rng() % (i + 1)); int t = b[i]; b[i] = b[j]; b[j] = t; }
    }
    for (int i = 0; i < n; i++) { ai[a[i]] = i; bi[b[i]] = i; }
    int m1, m2, mc;
    double cur = score(a, ai, b, bi, minmc, &m1, &m2, &mc);
    double best = 1e9; int bm1 = 0, bm2 = 0, bmc = 0;
    double T0 = 0.5, T1 = 0.002;
    for (long s = 0; s < steps; s++) {
        double T = T0 * pow(T1 / T0, (double)s / steps);
        int which = (int)(rng() & 1);
        int i = (int)(rng() % n), j = (int)(rng() % n);
        if (i == j) continue;
        int *p = which ? b : a, *pi = which ? bi : ai;
        int t = p[i]; p[i] = p[j]; p[j] = t;
        pi[p[i]] = i; pi[p[j]] = j;
        int n1, n2, nc;
        double nw = score(a, ai, b, bi, minmc, &n1, &n2, &nc);
        if (nw <= cur || exp((cur - nw) / T) > (double)(rng() % 1000000) / 1e6) {
            cur = nw; m1 = n1; m2 = n2; mc = nc;
            if (mc >= minmc && cur < best) {
                best = cur; bm1 = m1; bm2 = m2; bmc = mc;
                memcpy(ba, a, n * sizeof(int)); memcpy(bb, b, n * sizeof(int));
            }
        } else {
            t = p[i]; p[i] = p[j]; p[j] = t;
            pi[p[i]] = i; pi[p[j]] = j;
        }
    }
    int bmx = bm1 > bm2 ? bm1 : bm2;
    printf("n=%d frac=%.3f steps=%ld seed=%s best m1=%d m2=%d mc=%d rho_max=%d/%d=%.4f rho_sum=%.4f\n",
           n, frac, steps, argv[4], bm1, bm2, bmc, bmx, bmc, bmc ? (double)bmx / bmc : -1.0,
           bmc ? (double)(bm1 + bm2) / bmc : -1.0);
    printf("A=");
    for (int i = 0; i < n; i++) printf("%d%s", ba[i], i + 1 < n ? "," : "\n");
    printf("B=");
    for (int i = 0; i < n; i++) printf("%d%s", bb[i], i + 1 < n ? "," : "\n");
    return 0;
}
