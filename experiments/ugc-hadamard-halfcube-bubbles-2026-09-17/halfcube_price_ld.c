/* Exact edge prices of the half-cube bubble adversaries H_t (see
   halfcube_price.py for the definition and the formulas).  Long-double
   version of halfcube_price.c for K <= 128 (k <= 7): prices K*Pr[cut] are
   printed unscaled (rounding error ~1e-17), one line per edge class:
       C_0 C_1 ... C_{K/2-1}
   Mode "all": every x with x = +1 on {0, e_1..e_k} and every j (k <= 4).
   Mode "rand N seed": N random x, all j (any k <= 5).
   Mode "near N seed r": N random x at distance r from the pin chi_0.
   Duplicate lines are left for the caller to remove (sort -u). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static int k, K;
static int ch[128][128];

static void price(const int *x, int j, long double *out) {
    int y[128], Wx[128], Wy[128], ex[128], ey[128];
    memcpy(y, x, sizeof(int) * K);
    y[j] = -y[j];
    for (int a = 0; a < K; a++) {
        int sx = 0, sy = 0;
        for (int z = 0; z < K; z++) { sx += x[z] * ch[a][z]; sy += y[z] * ch[a][z]; }
        Wx[a] = sx; Wy[a] = sy;
    }
    for (int t = 0; t < K / 2; t++) out[t] = 0;
    for (int i = 0; i < K; i++) {
        for (int a = 0; a < K; a++) {
            ex[a] = (K - x[i] * ch[a][i] * Wx[a]) / 2;
            ey[a] = (K - y[i] * ch[a][i] * Wy[a]) / 2;
        }
        for (int t = 0; t < K / 2; t++) {
            int sx = 0, sy = 0, su = 0;
            for (int a = 0; a < K; a++) {
                int bx = ex[a] <= t, by = ey[a] <= t;
                sx += bx; sy += by; su += (bx || by);
            }
            long double one = 1.0L;
            long double px = ldexpl(1.0L, -sx), py = ldexpl(1.0L, -sy), pu = ldexpl(1.0L, -su);
            if (i != j) out[t] += px + py - 2 * pu;
            else out[t] += 2 * pu + one - px - py;
        }
    }
}

#ifdef EXACT
/* Built with -DEXACT (k <= 6 only): emitted prices are exact integers
   K*Pr[cut] * 2^K in __int128, the same format as halfcube_price.c, so
   cert_dual.py can certify them.  The climb score stays in long double. */
typedef __int128 i128;
static void price_exact(const int *x, int j, i128 *out) {
    int y[128], Wx[128], Wy[128], ex[128], ey[128];
    memcpy(y, x, sizeof(int) * K);
    y[j] = -y[j];
    for (int a = 0; a < K; a++) {
        int sx = 0, sy = 0;
        for (int z = 0; z < K; z++) { sx += x[z] * ch[a][z]; sy += y[z] * ch[a][z]; }
        Wx[a] = sx; Wy[a] = sy;
    }
    for (int t = 0; t < K / 2; t++) out[t] = 0;
    i128 one = (i128)1 << K;
    for (int i = 0; i < K; i++) {
        for (int a = 0; a < K; a++) {
            ex[a] = (K - x[i] * ch[a][i] * Wx[a]) / 2;
            ey[a] = (K - y[i] * ch[a][i] * Wy[a]) / 2;
        }
        for (int t = 0; t < K / 2; t++) {
            int sx = 0, sy = 0, su = 0;
            for (int a = 0; a < K; a++) {
                int bx = ex[a] <= t, by = ey[a] <= t;
                sx += bx; sy += by; su += (bx || by);
            }
            i128 px = one >> sx, py = one >> sy, pu = one >> su;
            if (i != j) out[t] += px + py - 2 * pu;
            else out[t] += 2 * pu + one - px - py;
        }
    }
}
static void print_i128(i128 v) {
    char buf[64]; int n = 0;
    if (v == 0) { putchar('0'); return; }
    if (v < 0) { putchar('-'); v = -v; }
    while (v) { buf[n++] = '0' + (int)(v % 10); v /= 10; }
    while (n) putchar(buf[--n]);
}
static void emit(const int *x) {
    i128 out[64];
    for (int j = 0; j < K; j++) {
        price_exact(x, j, out);
        for (int t = 0; t < K / 2; t++) { if (t) putchar(' '); print_i128(out[t]); }
        printf("\n");
    }
}
#else
static void emit(const int *x) {
    long double out[64];
    for (int j = 0; j < K; j++) {
        price(x, j, out);
        for (int t = 0; t < K / 2; t++) printf(t ? " %.18Lg" : "%.18Lg", out[t]);
        printf("\n");
    }
}
#endif

static long double score(const int *x, const long double *q) {
    long double out[64], best = -1;
    for (int j = 0; j < K; j++) {
        price(x, j, out);
        long double s = 0;
        for (int t = 0; t < K / 2; t++) s += q[t] * out[t];
        if (s > best) best = s;
    }
    return best;
}

int main(int argc, char **argv) {
    k = atoi(argv[1]); K = 1 << k;
    for (int a = 0; a < K; a++)
        for (int z = 0; z < K; z++) ch[a][z] = (__builtin_popcount(a & z) & 1) ? -1 : 1;
    int x[128];
    if (!strcmp(argv[2], "all")) {
        int free_[128], nf = 0;
        for (int z = 0; z < K; z++) if (z && (z & (z - 1))) free_[nf++] = z;
        for (long m = 0; m < (1L << nf); m++) {
            for (int z = 0; z < K; z++) x[z] = 1;
            for (int b = 0; b < nf; b++) if (m >> b & 1) x[free_[b]] = -1;
            emit(x);
        }
    } else if (!strcmp(argv[2], "rand")) {
        long N = atol(argv[3]); srand(atoi(argv[4]));
        for (long n = 0; n < N; n++) {
            for (int z = 0; z < K; z++) x[z] = (rand() & 1) ? 1 : -1;
            emit(x);
        }
    } else if (!strcmp(argv[2], "struct")) {
        /* x_i = f(i mod 2^m): Fourier mass on the span of m characters.
           All f with f(0) = 1 if N == 0, else N random ones. */
        int m = atoi(argv[3]); long N = atol(argv[4]); srand(atoi(argv[5]));
        int M = 1 << m;
        long total = N ? N : (1L << (M - 1));
        for (long n = 0; n < total; n++) {
            long bits = N ? ((long)rand() << 1) : (n << 1);
            for (int z = 0; z < K; z++) x[z] = (bits >> (z % M) & 1) ? -1 : 1;
            emit(x);
        }
    } else if (!strcmp(argv[2], "climb")) {
        /* Separation oracle for the cutting-plane LP: "climb qfile N seed".
           Reads a mixture q (K/2 numbers), hill-climbs N times over x by
           single-coordinate flips to maximize max_j sum_t q_t C_t(x, j),
           starting near chi_0 at a random radius (or from a random x if
           the radius draw lands at K/2), and emits every edge class of each
           local optimum.  The score goes to stderr. */
        FILE *f = fopen(argv[3], "r");
        long double q[64];
        for (int t = 0; t < K / 2; t++) if (fscanf(f, "%Lf", &q[t]) != 1) return 1;
        fclose(f);
        long N = atol(argv[4]); srand(atoi(argv[5]));
        for (long n = 0; n < N; n++) {
            int r = rand() % (K / 2 + 1);
            for (int z = 0; z < K; z++) x[z] = 1;
            if (n % 2 == 1) {
                /* odd starts: a random structured point x_i = f(i mod 2^m),
                   m in 2..4, then r / 4 random flips */
                int m = 2 + rand() % 3, M = 1 << m;
                long bits = (long)rand() << 1;
                for (int z = 0; z < K; z++) x[z] = (bits >> (z % M) & 1) ? -1 : 1;
                for (int c = 0; c < r / 4; c++) { int z = rand() % K; x[z] = -x[z]; }
            }
            else if (r == K / 2) for (int z = 0; z < K; z++) x[z] = (rand() & 1) ? 1 : -1;
            else { int c = 0; while (c < r) { int z = rand() % K; if (x[z] == 1) { x[z] = -1; c++; } } }
            long double best = score(x, q);
            for (int improved = 1; improved;) {
                improved = 0;
                for (int z = 0; z < K; z++) {
                    x[z] = -x[z];
                    long double s = score(x, q);
                    if (s > best + 1e-12L) { best = s; improved = 1; }
                    else x[z] = -x[z];
                }
            }
            fprintf(stderr, "start r=%d local max %.12Lf\n", r, best);
            emit(x);
        }
    } else if (!strcmp(argv[2], "near")) {
        long N = atol(argv[3]); srand(atoi(argv[4])); int r = atoi(argv[5]);
        for (long n = 0; n < N; n++) {
            for (int z = 0; z < K; z++) x[z] = 1;
            int c = 0;
            while (c < r) { int z = rand() % K; if (x[z] == 1) { x[z] = -1; c++; } }
            emit(x);
        }
    }
    return 0;
}
