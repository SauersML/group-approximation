/* Exact edge prices of the half-cube bubble adversaries H_t (see
   halfcube_price.py for the definition and the formulas).  Prices are
   printed as integers scaled by 2^K, one line per edge class:
       C_0 C_1 ... C_{K/2-1}
   Mode "all": every x with x = +1 on {0, e_1..e_k} and every j (k <= 4).
   Mode "rand N seed": N random x, all j (any k <= 5).
   Mode "near N seed r": N random x at distance r from the pin chi_0.
   Duplicate lines are left for the caller to remove (sort -u). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int k, K;
static int ch[32][32];

static void price(const int *x, int j, int64_t *out) {
    int y[32], Wx[32], Wy[32], ex[32], ey[32];
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
            int64_t one = (int64_t)1 << K;
            int64_t px = one >> sx, py = one >> sy, pu = one >> su;
            if (i != j) out[t] += px + py - 2 * pu;
            else out[t] += 2 * pu + one - px - py;
        }
    }
}

static void emit(const int *x) {
    int64_t out[16];
    for (int j = 0; j < K; j++) {
        price(x, j, out);
        for (int t = 0; t < K / 2; t++) printf(t ? " %lld" : "%lld", (long long)out[t]);
        printf("\n");
    }
}

int main(int argc, char **argv) {
    k = atoi(argv[1]); K = 1 << k;
    for (int a = 0; a < K; a++)
        for (int z = 0; z < K; z++) ch[a][z] = (__builtin_popcount(a & z) & 1) ? -1 : 1;
    int x[32];
    if (!strcmp(argv[2], "all")) {
        int free_[32], nf = 0;
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
