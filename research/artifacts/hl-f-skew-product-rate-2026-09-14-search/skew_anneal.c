/* Skew-product search for Thompson F permutation pairs with small ratio max(m1,m2)/mc.
 * A(p,i) = (A0 p, c_p(i)), B(p,i) = (B0 p, d_p(i)) on base points p and fibre [k].
 * Base: mode "torus N" = commuting translations on Z_N x Z_N, or "file PATH" = base pair A0,B0 from a
 * certificate file (lines A=..., B=..., 0-based images). Cocycle moves: "sym" composes c_p or d_p with a
 * random fibre transposition; "cyc" adds a random rotation (abelian fibre Z/k, so on a torus base the
 * pair is metabelian and the landed bound t <= 2 d(R1) + d(R2) forces ratio >= 1/3: calibration).
 * m1, m2, mc = moved points of R1 = bAABaaBAba, R2 = bAAABaaaBAAbaa, C = abAB (last letter acts first).
 * Metropolis on log ratio, geometric cooling, penalty keeps mc >= frac*n. Evidence only.
 * usage: skew_anneal torus N | file PATH  k sym|cyc frac steps seed [const]
 *   const: start from constant identity cocycles and do 0 steps (calibration of the count formula).
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n0, k, n;
static int *A0, *B0;
static unsigned long long rs;
static inline unsigned long long rng(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static const char *R1 = "bAABaaBAba", *R2 = "bAAABaaaBAAbaa", *CW = "abAB";
static int moved(const char *w, const int *a, const int *ai, const int *b, const int *bi) {
    int L = (int)strlen(w), cnt = 0;
    for (int x = 0; x < n; x++) {
        int y = x;
        for (int j = L - 1; j >= 0; j--) { char c = w[j]; y = c == 'a' ? a[y] : c == 'A' ? ai[y] : c == 'b' ? b[y] : bi[y]; }
        cnt += (y != x);
    }
    return cnt;
}
static void build(const int *c, const int *d, int *a, int *ai, int *b, int *bi) {
    for (int p = 0; p < n0; p++) for (int i = 0; i < k; i++) {
        int x = p * k + i;
        a[x] = A0[p] * k + c[p * k + i];
        b[x] = B0[p] * k + d[p * k + i];
    }
    for (int x = 0; x < n; x++) { ai[a[x]] = x; bi[b[x]] = x; }
}
static int loadbase(const char *path) {
    FILE *fp = fopen(path, "r"); if (!fp) return 0;
    static char line[1 << 16]; int na = 0, nb = 0;
    A0 = malloc(4096 * sizeof(int)); B0 = malloc(4096 * sizeof(int));
    while (fgets(line, sizeof line, fp)) {
        int *p = line[0] == 'A' ? A0 : line[0] == 'B' ? B0 : NULL; int *cnt = line[0] == 'A' ? &na : &nb;
        if (!p || line[1] != '=') continue;
        char *q = line + 2;
        while (*q && *q != '\n') { p[(*cnt)++] = (int)strtol(q, &q, 10); if (*q == ',') q++; else break; }
    }
    fclose(fp);
    if (na != nb || na == 0) return 0;
    n0 = na; return 1;
}
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: skew_anneal torus N | file PATH  k sym|cyc frac steps seed [const]\n"); return 1; }
    if (!strcmp(argv[1], "torus")) {
        int N = atoi(argv[2]); n0 = N * N;
        A0 = malloc(n0 * sizeof(int)); B0 = malloc(n0 * sizeof(int));
        for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) { A0[x * N + y] = ((x + 1) % N) * N + y; B0[x * N + y] = x * N + (y + 1) % N; }
    } else if (!loadbase(argv[2])) { fprintf(stderr, "bad base file\n"); return 1; }
    k = atoi(argv[3]); int cyc = !strcmp(argv[4], "cyc");
    double frac = atof(argv[5]); long steps = atol(argv[6]);
    rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[7]);
    int konst = argc >= 9 && !strcmp(argv[8], "const");
    n = n0 * k; int minmc = (int)floor(frac * n);
    int *c = malloc(n * sizeof(int)), *d = malloc(n * sizeof(int));
    int *a = malloc(n * sizeof(int)), *ai = malloc(n * sizeof(int)), *b = malloc(n * sizeof(int)), *bi = malloc(n * sizeof(int));
    int *bc = malloc(n * sizeof(int)), *bd = malloc(n * sizeof(int));
    for (int p = 0; p < n0; p++) for (int i = 0; i < k; i++) { c[p * k + i] = i; d[p * k + i] = i; }
    if (!konst) for (int p = 0; p < n0; p++) {
        if (cyc) { int s = (int)(rng() % k), t = (int)(rng() % k); for (int i = 0; i < k; i++) { c[p * k + i] = (i + s) % k; d[p * k + i] = (i + t) % k; } }
        else for (int *z = c; z; z = (z == c ? d : NULL)) for (int i = k - 1; i > 0; i--) { int j = (int)(rng() % (i + 1)); int tmp = z[p * k + i]; z[p * k + i] = z[p * k + j]; z[p * k + j] = tmp; }
    }
    build(c, d, a, ai, b, bi);
    int m1 = moved(R1, a, ai, b, bi), m2 = moved(R2, a, ai, b, bi), mc = moved(CW, a, ai, b, bi);
    if (konst) { printf("const n0=%d k=%d m1=%d m2=%d mc=%d\n", n0, k, m1, m2, mc); return 0; }
    double cur = log(((m1 > m2 ? m1 : m2) + 0.5) / (mc + 0.5)) + (mc < minmc ? 10.0 * (minmc - mc) : 0);
    int bm1 = -1, bm2 = 0, bmc = 1;
    int *oc = malloc(k * sizeof(int));
    double T0 = 0.5, T1 = 0.002;
    for (long s = 0; s < steps; s++) {
        double T = T0 * pow(T1 / T0, (double)s / steps);
        int *z = (rng() & 1) ? c : d; int p = (int)(rng() % n0);
        memcpy(oc, z + p * k, k * sizeof(int));
        if (cyc) { int sh = 1 + (int)(rng() % (k - 1)); for (int i = 0; i < k; i++) z[p * k + i] = (oc[i] + sh) % k; }
        else { int i = (int)(rng() % k), j = (int)(rng() % k); if (i == j) continue; int tmp = z[p * k + i]; z[p * k + i] = z[p * k + j]; z[p * k + j] = tmp; }
        build(c, d, a, ai, b, bi);
        int n1 = moved(R1, a, ai, b, bi), n2 = moved(R2, a, ai, b, bi), nc = moved(CW, a, ai, b, bi);
        double sc = log(((n1 > n2 ? n1 : n2) + 0.5) / (nc + 0.5)) + (nc < minmc ? 10.0 * (minmc - nc) : 0);
        if (sc <= cur || exp((cur - sc) / T) > (double)(rng() % 1000000) / 1e6) {
            cur = sc;
            if (nc >= minmc && nc > 0 && (bm1 < 0 || (long)(n1 > n2 ? n1 : n2) * bmc < (long)(bm1 > bm2 ? bm1 : bm2) * nc)) {
                bm1 = n1; bm2 = n2; bmc = nc; memcpy(bc, c, n * sizeof(int)); memcpy(bd, d, n * sizeof(int));
            }
        } else memcpy(z + p * k, oc, k * sizeof(int));
    }
    if (bm1 < 0) { printf("n=%d none\n", n); return 0; }
    int mx = bm1 > bm2 ? bm1 : bm2;
    printf("n=%d n0=%d k=%d mode=%s frac=%.2f best m1=%d m2=%d mc=%d rho_max=%d/%d=%.4f\n", n, n0, k, argv[4], frac, bm1, bm2, bmc, mx, bmc, (double)mx / bmc);
    build(bc, bd, a, ai, b, bi);
    printf("A="); for (int x = 0; x < n; x++) printf("%d%s", a[x], x + 1 < n ? "," : "\n");
    printf("B="); for (int x = 0; x < n; x++) printf("%d%s", b[x], x + 1 < n ? "," : "\n");
    return 0;
}
