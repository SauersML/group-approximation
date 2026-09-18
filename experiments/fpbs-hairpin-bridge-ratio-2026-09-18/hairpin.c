/* Br/TJT on hairpin vs straight chordless paths in Z^2, percolation spine.
 *
 * Environment Z: Bernoulli(p') bond percolation in a box with margin L around the
 * path; spine proxy = open edges whose cluster touches the box boundary.
 * Formulas (fpbs-percolation-spine-path-bridge-ratio-criterion, Thm 1(a)):
 *   t(i,j) = E r^{N(i,j]},  TJT = sum_k [t(0,k-1)t(k,n) + t(0,k)t(k-1,n)],
 *   Br = E[G r^{N-1}],  Br/TJT = gamma_n/(r D_n),  D_n = TJT/(n t(0,n)).
 * Both path types are symmetric under a reflection reversing the path, and the
 * box is chosen symmetric, so t(k,n) = t(0,n-k); only prefixes are estimated.
 * Prefix t(0,k) is estimated in its own run with the prefix edges importance-
 * sampled: open w.p. p'/a, a = p' + (1-p') r; weight a^k r^{#open, not in Z}.
 * Batch means (NB batches) give the error of Br/TJT and n D_n.
 *
 * usage: hairpin type(0 straight,1 hairpin) n p r L samples seed [mode]
 * (hairpin needs n even, m = (n-2)/2 columns per arm)
 * mode 1: only the middle split h = n/2: prints the split excess
 *   Lmid = log t(0,n) - log t(0,h) - log t(h,n) = log t(0,n) - 2 log t(0,h),
 * which for the hairpin is the cross-fold coverage correlation of the two arms.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>

static uint64_t s[4];
static inline uint64_t rotl(const uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t next(void) {
  const uint64_t result = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
  s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45);
  return result;
}
static inline double unif(void) { return (next() >> 11) * 0x1.0p-53; }
static void seed_rng(uint64_t x) {
  for (int i = 0; i < 4; i++) { x += 0x9e3779b97f4a7c15ULL; uint64_t z = x;
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    s[i] = z ^ (z >> 31); }
}

static int W, H, NV, *par;
static int find(int x) { while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; } return x; }
static void unite(int a, int b) { a = find(a); b = find(b); if (a != b) par[a] = b; }
static int vid(int x, int y) { return y * W + x; }

#define NB 10
int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage\n"); return 64; }
  int type = atoi(argv[1]), n = atoi(argv[2]);
  double p = atof(argv[3]), r = atof(argv[4]);
  int L = atoi(argv[5]); long S = atol(argv[6]); uint64_t seed = strtoull(argv[7], 0, 10);
  int m = (n - 2) / 2;
  int mode = argc > 8 ? atoi(argv[8]) : 0, h = n / 2;
  /* path vertices in box coordinates */
  int *px = malloc((n + 1) * sizeof(int)), *py = malloc((n + 1) * sizeof(int));
  if (type == 0) {
    W = n + 1 + 2 * L; H = 2 * L + 1;
    for (int i = 0; i <= n; i++) { px[i] = L + i; py[i] = L; }
  } else {
    if (n != 2 * m + 2 || m < 1) { fprintf(stderr, "hairpin needs even n >= 4\n"); return 64; }
    W = m + 1 + 2 * L; H = 3 + 2 * L;
    for (int i = 0; i <= m; i++) { px[i] = L + i; py[i] = L; }
    px[m + 1] = L + m; py[m + 1] = L + 1;
    for (int j = 0; j <= m; j++) { px[m + 2 + j] = L + m - j; py[m + 2 + j] = L + 2; }
  }
  NV = W * H;
  par = malloc((NV + 1) * sizeof(int));
  /* edges: horizontal id = vid(x,y) (x<W-1), vertical id = NV + vid(x,y) (y<H-1) */
  int NE = 2 * NV;
  int *pe = malloc(n * sizeof(int));   /* path edge ids in order */
  int *onpath = malloc(NE * sizeof(int));
  for (int e = 0; e < NE; e++) onpath[e] = -1;
  for (int k = 0; k < n; k++) {
    int x0 = px[k], y0 = py[k], x1 = px[k + 1], y1 = py[k + 1], id;
    if (y0 == y1) id = vid(x0 < x1 ? x0 : x1, y0); else id = NV + vid(x0, y0 < y1 ? y0 : y1);
    pe[k] = id; onpath[id] = k;
  }
  double a = p + (1 - p) * r, qt = p / a;
  unsigned char *open = malloc(NE);
  int *inZ = malloc(n * sizeof(int));
  /* sums[k][b]: estimator of t(0,k) in batch b; brs[b]: estimator of E[G r^N] */
  double (*sums)[NB] = calloc(n + 1, sizeof *sums);
  double brs[NB] = {0};
  long per = S / NB;
  for (int k = 1; k <= n; k++) {
    if (mode == 1 && k != h && k != n) continue;
    seed_rng(seed * 1000003ULL + k * 7919ULL + type);
    for (long it = 0; it < per * NB; it++) {
      int b = (int)(it / per);
      for (int v = 0; v <= NV; v++) par[v] = v;
      for (int x = 0; x < W; x++) { unite(vid(x, 0), NV); unite(vid(x, H - 1), NV); }
      for (int y = 0; y < H; y++) { unite(vid(0, y), NV); unite(vid(W - 1, y), NV); }
      for (int y = 0; y < H; y++) for (int x = 0; x < W; x++) {
        int e = vid(x, y);
        if (x < W - 1) { int k2 = onpath[e]; double pp = (k2 >= 0 && k2 < k) ? qt : p;
          open[e] = unif() < pp; if (open[e]) unite(vid(x, y), vid(x + 1, y)); }
        int f = NV + vid(x, y);
        if (y < H - 1) { int k2 = onpath[f]; double pp = (k2 >= 0 && k2 < k) ? qt : p;
          open[f] = unif() < pp; if (open[f]) unite(vid(x, y), vid(x, y + 1)); }
      }
      int root = find(NV), miss = 0;
      for (int j = 0; j < n; j++) {
        int e = pe[j];
        int v = e < NV ? e : e - NV;
        inZ[j] = open[e] && find(v) == root;
        if (j < k && open[e] && !inZ[j]) miss++;
      }
      double w = pow(a, k) * pow(r, miss);
      sums[k][b] += w;
      if (k == n) {
        int first = -1, last = -1, G = 0;
        for (int j = 0; j < n; j++) if (inZ[j]) { if (first < 0) first = j; last = j; }
        for (int j = first + 1; j < last; j++) if (!inZ[j]) G++;
        brs[b] += w * G;
      }
    }
  }
  if (mode == 1) {
    double v[NB + 1];
    for (int b = 0; b <= NB; b++) {
      double th = 0, tn = 0;
      if (b < NB) { th = sums[h][b] / per; tn = sums[n][b] / per; }
      else { for (int c = 0; c < NB; c++) { th += sums[h][c]; tn += sums[n][c]; } th /= per * NB; tn /= per * NB; }
      v[b] = log(tn) - 2 * log(th);
    }
    double mu = 0, sd = 0;
    for (int b = 0; b < NB; b++) mu += v[b] / NB;
    for (int b = 0; b < NB; b++) sd += (v[b] - mu) * (v[b] - mu);
    sd = sqrt(sd / (NB - 1) / NB);
    printf("%s n=%d p=%.3f r=%.2f L=%d S=%ld  Lmid=%.5f +- %.5f  logT=%.4f\n", type ? "hairpin " : "straight",
           n, p, r, L, S, v[NB], sd, log(sums[n][0] / per));
    return 0;
  }
  /* per-batch and pooled ratios */
  double vals[NB + 1][2];
  for (int b = 0; b <= NB; b++) {
    double t[4096];
    for (int k = 0; k <= n; k++) {
      double acc = 0; if (k == 0) { t[0] = 1; continue; }
      if (b < NB) acc = sums[k][b] / per; else { for (int c = 0; c < NB; c++) acc += sums[k][c]; acc /= per * NB; }
      t[k] = acc;
    }
    double br = 0; if (b < NB) br = brs[b] / per; else { for (int c = 0; c < NB; c++) br += brs[c]; br /= per * NB; }
    br /= r;
    double tjt = 0;
    for (int k = 1; k <= n; k++) tjt += t[k - 1] * t[n - k] + t[k] * t[n - k + 1];
    vals[b][0] = tjt / t[n];           /* n D_n */
    vals[b][1] = br / tjt;             /* Br/TJT */
  }
  double mu[2] = {0}, sd[2] = {0};
  for (int i = 0; i < 2; i++) { for (int b = 0; b < NB; b++) mu[i] += vals[b][i] / NB;
    for (int b = 0; b < NB; b++) sd[i] += (vals[b][i] - mu[i]) * (vals[b][i] - mu[i]);
    sd[i] = sqrt(sd[i] / (NB - 1) / NB); }
  /* tilted gap density gamma = Br r D_n / 1 */
  printf("%s n=%d p=%.3f r=%.2f L=%d S=%ld  nD_n=%.4f +- %.4f  Br/TJT=%.4f +- %.4f  gamma=%.4f\n",
         type ? "hairpin " : "straight", n, p, r, L, S, vals[NB][0], sd[0], vals[NB][1], sd[1],
         vals[NB][1] * r * vals[NB][0] / n);
  return 0;
}
