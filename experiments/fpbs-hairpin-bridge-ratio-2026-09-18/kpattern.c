/* Coverage decorrelation ratio K(S) = P(S in Z) / (P(S^- in Z) P(S^+ in Z)) for the
 * matched multi-run pattern on a hairpin, vs the same pattern on a straight path.
 *
 * Z = open edges whose cluster meets the boundary of a box with margin L (the
 * box proxy of the percolation spine; Bernoulli(p') bonds).  P(F in Z) = p'^|F| q(F),
 * q(F) = P(every run of F is joined to the boundary | F open), so
 * K(S) = q(S) / (q(S^-) q(S^+)).
 *
 * Hairpin with m = 2l+2 columns per arm, split edge e_k = first turn edge:
 *   S^- = { a_1, a_3, ..., a_{2l-1} }  (row 0),   S^+ = { b_1, b_3, ..., b_{2l-1} }  (row 2),
 * l single-edge runs on each side, matched column by column across the fold.
 * Straight path of the same length n = 2m+2, split edge = middle edge:
 *   S^- = l single-edge runs at odd offsets before it, S^+ = the mirror image.
 * By the reflection symmetry of each (path, box) pair, q(S^+) = q(S^-).
 *
 * usage: kpattern type(0 straight,1 hairpin) l p L samples seed
 * prints log K = log q(S) - 2 log q(S^-) with batch-means error.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

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
  if (argc < 7) { fprintf(stderr, "usage\n"); return 64; }
  int type = atoi(argv[1]), l = atoi(argv[2]);
  double p = atof(argv[3]); int L = atoi(argv[4]); long S = atol(argv[5]);
  uint64_t seed = strtoull(argv[6], 0, 10);
  int m = 2 * l + 2, n = 2 * m + 2;
  int *sx = malloc(2 * l * sizeof(int)), *sy = malloc(2 * l * sizeof(int));  /* left endpoints of horizontal pattern edges */
  if (type == 1) {
    W = m + 1 + 2 * L; H = 3 + 2 * L;
    for (int i = 0; i < l; i++) { sx[i] = L + 2 * i; sy[i] = L; sx[l + i] = L + 2 * i; sy[l + i] = L + 2; }
  } else {
    W = n + 1 + 2 * L; H = 2 * L + 1;
    int mid = n / 2;               /* split edge = (mid-1, mid) */
    for (int i = 0; i < l; i++) {
      sx[i] = L + mid - 3 - 2 * i; sy[i] = L;            /* before the split edge */
      sx[l + i] = L + mid + 1 + 2 * i; sy[l + i] = L;    /* mirror image after it */
    }
  }
  NV = W * H;
  par = malloc((NV + 1) * sizeof(int));
  unsigned char *forced = calloc(NV, 1);                /* horizontal edge (x,y)-(x+1,y) forced open */
  double acc[2][NB] = {{0}};
  long per = S / NB;
  for (int run = 0; run < 2; run++) {                   /* run 0: S^- only;  run 1: S = S^- + S^+ */
    for (int v = 0; v < NV; v++) forced[v] = 0;
    int cnt = run ? 2 * l : l;
    for (int i = 0; i < cnt; i++) forced[vid(sx[i], sy[i])] = 1;
    seed_rng(seed * 7777ULL + run * 131ULL + type);
    for (long it = 0; it < per * NB; it++) {
      for (int v = 0; v <= NV; v++) par[v] = v;
      for (int x = 0; x < W; x++) { unite(vid(x, 0), NV); unite(vid(x, H - 1), NV); }
      for (int y = 0; y < H; y++) { unite(vid(0, y), NV); unite(vid(W - 1, y), NV); }
      for (int y = 0; y < H; y++) for (int x = 0; x < W; x++) {
        if (x < W - 1 && (forced[vid(x, y)] || unif() < p)) unite(vid(x, y), vid(x + 1, y));
        if (y < H - 1 && unif() < p) unite(vid(x, y), vid(x, y + 1));
      }
      int root = find(NV), ok = 1;
      for (int i = 0; i < cnt && ok; i++) ok = find(vid(sx[i], sy[i])) == root;
      acc[run][it / per] += ok;
    }
  }
  double v[NB + 1];
  for (int b = 0; b <= NB; b++) {
    double q1 = 0, q2 = 0;
    if (b < NB) { q1 = acc[0][b] / per; q2 = acc[1][b] / per; }
    else { for (int c = 0; c < NB; c++) { q1 += acc[0][c]; q2 += acc[1][c]; } q1 /= per * NB; q2 /= per * NB; }
    v[b] = log(q2) - 2 * log(q1);
  }
  double mu = 0, sd = 0;
  for (int b = 0; b < NB; b++) mu += v[b] / NB;
  for (int b = 0; b < NB; b++) sd += (v[b] - mu) * (v[b] - mu);
  sd = sqrt(sd / (NB - 1) / NB);
  double q1 = 0, q2 = 0;
  for (int c = 0; c < NB; c++) { q1 += acc[0][c]; q2 += acc[1][c]; }
  printf("%s l=%d n=%d p=%.3f L=%d S=%ld  q(S-)=%.5g q(S)=%.5g  logK=%.4f +- %.4f\n",
         type ? "hairpin " : "straight", l, n, p, L, S, q1 / (per * NB), q2 / (per * NB), v[NB], sd);
  return 0;
}
