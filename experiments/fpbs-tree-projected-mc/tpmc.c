/* Monte Carlo of fibre-summed two-point quantities for Bernoulli bond percolation
   on tree-projected Cayley graphs of F_2 x Z (lane bs-pc-pu-2, 2026-09-12).

   Generators: (a,t) for t in Ta, (b,t) for t in Tb, (1,z) for z in Z, with inverses.
   Vertices (q,h), q a reduced word of F_2 (dirs 0=a 1=A 2=b 3=B), h in Z.
   Estimates, for one p:
     chi = E|K_o|, sig(q) = E|K_o cap Gamma_q| for q in {1,a,A,b,B},
     BH  = sum_q sig(q)^2 via two independent clusters (E sum_q m1(q) m2(q)),
     chiHbr(s) = E|K^{X minus branch(s^-1)}_o cap Gamma_1|, lam(s) = p |T_s| chiHbr(s),
     share_s(D) = E|K_o cap pi^-1(branch(s^D))| / chi for s in {a,b}.
   Usage: tpmc p N cap seed Ta Tb Z Dmax     e.g. tpmc 0.15 100000 2000000 1 0,1 0 1 8 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static uint64_t S4[4];
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t nxt(void) {
  uint64_t r = rotl(S4[1] * 5, 7) * 9, t = S4[1] << 17;
  S4[2] ^= S4[0]; S4[3] ^= S4[1]; S4[1] ^= S4[2]; S4[0] ^= S4[3]; S4[2] ^= t; S4[3] = rotl(S4[3], 45);
  return r;
}
static uint64_t splitmix(uint64_t *x) {
  uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}
static uint64_t THR;

#define MAXT 32
static int Ta[MAXT], nTa, Tb[MAXT], nTb, Zs[MAXT], nZ;
static int parse(const char *str, int *a) {
  int n = 0; char buf[512]; strncpy(buf, str, 511); buf[511] = 0;
  for (char *tok = strtok(buf, ","); tok && n < MAXT; tok = strtok(NULL, ",")) a[n++] = atoi(tok);
  return n;
}

/* tree of F_2 built lazily; first[c] = first letter, run[c] = length of initial run of it */
static int32_t *par, *child, *depth, *run; static int8_t *pdir, *first; static long nn, maxnodes;
static void tree_reset(void) { nn = 1; par[0] = -1; pdir[0] = -1; depth[0] = 0; run[0] = 0; first[0] = -1; for (int d = 0; d < 4; d++) child[d] = -1; }
static int32_t mv(int32_t x, int d) {
  if (x && d == (pdir[x] ^ 1)) return par[x];
  int32_t c = child[4 * (long)x + d]; if (c >= 0) return c;
  if (nn >= maxnodes) { fprintf(stderr, "node overflow\n"); exit(2); }
  c = (int32_t)nn++; par[c] = x; pdir[c] = (int8_t)d; depth[c] = depth[x] + 1;
  for (int e = 0; e < 4; e++) child[4 * (long)c + e] = -1;
  if (x == 0) { first[c] = (int8_t)d; run[c] = 1; }
  else { first[c] = first[x]; run[c] = (run[x] == depth[x] && d == first[x]) ? run[x] + 1 : run[x]; }
  child[4 * (long)x + d] = c; return c;
}

static uint64_t *hkey; static int hshift; static long hmask, *hused, nhused;
static inline uint64_t mkkey(int32_t x, int64_t h) { return (((uint64_t)(uint32_t)x << 32) | (uint32_t)(h + 2147483648LL)) + 1; }
static int hinsert(uint64_t k) {
  long i = (long)((k * 0x9E3779B97F4A7C15ULL) >> hshift);
  while (hkey[i]) { if (hkey[i] == k) return 0; i = (i + 1) & hmask; }
  hkey[i] = k; hused[nhused++] = i; return 1;
}
static void hclear(void) { for (long i = 0; i < nhused; i++) hkey[hused[i]] = 0; nhused = 0; }

static int32_t *qx, *cnt, *touched; static int64_t *qh; static long ntouched;
static inline int visit(int32_t y, int64_t h2, long *tail, long cap, int *capped) {
  if (!hinsert(mkkey(y, h2))) return 0;
  if (*tail >= cap) { *capped = 1; return 1; }
  qx[*tail] = y; qh[*tail] = h2; (*tail)++;
  if (!cnt[y]) touched[ntouched++] = y;
  cnt[y]++; return 0;
}
/* explore the cluster of (root,0); forbid = direction blocked at the root node (-1 for none) */
static long explore(long cap, int forbid, int *capped) {
  hclear(); for (long i = 0; i < ntouched; i++) cnt[touched[i]] = 0; ntouched = 0;
  long head = 0, tail = 0; *capped = 0;
  hinsert(mkkey(0, 0)); qx[0] = 0; qh[0] = 0; tail = 1; cnt[0] = 1; touched[ntouched++] = 0;
  while (head < tail) {
    int32_t x = qx[head]; int64_t h = qh[head]; head++;
    for (int i = 0; i < nZ; i++) for (int sg = -1; sg <= 1; sg += 2) {
      if (nxt() >= THR) continue;
      if (visit(x, h + sg * Zs[i], &tail, cap, capped)) return tail;
    }
    for (int d = 0; d < 4; d++) {
      if (x == 0 && d == forbid) continue;
      int n = (d < 2) ? nTa : nTb; int *T = (d < 2) ? Ta : Tb; int sg = (d % 2 == 0) ? 1 : -1;
      for (int i = 0; i < n; i++) {
        if (nxt() >= THR) continue;
        if (visit(mv(x, d), h + sg * T[i], &tail, cap, capped)) return tail;
      }
    }
  }
  return tail;
}

#define NB 20
#define NQ 15
static const char *QN[NQ] = {"chi","sig1","sigA","sigAi","sigB","sigBi","BH","chiHbrA","chiHbrAi","chiHbrB","chiHbrBi","lamA","lamAi","lamB","lamBi"};
int main(int argc, char **argv) {
  if (argc < 9) { fprintf(stderr, "usage: tpmc p N cap seed Ta Tb Z Dmax\n"); return 1; }
  double p = atof(argv[1]); long N = atol(argv[2]), cap = atol(argv[3]); uint64_t sd = strtoull(argv[4], 0, 10);
  nTa = parse(argv[5], Ta); nTb = parse(argv[6], Tb); nZ = parse(argv[7], Zs);
  int Dmax = atoi(argv[8]); if (Dmax > 32) Dmax = 32;
  for (int i = 0; i < 4; i++) S4[i] = splitmix(&sd);
  THR = (uint64_t)(p * 18446744073709551616.0);
  maxnodes = 6 * cap + 64; int hb = 1; while ((1L << hb) < 4 * cap) hb++; hshift = 64 - hb; hmask = (1L << hb) - 1;
  par = malloc(maxnodes * 4); depth = malloc(maxnodes * 4); run = malloc(maxnodes * 4); pdir = malloc(maxnodes); first = malloc(maxnodes);
  child = malloc(maxnodes * 16); cnt = calloc(maxnodes, 4); touched = malloc(maxnodes * 4);
  hkey = calloc(1L << hb, 8); hused = malloc(cap * 16 + 64); qx = malloc(cap * 4 + 16); qh = malloc(cap * 8 + 16);
  int32_t *l1n = malloc(cap * 4 + 16), *l1c = malloc(cap * 4 + 16);
  if (!par || !child || !hkey || !l1c) { fprintf(stderr, "alloc failed\n"); return 3; }
  static double acc[NB][NQ], shA[NB][33], shB[NB][33], bRb[NB][33]; long capped_total = 0, perb = N / NB;
  for (int b = 0; b < NB; b++) for (long it = 0; it < perb; it++) {
    int cp; tree_reset();
    long K = explore(cap, -1, &cp); capped_total += cp;
    acc[b][0] += K; acc[b][1] += cnt[0];
    for (int d = 0; d < 4; d++) { int32_t c = child[d]; acc[b][2 + d] += (c >= 0) ? cnt[c] : 0; }
    long n1 = ntouched;
    for (long i = 0; i < n1; i++) {
      int32_t c = touched[i]; l1n[i] = c; l1c[i] = cnt[c];
      if (first[c] == 0) for (int D = 1; D <= Dmax && D <= run[c]; D++) shA[b][D] += cnt[c];
      if (first[c] == 2) for (int D = 1; D <= Dmax && D <= run[c]; D++) shB[b][D] += cnt[c];
    }
    explore(cap, -1, &cp); capped_total += cp;
    double B = 0;
    for (long i = 0; i < n1; i++) {
      double v = (double)l1c[i] * cnt[l1n[i]]; B += v;
      if (depth[l1n[i]] <= 32) bRb[b][depth[l1n[i]]] += v;   /* sphere bubble b_R = sum_{|q|=R} sig(q)^2 */
    }
    acc[b][6] += B;
    for (int s = 0; s < 4; s++) { explore(cap, s ^ 1, &cp); capped_total += cp; acc[b][7 + s] += cnt[0]; }
  }
  printf("p=%.6f N=%ld cap=%ld capped=%ld Ta=%s Tb=%s Z=%s\n", p, perb * NB, cap, capped_total, argv[5], argv[6], argv[7]);
  double mean[NQ], se[NQ];
  for (int q = 0; q < NQ; q++) {
    double m = 0, v = 0, bm[NB];
    for (int b = 0; b < NB; b++) {
      double x = acc[b][q] / perb;
      if (q >= 11) x = p * ((q < 13) ? nTa : nTb) * acc[b][q - 4] / perb;
      bm[b] = x; m += x / NB;
    }
    for (int b = 0; b < NB; b++) v += (bm[b] - m) * (bm[b] - m) / (NB - 1);
    mean[q] = m; se[q] = sqrt(v / NB);
    printf("%s %.6g %.3g\n", QN[q], mean[q], se[q]);
  }
  for (int D = 1; D <= Dmax; D++) {
    double ma = 0, mb = 0, va = 0, vb = 0, ra[NB], rb[NB];
    for (int b = 0; b < NB; b++) { ra[b] = shA[b][D] / acc[b][0]; rb[b] = shB[b][D] / acc[b][0]; ma += ra[b] / NB; mb += rb[b] / NB; }
    for (int b = 0; b < NB; b++) { va += (ra[b] - ma) * (ra[b] - ma) / (NB - 1); vb += (rb[b] - mb) * (rb[b] - mb) / (NB - 1); }
    printf("shareA %d %.6g %.3g shareB %d %.6g %.3g\n", D, ma, sqrt(va / NB), D, mb, sqrt(vb / NB));
  }
  for (int Rr = 0; Rr <= Dmax; Rr++) {
    double m = 0, v = 0, bm[NB];
    for (int b = 0; b < NB; b++) { bm[b] = bRb[b][Rr] / perb; m += bm[b] / NB; }
    for (int b = 0; b < NB; b++) v += (bm[b] - m) * (bm[b] - m) / (NB - 1);
    printf("bR %d %.6g %.3g\n", Rr, m, sqrt(v / NB));
  }
  return 0;
}
