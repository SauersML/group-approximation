/* brratio.c -- Br / TJT for a percolation-cluster spine on Z^2.
 *
 * Spine Z = edge set of the infinite cluster of Bernoulli(pp) bond
 * percolation on Z^2 (proxy: the clusters touching the boundary of a box
 * with margin M around the volume).  Given Z, edges of the plain volume
 * Lambda are open with prob 1 (if in Z) or r (the xi layer).
 *
 * Volumes (type):
 *   0  straight path u=(0,0) -> v=(n,0)                    (route R2 empty)
 *   1  rectangle boundary n x h, u=(0,0), v=(n,0): two parallel routes,
 *      bottom (length n) and top (length n+2h)             (h >= 2)
 *
 * Quantities, all exact functionals of Z (xi integrated out exactly where
 * possible, sampled otherwise):
 *   t(A)   = E r^{N(A)},  N(A) = #edges of A not in Z   (A a cyclic interval)
 *   T(u,x) = P(u <-> x in omega cap Lambda) via inclusion-exclusion of arcs
 *   Br     = E sum_f P^Z(f pivotal for u<->v and bridging)  (definition of
 *            fpbs-annealed-pivotal-factorization-off-spine-bridges)
 * Importance sampling: when estimating a functional that needs the edges of a
 * set A all omega-open, the percolation state of each edge of A is sampled
 * with prob pp/a (a = pp + (1-pp) r) instead of pp; weight a^|A| r^{-C(A)}.
 * The off-Lambda environment is sampled once per env and reused (it is
 * independent of the Lambda edges); the Lambda edges are resampled K times.
 *
 * Output: one line per batch of envs with batch means of all quantities.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static uint64_t S[4];
static inline uint64_t rotl(const uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t nxt(void) {
  const uint64_t res = rotl(S[1] * 5, 7) * 9, t = S[1] << 17;
  S[2] ^= S[0]; S[3] ^= S[1]; S[1] ^= S[2]; S[0] ^= S[3]; S[2] ^= t; S[3] = rotl(S[3], 45);
  return res;
}
static inline double unif(void) { return (nxt() >> 11) * 0x1.0p-53; }
static void seed_rng(uint64_t sd) {
  for (int i = 0; i < 4; i++) { sd += 0x9e3779b97f4a7c15ULL; uint64_t z = sd;
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    S[i] = z ^ (z >> 31); }
}

static int *par;
static inline int fnd(int x) { while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; } return x; }
static inline void uni(int a, int b) { a = fnd(a); b = fnd(b); if (a != b) { if (a < b) par[b] = a; else par[a] = b; } }

/* small union-find on compressed class ids */
static int *sp; static char *sflag;
static inline int sf(int x) { while (sp[x] != x) { sp[x] = sp[sp[x]]; x = sp[x]; } return x; }
static inline void su(int a, int b) { a = sf(a); b = sf(b); if (a != b) { sp[b] = a; sflag[a] |= sflag[b]; } }

static int P, n, h, type, K, ncls;
static double pp, r, a;
static int *wx, *wy;      /* volume vertices w_0..w_{P-1} (path: w_0..w_n, P=n edges) */
static int *cid;          /* compressed class id of w_j */
static char *cinf;        /* class touches boundary */
static int NV;            /* number of volume vertices */
static char *open_, *inZ; /* per volume edge k=1..P */
static char *vz;          /* vertex in V(Z cap Lambda) */

/* edge k (1..P) joins vertex e0(k) and e1(k) */
static inline int e0(int k) { return k - 1; }
static inline int e1(int k) { return (type == 0) ? k : (k % P); }

/* sample percolation states of volume edges; edges with tilt[k] use pp/a.
   returns log-weight contributions via *C (closed tilted count) and computes inZ. */
static char *tilt;
static void sample_Z(int *Ctilt) {
  double qt = pp / a; int C = 0;
  for (int k = 1; k <= P; k++) {
    double q = tilt[k] ? qt : pp;
    open_[k] = unif() < q;
    if (tilt[k] && !open_[k]) C++;
  }
  for (int i = 0; i < ncls; i++) { sp[i] = i; sflag[i] = cinf[i]; }
  for (int k = 1; k <= P; k++) if (open_[k]) su(cid[e0(k)], cid[e1(k)]);
  for (int k = 1; k <= P; k++) inZ[k] = open_[k] && sflag[sf(cid[e0(k)])];
  *Ctilt = C;
}

/* cyclic interval (s, len): edges s, s+1, ..., s+len-1 (mod P, 1-based) */
static inline int cyc(int k) { return ((k - 1) % P + P) % P + 1; }
static double est_t(int s, int len) {
  if (len == 0) return 1.0;
  memset(tilt, 0, P + 1);
  for (int i = 0; i < len; i++) tilt[cyc(s + i)] = 1;
  double acc = 0, alen = pow(a, len);
  for (int rep = 0; rep < K; rep++) {
    int C; sample_Z(&C);
    int N = 0; for (int i = 0; i < len; i++) if (!inZ[cyc(s + i)]) N++;
    acc += alen * pow(r, N - C);
  }
  return acc / K;
}

/* Br contribution with f on route R: R given as vertex list rv[0..lr] from u to v and
   edge list re[1..lr]; other route O as vertex list ov[0..lo], edges oe[1..lo] (lo may be 0). */
#define GB 12
static double brk[GB];
static double est_br_route(int lr, const int *rv, const int *re, int lo, const int *ov, const int *oe) {
  memset(tilt, 0, P + 1);
  for (int i = 1; i <= lr; i++) tilt[re[i]] = 1;
  double acc = 0, alen = pow(a, lr);
  char *pre = malloc(lr + 2), *suf = malloc(lr + 2);
  for (int rep = 0; rep < K; rep++) {
    int C; sample_Z(&C);
    for (int j = 0; j < NV; j++) vz[j] = 0;
    for (int k = 1; k <= P; k++) if (inZ[k]) { vz[e0(k)] = 1; vz[e1(k)] = 1; }
    int N = 0; for (int i = 1; i <= lr; i++) if (!inZ[re[i]]) N++;
    if (N == 0) continue;
    /* other route: sample xi, find reach from u and from v */
    int blocked, ureach = vz[rv[0]], vreach = vz[rv[lr]];
    if (lo == 0) blocked = 1;
    else {
      int first = -1, last = -1;
      for (int i = 1; i <= lo; i++) {
        int om = inZ[oe[i]] || (unif() < r);
        if (!om) { if (first < 0) first = i; last = i; }
      }
      blocked = first >= 0;
      if (blocked) {
        for (int i = 0; i < first; i++) ureach |= vz[ov[i]];
        for (int i = last; i <= lo; i++) vreach |= vz[ov[i]];
      }
    }
    if (!blocked) continue;
    /* prefix OR of vz on route vertices 0..k-1, suffix OR on k..lr */
    pre[0] = 0; for (int i = 0; i < lr; i++) pre[i + 1] = pre[i] | vz[rv[i]];
    suf[lr + 1] = 0; for (int i = lr; i >= 0; i--) suf[i] = suf[i + 1] | vz[rv[i]];
    int cnt = 0;
    for (int k = 1; k <= lr; k++) if (!inZ[re[k]]) {
      int ul = ureach | pre[k];      /* vertices rv[0..k-1] */
      int vl = vreach | suf[k];      /* vertices rv[k..lr] */
      if (ul && vl) cnt++;
    }
    if (cnt) {
      double w = alen * pow(r, N - 1 - C) * cnt;
      acc += w;
      int g = N < GB ? N : GB - 1; brk[g] += w / K;
    }
  }
  free(pre); free(suf);
  return acc / K;
}

int main(int argc, char **argv) {
  if (argc < 11) { fprintf(stderr, "usage: type n h pp r M envs K batch seed\n"); return 1; }
  type = atoi(argv[1]); n = atoi(argv[2]); h = atoi(argv[3]); pp = atof(argv[4]); r = atof(argv[5]);
  int M = atoi(argv[6]), envs = atoi(argv[7]); K = atoi(argv[8]); int batch = atoi(argv[9]);
  seed_rng(strtoull(argv[10], 0, 10));
  a = pp + (1 - pp) * r;
  if (type == 0) h = 0;
  int Wd = n + 2 * M + 1, Ht = h + 2 * M + 1, NVt = Wd * Ht;
  if (type == 0) { P = n; NV = n + 1; } else { P = 2 * n + 2 * h; NV = P; }
  wx = malloc(sizeof(int) * (NV + 1)); wy = malloc(sizeof(int) * (NV + 1));
  if (type == 0) for (int j = 0; j <= n; j++) { wx[j] = M + j; wy[j] = M; }
  else {
    int j = 0;
    for (int i = 0; i < n; i++) { wx[j] = M + i; wy[j] = M; j++; }
    for (int i = 0; i < h; i++) { wx[j] = M + n; wy[j] = M + i; j++; }
    for (int i = 0; i < n; i++) { wx[j] = M + n - i; wy[j] = M + h; j++; }
    for (int i = 0; i < h; i++) { wx[j] = M; wy[j] = M + h - i; j++; }
  }
  /* mark lattice edges of Lambda: hor[x,y] joins (x,y)-(x+1,y); ver[x,y] joins (x,y)-(x,y+1) */
  char *inLh = calloc(NVt, 1), *inLv = calloc(NVt, 1);
  for (int k = 1; k <= P; k++) {
    int A = e0(k), B = e1(k);
    int x0 = wx[A], y0 = wy[A], x1 = wx[B], y1 = wy[B];
    if (y0 == y1) { int x = x0 < x1 ? x0 : x1; inLh[y0 * Wd + x] = 1; }
    else { int y = y0 < y1 ? y0 : y1; inLv[y * Wd + x0] = 1; }
  }
  par = malloc(sizeof(int) * (NVt + 1));
  cid = malloc(sizeof(int) * (NV + 1)); cinf = malloc(NV + 1);
  sp = malloc(sizeof(int) * (NV + 1)); sflag = malloc(NV + 1);
  open_ = malloc(P + 2); inZ = malloc(P + 2); tilt = malloc(P + 2); vz = malloc(NV + 1);
  int *root = malloc(sizeof(int) * (NV + 1));

  /* interval lists */
  int nq = 0;
  /* quantities: tu[j] = T(u,w_j), tv[j] = T(w_j,v) for j=0..NV-1; Tuv; Br; q; theta; brk */
  int NQ = 2 * NV + 4 + GB;
  double *bsum = calloc(NQ, sizeof(double)), *q = calloc(NQ, sizeof(double));
  /* routes */
  int lr1 = n, *rv1 = malloc(sizeof(int) * (n + 1)), *re1 = malloc(sizeof(int) * (n + 1));
  for (int i = 0; i <= n; i++) rv1[i] = i;
  for (int i = 1; i <= n; i++) re1[i] = i;
  int lr2 = (type == 0) ? 0 : n + 2 * h;
  int *rv2 = malloc(sizeof(int) * (lr2 + 1)), *re2 = malloc(sizeof(int) * (lr2 + 1));
  if (type == 1) { /* top route from u=w_0 to v=w_n: w_0, w_{P-1}, ..., w_n; edges P, P-1, ..., n+1 */
    for (int i = 0; i <= lr2; i++) rv2[i] = (P - i) % P;
    for (int i = 1; i <= lr2; i++) re2[i] = P - i + 1;
  }
  printf("# type=%d n=%d h=%d pp=%g r=%g M=%d envs=%d K=%d a=%.10g P=%d NV=%d\n", type, n, h, pp, r, M, envs, K, a, P, NV);
  int nb = 0;
  for (int env = 0; env < envs; env++) {
    for (int i = 0; i <= NVt; i++) par[i] = i;
    uint64_t thr = (uint64_t)(pp * 18446744073709551616.0);
    for (int y = 0; y < Ht; y++) for (int x = 0; x < Wd; x++) {
      int v = y * Wd + x;
      if (x + 1 < Wd && !inLh[v] && nxt() < thr) uni(v, v + 1);
      if (y + 1 < Ht && !inLv[v] && nxt() < thr) uni(v, v + Wd);
      if (x == 0 || y == 0 || x == Wd - 1 || y == Ht - 1) uni(v, NVt);
    }
    int rb = fnd(NVt);
    ncls = 0;
    for (int j = 0; j < NV; j++) {
      int rt = fnd(wy[j] * Wd + wx[j]); int c = -1;
      for (int i = 0; i < ncls; i++) if (root[i] == rt) { c = i; break; }
      if (c < 0) { c = ncls; root[ncls] = rt; cinf[ncls] = (fnd(rt) == rb); ncls++; }
      cid[j] = c;
    }
    int anyinf = 0; for (int i = 0; i < ncls; i++) anyinf |= cinf[i];
    for (int i = 0; i < NQ; i++) q[i] = 0;
    /* T(u,w_j), T(w_j,v) */
    if (type == 0) {
      for (int j = 0; j <= n; j++) { q[j] = est_t(1, j); q[NV + j] = est_t(j + 1, n - j); }
      q[2 * NV] = q[n];
    } else {
      double tf = est_t(1, P);
      for (int j = 0; j < NV; j++) {
        q[j] = (j == 0) ? 1.0 : est_t(1, j) + est_t(j + 1, P - j) - tf;
        int l = ((j - n) % P + P) % P;
        q[NV + j] = (l == 0) ? 1.0 : est_t(n + 1, l) + est_t(n + 1 + l, P - l) - tf;
      }
      q[2 * NV] = q[n];
    }
    for (int g = 0; g < GB; g++) brk[g] = 0;
    double br = est_br_route(lr1, rv1, re1, lr2, rv2, re2);
    if (type == 1) br += est_br_route(lr2, rv2, re2, lr1, rv1, re1);
    q[2 * NV + 1] = br;
    q[2 * NV + 2] = anyinf;
    /* theta proxy: middle vertex of route 1 in C_inf with untilted volume edges */
    memset(tilt, 0, P + 1); int C; sample_Z(&C);
    { int jm = n / 2; for (int i = 0; i < ncls; i++) { sp[i] = i; sflag[i] = cinf[i]; }
      for (int k = 1; k <= P; k++) if (open_[k]) su(cid[e0(k)], cid[e1(k)]);
      q[2 * NV + 3] = sflag[sf(cid[jm])]; }
    for (int g = 0; g < GB; g++) q[2 * NV + 4 + g] = brk[g];
    for (int i = 0; i < NQ; i++) bsum[i] += q[i];
    nb++;
    if (nb == batch || env == envs - 1) {
      printf("B %d", nb);
      for (int i = 0; i < NQ; i++) printf(" %.8e", bsum[i] / nb);
      printf("\n"); fflush(stdout);
      for (int i = 0; i < NQ; i++) bsum[i] = 0; nb = 0;
    }
  }
  (void)nq;
  return 0;
}
