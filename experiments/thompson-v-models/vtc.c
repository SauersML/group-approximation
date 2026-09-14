/* vtc.c -- constructive search for free S4/S3 gluings that satisfy long words.
 *
 * Generators of Bleak--Quick (2.4), right action. a is the pairing x <-> x^1, b is a free S4
 * structure (block j = points 24j..24j+23), and c is searched. A partial fixed-point-free
 * involution c is extended one pair at a time. Every relator instance through a new c-edge is
 * scanned forwards and backwards (Felsch-style scanning); a scan with one gap deduces c there.
 * The hexagon relator (ac)^3 is a hard constraint, so <a,c> acts freely on every completed
 * gluing; the relators of relfile are soft only when a budget is given. New blocks are
 * introduced canonically (first point of the first untouched block). This removes the
 * S4 wr S_m symmetry of (a, b), and in transitive mode every solution is transitive.
 *   budget 0 : exact depth-first search, node limit per restart, random candidate order.
 *   budget B>0 : tolerate up to B soft conflicts (closure mismatch or illegal deduction).
 *   budget -1 : tolerate all soft conflicts; with sample S the S first candidates are tried and
 *               ranked by the soft conflicts they cause.
 * Numerics only suggest; they prove nothing about soficity of V.
 *
 *   heur 0 : branch on the first undefined point; heur 1 : on the point ending the most nearly
 *            complete relator scans (see select_point); heur 2 : among the MTOP best-scored
 *            points, branch on the one with fewest candidates that survive propagation.
 * usage: vtc k relfile seed restarts maxnodes budget transitive sample heur   (k divisible by 24)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define MAXW 1024
#define MAXR 16
#define MAXROT 512

static unsigned long long rs;
static unsigned long long rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

/* letters 0=a 1=b 2=c, inverses 3..5 (same syntax as vglue.c) */
static int parse_seq(const char *s, int *i, int *out, int n){
  while (s[*i] && s[*i] != ')' && s[*i] != '\n' && s[*i] != '\r'){
    int buf[MAXW]; int mm = 0;
    if (s[*i] == '('){ (*i)++; mm = parse_seq(s, i, buf, 0); if (s[*i] == ')') (*i)++; }
    else if (s[*i] >= 'a' && s[*i] <= 'c'){ buf[0] = s[*i] - 'a'; mm = 1; (*i)++; }
    else { (*i)++; continue; }
    int rep = 1, inv = 0;
    if (s[*i] == '^'){
      (*i)++; if (s[*i] == '-'){ inv = 1; (*i)++; }
      rep = atoi(s + *i); while (s[*i] >= '0' && s[*i] <= '9') (*i)++;
    }
    for (int r = 0; r < rep; r++){
      if (inv) for (int j = mm-1; j >= 0; j--) out[n++] = (buf[j] + 3) % 6;
      else for (int j = 0; j < mm; j++) out[n++] = buf[j];
    }
  }
  return n;
}

static int k, m, NR, transitive, sample;
static int W[MAXR][MAXW], WL[MAXR];
static int *A, *Bf, *Bi, *C;
static int NRot; static int *Rot[MAXROT]; static int RotL[MAXROT], RotHard[MAXROT];
static int *QU, *QV, *QH; static int qh, qt, QCAP;
static int *trail; static int tl, touched;
static long viol, budget, nodes, maxnodes;

static inline int ap(int l, int x){
  switch (l){ case 0: case 3: return A[x]; case 1: return Bf[x]; case 4: return Bi[x]; default: return C[x]; }
}
static int soft(int hard){
  if (hard) return 0;
  if (budget < 0 || viol < budget){ viol++; return 1; }
  return 0;
}
static int push(int u, int v, int hard){
  if (qt >= QCAP) return 0;
  QU[qt] = u; QV[qt] = v; QH[qt] = hard; qt++; return 1;
}
/* scan rotation r from point p: 1 = consistent (possibly with a queued deduction), 0 = conflict */
static int scan(int r, int p){
  const int *w = Rot[r]; int n = RotL[r];
  int f = 0, cur = p;
  while (f < n){ int nx = ap(w[f], cur); if (nx < 0) break; cur = nx; f++; }
  if (f == n) return cur == p ? 1 : soft(RotHard[r]);
  int g = n, cb = p;
  while (g > f){ int nx = ap((w[g-1] + 3) % 6, cb); if (nx < 0) break; cb = nx; g--; }
  if (g == f) return cur == cb ? 1 : soft(RotHard[r]);
  if (g == f + 1 && !push(cur, cb, RotHard[r])) return 0;
  return 1;
}
static int define(int x, int y, int hard){
  qh = qt = 0; push(x, y, hard);
  while (qh < qt){
    int u = QU[qh], v = QV[qh], h = QH[qh]; qh++;
    if (C[u] == v) continue;
    if (u == v || v == A[u] || C[u] >= 0 || C[v] >= 0){ if (!soft(h)) return 0; continue; }
    C[u] = v; C[v] = u; trail[tl++] = u;
    for (int r = 0; r < NRot; r++){ if (!scan(r, u)) return 0; if (!scan(r, v)) return 0; }
  }
  return 1;
}
static void undo(int mark){
  while (tl > mark){ int u = trail[--tl]; int v = C[u]; C[u] = -1; if (v >= 0) C[v] = -1; }
}

/* heuristic 1: the undefined point that ends the most nearly complete relator scans.
 * Each instance (start p, relator r) is scanned forwards and backwards up to its first gap;
 * both gap points get weight 4^(number of c-letters already traversed). */
#define MTOP 6
static int heur; static double *sc; static int top[MTOP], ntop;
static int select_point(void){
  int np = 24*touched, x = -1; double best = -1;
  if (heur == 0){ for (int p = 0; p < np; p++) if (C[p] < 0) return p; return -1; }
  for (int p = 0; p < np; p++) sc[p] = 0;
  int hex[6] = {0,2,0,2,0,2};
  for (int p = 0; p < np; p++) for (int r = 0; r <= NR; r++){
    const int *w = r < NR ? W[r] : hex; int n = r < NR ? WL[r] : 6;
    int f = 0, cur = p, cf = 0;
    while (f < n){ int nx = ap(w[f], cur); if (nx < 0) break; if (w[f] == 2 || w[f] == 5) cf++; cur = nx; f++; }
    if (f == n) continue;
    int g = n, cb = p, cg = 0;
    while (g > f){ int nx = ap((w[g-1] + 3) % 6, cb); if (nx < 0) break; if (w[g-1] == 2 || w[g-1] == 5) cg++; cb = nx; g--; }
    double wt = (double)(1ULL << (2 * (cf + cg < 30 ? cf + cg : 30)));
    sc[cur] += wt; if (cb != cur) sc[cb] += wt;
  }
  for (int p = 0; p < np; p++) if (C[p] < 0){
    double s = sc[p] * (1.0 + 1e-6 * (double)(rnd() % 1000));
    if (s > best){ best = s; x = p; }
  }
  if (heur == 2 && x >= 0){                                  /* top MTOP points by score */
    ntop = 0;
    for (int t = 0; t < MTOP; t++){
      int bx = -1; double bs = -1;
      for (int p = 0; p < np; p++) if (C[p] < 0 && sc[p] >= 0 && sc[p] > bs){ bs = sc[p]; bx = p; }
      if (bx < 0) break;
      top[ntop++] = bx; sc[bx] = -1;
    }
  }
  return x;
}
/* legal candidates for c(x): undefined touched points and the canonical new-block point */
static int candidates(int x, int *cand){
  int nc = 0;
  for (int p = 0; p < 24*touched; p++) if (C[p] < 0 && p != x && p != A[x]) cand[nc++] = p;
  if (touched < m) cand[nc++] = 24*touched;
  return nc;
}
/* keep only candidates whose propagation succeeds; stop early once more than limit survive */
static int consistent(int x, int *cand, int nc, int limit){
  int nd = 0;
  for (int i = 0; i < nc && nd <= limit; i++){
    int y = cand[i], mark = tl, ts = touched; long vs = viol;
    if (y >= 24*touched) touched++;
    nodes++;
    int ok = define(x, y, 1);
    undo(mark); touched = ts; viol = vs;
    if (ok) cand[nd++] = y;
  }
  return nd;
}

static int dfs(void){
  if (maxnodes > 0 && nodes >= maxnodes) return -1;
  int t0 = touched, x = select_point();
  if (x < 0){
    if (touched == m) return 1;
    if (transitive) return 0;
    x = 24*touched; touched++; ntop = 0;
  }
  int *cand = malloc(sizeof(int)*(k+1)); long *score = malloc(sizeof(long)*(k+1)); int nc = 0;
  if (heur == 2 && ntop > 0){                               /* fail-first among the top points */
    int *tmp = malloc(sizeof(int)*(k+1)); int bestn = k + 2, nt = ntop, tp[MTOP];
    memcpy(tp, top, sizeof(int)*nt);
    for (int t = 0; t < nt; t++){
      int n0 = candidates(tp[t], tmp); int nd = consistent(tp[t], tmp, n0, bestn - 1);
      if (nd < bestn){ bestn = nd; x = tp[t]; memcpy(cand, tmp, sizeof(int)*nd); nc = nd; }
      if (nd == 0) break;
    }
    free(tmp);
  } else nc = candidates(x, cand);
  for (int i = nc-1; i > 0; i--){ int j = rnd() % (i+1); int t = cand[i]; cand[i] = cand[j]; cand[j] = t; }
  if (sample > 0){
    int ns = sample < nc ? sample : nc;
    for (int i = 0; i < ns; i++){
      int y = cand[i], mark = tl, ts = touched; long vs = viol;
      if (y >= 24*touched) touched++;
      nodes++;
      score[i] = define(x, y, 1) ? viol - vs : 1L << 40;
      undo(mark); touched = ts; viol = vs;
    }
    for (int i = 1; i < ns; i++){                          /* insertion sort by score */
      int y = cand[i]; long s = score[i]; int j = i - 1;
      while (j >= 0 && score[j] > s){ cand[j+1] = cand[j]; score[j+1] = score[j]; j--; }
      cand[j+1] = y; score[j+1] = s;
    }
  }
  for (int i = 0; i < nc; i++){
    int y = cand[i], mark = tl, ts = touched; long vs = viol;
    if (y >= 24*touched) touched++;
    nodes++;
    if (define(x, y, 1)){ int r = dfs(); if (r != 0){ free(cand); free(score); return r; } }
    undo(mark); touched = ts; viol = vs;
    if (maxnodes > 0 && nodes >= maxnodes) break;
  }
  free(cand); free(score); touched = t0;
  return (maxnodes > 0 && nodes >= maxnodes) ? -1 : 0;
}

/* free S4 structure on 24m points, as in vglue.c */
static int find_el(int N, int n, int el[][4], const int *p){
  for (int q = 0; q < N; q++) if (!memcmp(el[q], p, sizeof(int)*n)) return q;
  return -1;
}
static int build_free(int n, int ng, const int gens[][4], int apos, int mm, int **out){
  int el[24][4], mult[24][4], N = 1;
  for (int i = 0; i < n; i++) el[0][i] = i;
  for (int e = 0; e < N; e++) for (int s = 0; s < ng; s++){
    int p[4]; for (int i = 0; i < n; i++) p[i] = gens[s][el[e][i]];
    int f = find_el(N, n, el, p); if (f < 0){ memcpy(el[N], p, sizeof(int)*n); f = N++; }
    mult[e][s] = f;
  }
  int *idx = malloc(sizeof(int)*N*mm); for (int q = 0; q < N*mm; q++) idx[q] = -1;
  int p = 0;
  for (int j = 0; j < mm; j++) for (int e = 0; e < N; e++) if (idx[j*N+e] < 0){
    idx[j*N+e] = p; idx[j*N+mult[e][apos]] = p+1; p += 2;
  }
  for (int j = 0; j < mm; j++) for (int e = 0; e < N; e++) for (int s = 0; s < ng; s++)
    out[s][idx[j*N+e]] = idx[j*N+mult[e][s]];
  free(idx);
  return N;
}
static double word_defect(const int *w, int L){
  int mv = 0;
  for (int x = 0; x < k; x++){ int y = x; for (int j = 0; j < L; j++) y = ap(w[j], y); if (y != x) mv++; }
  return (double)mv / k;
}
static int uf_find(int *par, int x){ while (par[x] != x){ par[x] = par[par[x]]; x = par[x]; } return x; }

int main(int argc, char **argv){
  if (argc < 10){ fprintf(stderr, "usage: vtc k relfile seed restarts maxnodes budget transitive sample heur\n"); return 1; }
  k = atoi(argv[1]); unsigned long long seed = strtoull(argv[3], 0, 10); int restarts = atoi(argv[4]);
  maxnodes = atol(argv[5]); budget = atol(argv[6]); transitive = atoi(argv[7]); sample = atoi(argv[8]);
  heur = atoi(argv[9]); sc = malloc(sizeof(double)*k);
  if (k % 24){ fprintf(stderr, "k must be divisible by 24\n"); return 1; }
  m = k / 24;
  FILE *f = fopen(argv[2], "r"); if (!f){ fprintf(stderr, "cannot open %s\n", argv[2]); return 1; }
  char line[4096];
  while (NR < MAXR && fgets(line, sizeof line, f)){ int i = 0; int L = parse_seq(line, &i, W[NR], 0); if (L > 0) WL[NR++] = L; }
  fclose(f);
  A = malloc(sizeof(int)*k); Bf = malloc(sizeof(int)*k); Bi = malloc(sizeof(int)*k); C = malloc(sizeof(int)*k);
  trail = malloc(sizeof(int)*k); QCAP = 1 << 22;
  QU = malloc(sizeof(int)*QCAP); QV = malloc(sizeof(int)*QCAP); QH = malloc(sizeof(int)*QCAP);
  int *aux = malloc(sizeof(int)*k), *par = malloc(sizeof(int)*k);
  const int g4[2][4] = {{1,0,2,3},{0,2,3,1}};   /* a, b on cylinders 00,01,10,11 */
  int *o4[2] = {aux, Bf};
  if (build_free(4, 2, g4, 0, m, o4) != 24){ fprintf(stderr, "S4 size\n"); return 1; }
  for (int x = 0; x < k; x++){ A[x] = x ^ 1; if (aux[x] != A[x]){ fprintf(stderr, "S4 pairing\n"); return 1; } }
  for (int x = 0; x < k; x++){ Bi[Bf[x]] = x; if (Bf[x]/24 != x/24){ fprintf(stderr, "S4 block\n"); return 1; } }
  int hex[6] = {0,2,0,2,0,2};
  for (int r = 0; r <= NR; r++){
    const int *w = r < NR ? W[r] : hex; int L = r < NR ? WL[r] : 6;
    for (int j = 0; j < L; j++) if (w[j] == 2 || w[j] == 5){
      if (NRot >= MAXROT){ fprintf(stderr, "too many rotations\n"); return 1; }
      Rot[NRot] = malloc(sizeof(int)*L);
      for (int t = 0; t < L; t++) Rot[NRot][t] = w[(j + t) % L];
      RotL[NRot] = L; RotHard[NRot] = (r == NR); NRot++;
    }
  }
  const char *SH[6] = {"a^2", "b^3", "(ab)^4", "c^2", "(ac)^3", "c^-1(ac)^2a"};
  for (int rep = 0; rep < restarts; rep++){
    rs = seed * 2654435761ULL + 1000003ULL * (unsigned long long)rep + 12345; for (int i = 0; i < 20; i++) rnd();
    for (int x = 0; x < k; x++) C[x] = -1;
    tl = 0; touched = 1; viol = 0; nodes = 0;
    time_t t0 = time(0);
    int res = dfs();
    printf("k=%d rel=%s seed=%llu rep=%d maxnodes=%ld budget=%ld transitive=%d sample=%d heur=%d result=%s nodes=%ld viol=%ld",
           k, argv[2], seed, rep, maxnodes, budget, transitive, sample, heur,
           res == 1 ? "COMPLETE" : res == 0 ? "EXHAUSTED" : "LIMIT", nodes, viol);
    if (res == 1){
      int shortbad = 0, fpf = 1; double s = 0;
      for (int r = 0; r < 6; r++){ int w[64]; int i = 0; int L = parse_seq(SH[r], &i, w, 0); if (word_defect(w, L) != 0.0) shortbad++; }
      for (int x = 0; x < k; x++) if (A[x] == x || Bf[x] == x || C[x] == x || C[x] < 0) fpf = 0;
      printf(" short_bad=%d fpf=%d per:", shortbad, fpf);
      for (int r = 0; r < NR; r++){ double d = word_defect(W[r], WL[r]); s += d; printf(" %.4f", d); }
      for (int x = 0; x < k; x++) par[x] = x;
      for (int x = 0; x < k; x++){ int y[3] = {A[x], Bf[x], C[x]}; for (int t = 0; t < 3; t++){ int p = uf_find(par, x), q = uf_find(par, y[t]); if (p != q) par[p] = q; } }
      int nco = 0, big = 0; for (int x = 0; x < k; x++) if (uf_find(par, x) == x) nco++;
      for (int x = 0; x < k; x++){ int sz = 0; if (uf_find(par, x) != x) continue; for (int z = 0; z < k; z++) if (uf_find(par, z) == x) sz++; if (sz > big) big = sz; }
      printf(" avg=%.5f components=%d largest=%d", s / NR, nco, big);
    }
    printf(" secs=%ld\n", (long)(time(0) - t0));
    fflush(stdout);
  }
  return 0;
}
