/* vrepair.c -- repair-move annealing over exact free S4/S3 gluings.
 *
 * Same state space as vglue.c: a = pairing x <-> x^1, b = free S4 structure, c = tau^-1 c0 tau with
 * tau in the centralizer C2 wr S_(k/2) of a, so a^2, b^3, (ab)^4, c^2, (ac)^3 hold exactly on every
 * state. The difference is the move. With probability 1-noise the move is a repair: take a
 * violated instance x.r != x, a random c-letter at position j of r, the forward point p reached
 * before that letter and the backward point q reached after it; conjugate c by the pair swap tau
 * (commuting with a, fixing the pair of p) with tau(c(p)) = q, so that afterwards c(p) = q and the
 * instance closes if its prefix and suffix are unchanged. With probability noise the move is a
 * random pair flip or swap, as in vglue.c. Acceptance is Metropolis on the number of violated
 * instances, with a geometric temperature schedule; runs stop at 0.
 * Numerics only suggest; they prove nothing about soficity of V.
 *
 * usage: vrepair k iters T0 T1 noise seed relfile      (k divisible by 24)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXW 1024
#define MAXR 16

static unsigned long long rs;
static unsigned long long rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void){ return (rnd() >> 11) * (1.0/9007199254740992.0); }

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

static int k, NR; static int W[MAXR][MAXW], WL[MAXR];
static int *P[6];                       /* 0=a 1=b 2=c, 3..5 inverses (P[3]=a, P[5]=c) */
static int *viol[MAXR], nviol[MAXR];

static long evaluate(void){
  long tot = 0;
  for (int r = 0; r < NR; r++){
    int n = 0; const int *w = W[r]; int L = WL[r];
    for (int x = 0; x < k; x++){ int y = x; for (int j = 0; j < L; j++) y = P[w[j]][y]; if (y != x) viol[r][n++] = x; }
    nviol[r] = n; tot += n;
  }
  return tot;
}

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
static int uf_find(int *par, int x){ while (par[x] != x){ par[x] = par[par[x]]; x = par[x]; } return x; }

/* tau swaps pair(u) with pair(v) so that u <-> v, a(u) <-> a(v) (flip if they share a pair) */
static int tau_of(int z, int u, int v){
  if ((u ^ 1) == v){ if (z == u) return v; if (z == v) return u; return z; }
  if (z == u) return v;
  if (z == v) return u;
  if (z == (u ^ 1)) return v ^ 1;
  if (z == (v ^ 1)) return u ^ 1;
  return z;
}

int main(int argc, char **argv){
  if (argc < 8){ fprintf(stderr, "usage: vrepair k iters T0 T1 noise seed relfile\n"); return 1; }
  k = atoi(argv[1]); long iters = atol(argv[2]); double T0 = atof(argv[3]), T1 = atof(argv[4]), noise = atof(argv[5]);
  rs = strtoull(argv[6], 0, 10) * 2654435761ULL + 777; for (int i = 0; i < 20; i++) rnd();
  if (k % 24){ fprintf(stderr, "k must be divisible by 24\n"); return 1; }
  FILE *f = fopen(argv[7], "r"); if (!f){ fprintf(stderr, "cannot open %s\n", argv[7]); return 1; }
  char line[4096];
  while (NR < MAXR && fgets(line, sizeof line, f)){ int i = 0; int L = parse_seq(line, &i, W[NR], 0); if (L > 0) WL[NR++] = L; }
  fclose(f);
  for (int g = 0; g < 6; g++) P[g] = malloc(sizeof(int)*k);
  for (int r = 0; r < NR; r++) viol[r] = malloc(sizeof(int)*k);
  int *aux = malloc(sizeof(int)*k), *save = malloc(sizeof(int)*k), *tt = malloc(sizeof(int)*k), *par = malloc(sizeof(int)*k);
  int *best = malloc(sizeof(int)*k);
  for (int x = 0; x < k; x++) P[0][x] = x ^ 1;
  const int g4[2][4] = {{1,0,2,3},{0,2,3,1}};
  const int g3[2][4] = {{1,0,2,0},{2,1,0,0}};
  int *o4[2] = {aux, P[1]}; if (build_free(4, 2, g4, 0, k/24, o4) != 24){ fprintf(stderr, "S4 size\n"); return 1; }
  for (int x = 0; x < k; x++) if (aux[x] != P[0][x]){ fprintf(stderr, "S4 pairing\n"); return 1; }
  int *o3[2] = {aux, P[2]}; if (build_free(3, 2, g3, 0, k/6, o3) != 6){ fprintf(stderr, "S3 size\n"); return 1; }
  for (int x = 0; x < k; x++) if (aux[x] != P[0][x]){ fprintf(stderr, "S3 pairing\n"); return 1; }
  int h = k/2; int *pi = malloc(sizeof(int)*h);
  for (int i = 0; i < h; i++) pi[i] = i;
  for (int i = h-1; i > 0; i--){ int j = rnd() % (i+1); int t = pi[i]; pi[i] = pi[j]; pi[j] = t; }
  for (int i = 0; i < h; i++){ int fl = rnd() & 1; tt[2*i] = 2*pi[i] + fl; tt[2*i+1] = 2*pi[i] + (1-fl); }
  for (int x = 0; x < k; x++) aux[tt[x]] = x;
  memcpy(save, P[2], sizeof(int)*k);
  for (int x = 0; x < k; x++) P[2][x] = aux[save[tt[x]]];
  for (int x = 0; x < k; x++){ P[3][x] = P[0][x]; P[5][x] = P[2][x]; P[4][P[1][x]] = x; }
  long cur = evaluate(), bestv = cur, base = cur, solved_at = -1, repairs = 0, accepted = 0;
  memcpy(best, P[2], sizeof(int)*k);
  time_t t0 = time(0);
  int S[8], Sold[8];
  for (long it = 0; it < iters && cur > 0; it++){
    double T = T0 * pow(T1/T0, (double)it/iters);
    int u, v;                                               /* tau swaps pair(u), pair(v) with u <-> v */
    if (urand() >= noise){
      int r = rnd() % NR; if (nviol[r] == 0) continue;
      int x = viol[r][rnd() % nviol[r]]; const int *w = W[r]; int L = WL[r];
      int cpos[MAXW], nc = 0; for (int j = 0; j < L; j++) if (w[j] == 2 || w[j] == 5) cpos[nc++] = j;
      if (nc == 0) continue;
      int j = cpos[rnd() % nc];
      int p = x; for (int t = 0; t < j; t++) p = P[w[t]][p];
      int q = x; for (int t = L-1; t > j; t--) q = P[(w[t] + 3) % 6][q];
      if (q == p || q == (p ^ 1) || P[2][p] == q) continue;
      u = P[2][p]; v = q; repairs++;
    } else {
      u = rnd() % k; v = rnd() % k; if ((u >> 1) == (v >> 1) && u == v) continue;
    }
    /* changed points: pair(u), pair(v), and their c-images */
    int ns = 0; int cand[8] = {u, u ^ 1, v, v ^ 1, P[2][u], P[2][u ^ 1], P[2][v], P[2][v ^ 1]};
    for (int t = 0; t < 8; t++){ int z = cand[t], dup = 0; for (int s = 0; s < ns; s++) if (S[s] == z) dup = 1; if (!dup) S[ns++] = z; }
    for (int s = 0; s < ns; s++) Sold[s] = P[2][S[s]];
    int nv[8]; for (int s = 0; s < ns; s++) nv[s] = tau_of(P[2][tau_of(S[s], u, v)], u, v);
    for (int s = 0; s < ns; s++){ P[2][S[s]] = nv[s]; P[5][S[s]] = nv[s]; }
    long nd = evaluate();
    if (nd <= cur || urand() < exp((double)(cur - nd) / T)){
      cur = nd; accepted++;
      if (cur < bestv){ bestv = cur; memcpy(best, P[2], sizeof(int)*k); if (cur == 0) solved_at = it; }
    } else {
      for (int s = 0; s < ns; s++){ P[2][S[s]] = Sold[s]; P[5][S[s]] = Sold[s]; }
      evaluate();
    }
  }
  memcpy(P[2], best, sizeof(int)*k); memcpy(P[5], best, sizeof(int)*k);
  long fin = evaluate();
  int shortbad = 0, fpf = 1;
  const char *SH[6] = {"a^2", "b^3", "(ab)^4", "c^2", "(ac)^3", "c^-1(ac)^2a"};
  for (int r = 0; r < 6; r++){
    int w[64]; int i = 0; int L = parse_seq(SH[r], &i, w, 0);
    for (int x = 0; x < k; x++){ int y = x; for (int j = 0; j < L; j++) y = P[w[j]][y]; if (y != x){ shortbad++; break; } }
  }
  for (int x = 0; x < k; x++) if (P[0][x] == x || P[1][x] == x || P[2][x] == x || P[2][P[2][x]] != x) fpf = 0;
  for (int x = 0; x < k; x++) par[x] = x;
  for (int x = 0; x < k; x++) for (int g = 0; g < 3; g++){ int p = uf_find(par, x), q = uf_find(par, P[g][x]); if (p != q) par[p] = q; }
  int nco = 0, big = 0;
  for (int x = 0; x < k; x++) if (uf_find(par, x) == x){ nco++; int sz = 0; for (int z = 0; z < k; z++) if (uf_find(par, z) == x) sz++; if (sz > big) big = sz; }
  printf("k=%d iters=%ld T0=%g T1=%g noise=%g seed=%s rel=%s short_bad=%d fpf=%d base_avg=%.5f best_avg=%.5f per:",
         k, iters, T0, T1, noise, argv[6], argv[7], shortbad, fpf, (double)base/(NR*k), (double)fin/(NR*k));
  for (int r = 0; r < NR; r++) printf(" %.4f", (double)nviol[r]/k);
  printf(" solved_at=%ld repairs=%ld accepted=%ld components=%d largest=%d secs=%ld\n",
         solved_at, repairs, accepted, nco, big, (long)(time(0) - t0));
  return 0;
}
