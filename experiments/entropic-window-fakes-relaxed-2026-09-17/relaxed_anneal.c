/* Relaxed simulated annealing for an F_2-linear minimal-window fake.
   Input: file from relaxed_target.py.  usage: relaxed_anneal target.txt d s seed iters [lambda]
   x_g = coordinate block g of F_2^(m d); codeword j = s rows supported on its read blocks.
   rank(S) = d |S_x| + rank of the rows of the codewords in S with the blocks of S_x deleted.
   loss = sum over translation classes of sum |rank(S) - rank(rep)|  +  lambda * max(0, Phi_num - (d-1)),
   Phi_num = rank(y_0) + rank(x_1 y_F) - rank(y_F).  At loss 0 the configuration satisfies (I),(D),(T) exactly and
   Phi = Phi_num / d < 1.  Prints the rows as hex (verify with ../entropic-window-fakes-2026-09-17/verify_linear.py). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef unsigned __int128 u128;
static int m, r, d, s, nread[12], rd[12][16], N, *col, *rep, my0, mx1yF, myF;
static u128 mask[12], W[12][40], bmask[16];
static unsigned long long rng = 88172645463325252ULL;
static unsigned long long xr(void){ rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static int pc128(u128 v){ return __builtin_popcountll((unsigned long long)v) + __builtin_popcountll((unsigned long long)(v >> 64)); }
static int rank_of(int S){
  u128 keep = 0; int nx = 0;
  for (int g = 0; g < m; g++){ if (S >> g & 1) nx++; else keep |= bmask[g]; }
  u128 piv[128]; int np = 0; /* basis with distinct leading bits, kept sorted descending */
  for (int j = 0; j < r; j++) if (S >> (m + j) & 1) for (int k = 0; k < s; k++){
    u128 v = W[j][k] & keep;
    for (int b = 0; b < np && v; b++){ u128 w = v ^ piv[b]; if (w < v) v = w; }
    if (v){ int p = np++; while (p > 0 && piv[p-1] < v){ piv[p] = piv[p-1]; p--; } piv[p] = v; }
  }
  (void)pc128;
  return nx * d + np;
}
static u128 rnd128(void){ return ((u128)xr() << 64) | xr(); }
int main(int argc, char **argv){
  FILE *f = fopen(argv[1], "r"); d = atoi(argv[2]); s = atoi(argv[3]);
  unsigned long long seed = atoll(argv[4]); long iters = atol(argv[5]); int lam = argc > 6 ? atoi(argv[6]) : 4;
  rng ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
  if (fscanf(f, "%d %d", &m, &r) != 2) return 2;
  if (m * d > 128 || s > 40){ fprintf(stderr, "too big\n"); return 3; }
  for (int g = 0; g < m; g++){ bmask[g] = 0; for (int b = 0; b < d; b++) bmask[g] |= (u128)1 << (g * d + b); }
  for (int j = 0; j < r; j++){ if (fscanf(f, "%d", &nread[j]) != 1) return 2; mask[j] = 0;
    for (int i = 0; i < nread[j]; i++){ if (fscanf(f, "%d", &rd[j][i]) != 1) return 2; mask[j] |= bmask[rd[j][i]]; } }
  N = 1 << (m + r); col = malloc(sizeof(int) * N); rep = malloc(sizeof(int) * N);
  for (int S = 0; S < N; S++){ if (fscanf(f, "%d", &col[S]) != 1) return 2; }
  if (fscanf(f, "%d %d %d", &my0, &mx1yF, &myF) != 3) return 2;
  int nc = 0; for (int S = 0; S < N; S++) if (col[S] + 1 > nc) nc = col[S] + 1;
  int *first = malloc(sizeof(int) * nc); for (int c = 0; c < nc; c++) first[c] = -1;
  for (int S = 0; S < N; S++){ if (first[col[S]] < 0) first[col[S]] = S; rep[S] = first[col[S]]; }
  for (int j = 0; j < r; j++) for (int k = 0; k < s; k++) W[j][k] = rnd128() & mask[j];
  int *h = malloc(sizeof(int) * N), *h2 = malloc(sizeof(int) * N);
  #define LOSS(H) ({ long L = 0; for (int S = 0; S < N; S++) L += labs((long)H[S] - H[rep[S]]); \
     long ph = (long)H[my0] + H[mx1yF] - H[myF]; if (ph > d - 1) L += lam * (ph - (d - 1)); L; })
  for (int S = 0; S < N; S++) h[S] = rank_of(S);
  long loss = LOSS(h), best = loss;
  for (long it = 0; it < iters && loss > 0; it++){
    int j = xr() % r, k = xr() % s;
    int bi = xr() % nread[j], b = rd[j][bi] * d + (int)(xr() % d);
    W[j][k] ^= (u128)1 << b;
    for (int S = 0; S < N; S++) h2[S] = (S >> (m + j) & 1) ? rank_of(S) : h[S];
    long nl = LOSS(h2);
    double T = 2.0 * (1.0 - (double)it / iters) + 0.08;
    if (nl <= loss || (double)(xr() % 1000000) / 1e6 < exp((loss - nl) / T)){
      loss = nl; int *t = h; h = h2; h2 = t; if (loss < best) best = loss;
    } else W[j][k] ^= (u128)1 << b;
    if ((it & 0xfffff) == 0){ fprintf(stderr, "it %ld loss %ld best %ld\n", it, loss, best); }
  }
  long ph = (long)h[my0] + h[mx1yF] - h[myF];
  printf("final loss %ld best %ld phi_num %ld d %d\n", loss, best, ph, d);
  if (loss == 0){
    for (int j = 0; j < r; j++){ printf("y%d:", j); for (int k = 0; k < s; k++) printf(" 0x%llx%016llx", (unsigned long long)(W[j][k] >> 64), (unsigned long long)W[j][k]); printf("\n"); }
  }
  return loss == 0 ? 0 : 1;
}
