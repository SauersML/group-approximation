/* Simulated annealing for an F_2-linear representation of an integer polymatroid target.
   Input file (from extract_fake.py via the .txt writer):
     m d r
     s_j nread idx...      (r lines)
     h(S) for S = 0 .. 2^(m+r)-1   (bit order: x_0..x_{m-1}, y_0..y_{r-1})
   x_g = coordinate block g of F_2^(m d); y_j = row space of s_j vectors supported on its read blocks.
   usage: linrep target.txt seed iters [scale]
   scale k >= 1 multiplies the target by k and d by k (a representation of k*h is also entropic).
   Prints the loss and, at loss 0, the matrices as hex. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef unsigned __int128 u128;
static int m, d, r, s[8], nread[8], rd[8][8], nv, N, *tgt;
static u128 mask[8], W[8][64];
static unsigned long long rng = 88172645463325252ULL;
static unsigned long long xr(void){ rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static int rank_of(int S){
  u128 basis[160]; int nb = 0;
  u128 rows[400]; int nr = 0;
  for (int g = 0; g < m; g++) if (S >> g & 1) for (int i = 0; i < d; i++) rows[nr++] = (u128)1 << (g * d + i);
  for (int j = 0; j < r; j++) if (S >> (m + j) & 1) for (int k = 0; k < s[j]; k++) rows[nr++] = W[j][k];
  for (int t = 0; t < nr; t++){
    u128 v = rows[t];
    for (int b = 0; b < nb; b++){ u128 w = v ^ basis[b]; if (w < v) v = w; }
    if (v){ /* insert keeping basis sorted descending so the min trick is a valid reduction */
      int p = nb++; while (p > 0 && basis[p-1] < v){ basis[p] = basis[p-1]; p--; } basis[p] = v;
      /* re-reduce is not needed for rank counting with descending leading bits */
    }
  }
  return nb;
}
static u128 rnd128(void){ return ((u128)xr() << 64) | xr(); }
int main(int argc, char **argv){
  FILE *f = fopen(argv[1], "r"); unsigned long long seed = atoll(argv[2]); long iters = atol(argv[3]);
  int scale = argc > 4 ? atoi(argv[4]) : 1;
  rng ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
  if (fscanf(f, "%d %d %d", &m, &d, &r) != 3) return 2;
  for (int j = 0; j < r; j++){ if (fscanf(f, "%d %d", &s[j], &nread[j]) != 2) return 2; for (int i = 0; i < nread[j]; i++) if (fscanf(f, "%d", &rd[j][i]) != 1) return 2; }
  nv = m + r; N = 1 << nv; tgt = malloc(sizeof(int) * N);
  for (int S = 0; S < N; S++){ if (fscanf(f, "%d", &tgt[S]) != 1) return 2; tgt[S] *= scale; }
  d *= scale; for (int j = 0; j < r; j++) s[j] *= scale;
  if (m * d > 128){ fprintf(stderr, "too many bits\n"); return 3; }
  for (int j = 0; j < r; j++){ mask[j] = 0; for (int i = 0; i < nread[j]; i++) for (int b = 0; b < d; b++) mask[j] |= (u128)1 << (rd[j][i] * d + b);
    for (int k = 0; k < s[j]; k++) W[j][k] = rnd128() & mask[j]; }
  int *cur = malloc(sizeof(int) * N); long loss = 0;
  for (int S = 1; S < N; S++){ cur[S] = rank_of(S); loss += labs((long)cur[S] - tgt[S]); }
  long best = loss;
  int *tmp = malloc(sizeof(int) * N);
  for (long it = 0; it < iters && loss > 0; it++){
    int j = xr() % r, k = xr() % s[j];
    int bi = xr() % nread[j], b = rd[j][bi] * d + (int)(xr() % d);
    W[j][k] ^= (u128)1 << b;
    long nl = loss;
    for (int S = 1; S < N; S++) if (S >> (m + j) & 1){ tmp[S] = rank_of(S); nl += labs((long)tmp[S] - tgt[S]) - labs((long)cur[S] - tgt[S]); }
    double T = 1.5 * (1.0 - (double)it / iters) + 0.05;
    if (nl <= loss || (double)(xr() % 1000000) / 1e6 < exp((loss - nl) / T)){
      loss = nl; for (int S = 1; S < N; S++) if (S >> (m + j) & 1) cur[S] = tmp[S];
      if (loss < best){ best = loss; }
    } else W[j][k] ^= (u128)1 << b;
  }
  printf("final loss %ld best %ld\n", loss, best);
  if (loss == 0){
    for (int j = 0; j < r; j++){ printf("y%d:", j); for (int k = 0; k < s[j]; k++) printf(" %016llx%016llx", (unsigned long long)(W[j][k] >> 64), (unsigned long long)W[j][k]); printf("\n"); }
  }
  return loss == 0 ? 0 : 1;
}
