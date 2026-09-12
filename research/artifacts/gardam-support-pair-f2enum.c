/* Enumerate all (u, v) in F_2^21 x F_2^21 with u*v = 1 on the product table.
   table.txt: "n K eid" then n rows of n product indices (row i = S_i, col j = T_j).
   For each u (2^n, Gray code), row_k(u) = XOR_{i in u} R[k][i], a bitmask over v;
   solve the linear system row_k . v = [k == eid] by elimination, enumerate the
   affine solution set, print "u v" as hex. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#define MAXK 512
static uint32_t R[MAXK][32];
int main(void) {
  FILE *f = fopen("table.txt", "r");
  int n, K, eid;
  if (!f || fscanf(f, "%d %d %d", &n, &K, &eid) != 3 || K > MAXK || n > 24) { fprintf(stderr, "bad table\n"); return 2; }
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) {
      int k;
      if (fscanf(f, "%d", &k) != 1) { fprintf(stderr, "bad row\n"); return 2; }
      R[k][i] ^= (uint32_t)1 << j;
    }
  fclose(f);
  static uint32_t row[MAXK], M[MAXK];
  for (int k = 0; k < K; k++) row[k] = 0;
  uint32_t u = 0;
  long long nsol = 0, nu = 0;
  uint64_t total = (uint64_t)1 << n;
  for (uint64_t c = 0; c < total; c++) {
    if (c) {
      int i = __builtin_ctzll(c);
      u ^= (uint32_t)1 << i;
      for (int k = 0; k < K; k++) row[k] ^= R[k][i];
    }
    /* augmented rows: bit n = rhs */
    int m = 0;
    for (int k = 0; k < K; k++) {
      uint32_t r = row[k] | ((k == eid) ? ((uint32_t)1 << n) : 0);
      if (r) M[m++] = r;
    }
    int rank = 0, piv[32];
    uint32_t low = ((uint32_t)1 << n) - 1;
    for (int col = 0; col < n && rank < m; col++) {
      int sel = -1;
      for (int t = rank; t < m; t++) if (M[t] >> col & 1) { sel = t; break; }
      if (sel < 0) continue;
      uint32_t tmp = M[sel]; M[sel] = M[rank]; M[rank] = tmp;
      for (int t = 0; t < m; t++) if (t != rank && (M[t] >> col & 1)) M[t] ^= M[rank];
      piv[rank++] = col;
    }
    int bad = 0;
    for (int t = rank; t < m; t++) if (M[t]) { bad = 1; break; }
    if (bad) continue;
    nu++;
    /* free columns */
    int isp[32] = {0}, free_[32], nf = 0;
    for (int t = 0; t < rank; t++) isp[piv[t]] = 1;
    for (int col = 0; col < n; col++) if (!isp[col]) free_[nf++] = col;
    if (nf > 20) { fprintf(stderr, "u=%x kernel dim %d too big\n", u, nf); return 3; }
    for (uint64_t fm = 0; fm < ((uint64_t)1 << nf); fm++) {
      uint32_t v = 0;
      for (int t = 0; t < nf; t++) if (fm >> t & 1) v |= (uint32_t)1 << free_[t];
      for (int t = 0; t < rank; t++) {
        uint32_t r = M[t];
        int val = (r >> n) & 1;
        val ^= __builtin_popcount(r & low & v & ~((uint32_t)1 << piv[t])) & 1;
        if (val) v |= (uint32_t)1 << piv[t];
      }
      printf("%x %x\n", u, v);
      nsol++;
    }
  }
  fprintf(stderr, "u with solvable system: %lld, total F_2 points: %lld\n", nu, nsol);
  return 0;
}
