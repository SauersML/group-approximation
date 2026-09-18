/* Column generator for the one-bit linear-atom LP (same model as atom_lp.py, codeword subspaces of dimension <= 1).
   usage: atom_gen target.txt out.bin
   An atom picks, for each codeword j, either the zero space or one nonzero vector of F_2^(reads of j).
   Writes int8 records, one per atom: [phi_a, h_a(S) - h_a(rep(S)) for each S with S != rep(S)],
   preceded by an int32 header (natoms, ncols). Atoms are enumerated in mixed radix (2^nread_j per codeword j,
   0 meaning the zero space, v meaning sum_i bit_i(v) e_(reads[j][i])). */
#include <stdio.h>
#include <stdlib.h>
static int m, r, nread[12], rd[12][16], N, *col, *rep, my0, mx1yF, myF;
static int rank_small(unsigned *v, int n){
  int np = 0; unsigned piv[16];
  for (int i = 0; i < n; i++){ unsigned x = v[i];
    for (int b = 0; b < np; b++){ unsigned w = x ^ piv[b]; if (w < x) x = w; }
    if (x){ int p = np++; while (p > 0 && piv[p-1] < x){ piv[p] = piv[p-1]; p--; } piv[p] = x; } }
  return np;
}
int main(int argc, char **argv){
  FILE *f = fopen(argv[1], "r");
  if (fscanf(f, "%d %d", &m, &r) != 2) return 2;
  for (int j = 0; j < r; j++){ if (fscanf(f, "%d", &nread[j]) != 1) return 2; for (int i = 0; i < nread[j]; i++) if (fscanf(f, "%d", &rd[j][i]) != 1) return 2; }
  N = 1 << (m + r); col = malloc(sizeof(int) * N); rep = malloc(sizeof(int) * N);
  for (int S = 0; S < N; S++) if (fscanf(f, "%d", &col[S]) != 1) return 2;
  if (fscanf(f, "%d %d %d", &my0, &mx1yF, &myF) != 3) return 2;
  int nc = 0; for (int S = 0; S < N; S++) if (col[S] + 1 > nc) nc = col[S] + 1;
  int *first = malloc(sizeof(int) * nc); for (int c = 0; c < nc; c++) first[c] = -1;
  int npairs = 0;
  for (int S = 0; S < N; S++){ if (first[col[S]] < 0) first[col[S]] = S; rep[S] = first[col[S]]; if (rep[S] != S) npairs++; }
  long natoms = 1; for (int j = 0; j < r; j++) natoms <<= nread[j];
  FILE *o = fopen(argv[2], "wb"); int hdr[2] = { (int)natoms, npairs + 1 }; fwrite(hdr, sizeof(int), 2, o);
  signed char *rec = malloc(npairs + 1); int *h = malloc(sizeof(int) * N);
  for (long a = 0; a < natoms; a++){
    unsigned code[12]; long t = a;
    for (int j = 0; j < r; j++){ int loc = t & ((1 << nread[j]) - 1); t >>= nread[j]; unsigned v = 0;
      for (int i = 0; i < nread[j]; i++) if (loc >> i & 1) v |= 1u << rd[j][i]; code[j] = v; }
    for (int S = 0; S < N; S++){
      unsigned keep = 0; int nx = 0; for (int g = 0; g < m; g++){ if (S >> g & 1) nx++; else keep |= 1u << g; }
      unsigned v[12]; int n = 0; for (int j = 0; j < r; j++) if (S >> (m + j) & 1) v[n++] = code[j] & keep;
      h[S] = nx + rank_small(v, n);
    }
    int k = 0; rec[k++] = (signed char)(h[my0] + h[mx1yF] - h[myF]);
    for (int S = 0; S < N; S++) if (rep[S] != S) rec[k++] = (signed char)(h[S] - h[rep[S]]);
    fwrite(rec, 1, npairs + 1, o);
  }
  fclose(o); printf("atoms %ld rows %d\n", natoms, npairs); return 0;
}
