/*
 * Exact Monte Carlo sampler for the open cluster of 0 in Bernoulli(p) bond
 * percolation on the range-k fibre graph Cay(Z, {+-1, ..., +-k}), restricted
 * to the window [-W, W].
 *
 * Purpose (see ../../research/fpbs-pointwise-critical-bound-fails-on-spread-products.md):
 * the fibre is a subgraph of X_k = Cay(F_2 x Z, {a^+-1, b^+-1, t^+-1..t^+-k}),
 * the window is a further subgraph, and p = 1/(2k+3) = 1/(d-1) <= p_c(X_k).
 * Monotonicity therefore gives, for every m in the window,
 *
 *     tau^{X_k}_{p_c}(o, t^m)  >=  P_p( 0 <-> m inside the window ).
 *
 * The sampler explores the cluster of 0 by breadth-first search.  Edges are
 * revealed lazily: when vertex u is processed, every edge {u, u+-j} is given a
 * fresh Bernoulli(p) value, and the value is used only if the other endpoint is
 * not yet in the cluster.  An edge whose other endpoint is outside the cluster
 * when u is processed is revealed exactly once (the other endpoint, if it joins
 * later, finds u already in the cluster), so the cluster law is exact.  Open
 * edges among the 2k candidates are located by geometric skipping.
 *
 * Output: for each word-length shell n (|t^m| = ceil(|m|/k)), the counts of
 * samples in which the cluster contains m = +k n and m = -k n, and the total
 * number of cluster vertices in the shell.
 *
 * Usage: fibre_cluster k nmax samples seed
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t s[4];
static inline uint64_t rotl(const uint64_t x, int r) { return (x << r) | (x >> (64 - r)); }
static uint64_t next64(void) {
  const uint64_t result = rotl(s[1] * 5, 7) * 9;
  const uint64_t t = s[1] << 17;
  s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3];
  s[2] ^= t; s[3] = rotl(s[3], 45);
  return result;
}
static inline double unif(void) { return ((next64() >> 11) + 0.5) * 0x1.0p-53; }
static void seed_rng(uint64_t seed) {
  for (int i = 0; i < 4; i++) {
    seed += 0x9E3779B97F4A7C15ULL;
    uint64_t z = seed;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    s[i] = z ^ (z >> 31);
  }
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: %s k nmax samples seed\n", argv[0]); return 1; }
  const long k = atol(argv[1]);
  const long nmax = atol(argv[2]);
  const long samples = atol(argv[3]);
  seed_rng(strtoull(argv[4], NULL, 10));
  const double p = 1.0 / (2.0 * k + 3.0);
  const double logq = log1p(-p);
  const long W = k * (nmax + 20); /* window half-width */
  const long L = 2 * W + 1;
  long *stamp = calloc(L, sizeof(long));
  long *queue = malloc(L * sizeof(long));
  long *hit_plus = calloc(nmax + 1, sizeof(long));
  long *hit_minus = calloc(nmax + 1, sizeof(long));
  double *shell_mass = calloc(nmax + 2, sizeof(double));
  double total_size = 0;
  for (long it = 1; it <= samples; it++) {
    long head = 0, tail = 0;
    stamp[W] = it;
    queue[tail++] = 0;
    while (head < tail) {
      long u = queue[head++];
      /* candidates indexed 0..2k-1: c < k -> u+(c+1), else u-(c-k+1) */
      long c = -1;
      for (;;) {
        double g = floor(log(unif()) / logq); /* closed trials before next open */
        c += (long)g + 1;
        if (c >= 2 * k) break;
        long v = (c < k) ? u + (c + 1) : u - (c - k + 1);
        if (v < -W || v > W) continue;
        if (stamp[v + W] == it) continue;
        stamp[v + W] = it;
        queue[tail++] = v;
      }
    }
    total_size += tail;
    for (long i = 0; i < tail; i++) {
      long m = queue[i];
      long am = m < 0 ? -m : m;
      long n = (am + k - 1) / k;
      if (n <= nmax) shell_mass[n] += 1.0;
      if (am % k == 0 && n <= nmax && n >= 1) {
        if (m > 0) hit_plus[n]++; else hit_minus[n]++;
      }
    }
  }
  printf("# k=%ld p=%.10f samples=%ld window=%ld mean_cluster=%.4f\n", k, p, samples, W,
         total_size / samples);
  printf("# n hit_plus hit_minus shell_mass_total\n");
  for (long n = 0; n <= nmax; n++)
    printf("%ld %ld %ld %.0f\n", n, hit_plus[n], hit_minus[n], shell_mass[n]);
  return 0;
}
