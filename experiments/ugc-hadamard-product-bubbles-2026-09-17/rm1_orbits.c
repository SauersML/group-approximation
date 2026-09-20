/* Orbit representatives of cosets of RM(1,n) in F_2^(2^n) under AGL(n,2).
 * Coset canonical form: the unique member vanishing on {0, e_1, ..., e_n}.
 * Usage: rm1_orbits n   (2 <= n <= 5).  Prints "rep_hex orbit_size" per
 * orbit; exits 1 unless orbit sizes sum to 2^(2^n - n - 1). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int n, N, nfree, freepos[32];
static uint32_t canon(uint32_t f) {
    uint32_t g = f;
    if (g & 1u) g ^= (N == 32 ? 0xffffffffu : ((1u << N) - 1));
    for (int l = 0; l < n; l++)
        if ((g >> (1u << l)) & 1u)
            for (int z = 0; z < N; z++) if ((z >> l) & 1) g ^= 1u << z;
    return g;
}
static uint32_t apply(uint32_t f, const int *perm) { /* g(z) = f(perm[z]) */
    uint32_t g = 0;
    for (int z = 0; z < N; z++) if ((f >> perm[z]) & 1u) g |= 1u << z;
    return g;
}
static uint64_t idx_of(uint32_t f) {
    uint64_t i = 0;
    for (int q = 0; q < nfree; q++) if ((f >> freepos[q]) & 1u) i |= 1ULL << q;
    return i;
}
int main(int argc, char **argv) {
    if (argc < 2) return 2;
    n = atoi(argv[1]); N = 1 << n;
    int gen[3][32];
    for (int z = 0; z < N; z++) {
        gen[0][z] = z ^ 1;                                   /* translation by e_1 */
        gen[1][z] = ((z << 1) | (z >> (n - 1))) & (N - 1);   /* cyclic coordinate shift */
        gen[2][z] = z ^ ((z >> 1) & 1);                      /* transvection z_0 += z_1 */
    }
    nfree = 0;
    for (int z = 1; z < N; z++) if (z & (z - 1)) freepos[nfree++] = z;
    uint64_t ncl = 1ULL << nfree;
    uint8_t *vis = calloc(ncl / 8 + 1, 1);
    uint32_t *stack = malloc(sizeof(uint32_t) * ncl);
    uint64_t covered = 0; int norb = 0;
    for (uint64_t idx = 0; idx < ncl; idx++) {
        if (vis[idx >> 3] & (1 << (idx & 7))) continue;
        uint32_t rep = 0;
        for (int q = 0; q < nfree; q++) if ((idx >> q) & 1) rep |= 1u << freepos[q];
        uint64_t sp = 0, sz = 0;
        vis[idx >> 3] |= 1 << (idx & 7); stack[sp++] = rep;
        while (sp) {
            uint32_t f = stack[--sp]; sz++;
            for (int g = 0; g < 3; g++) {
                uint32_t h = canon(apply(f, gen[g]));
                uint64_t hi = idx_of(h);
                if (!(vis[hi >> 3] & (1 << (hi & 7)))) { vis[hi >> 3] |= 1 << (hi & 7); stack[sp++] = h; }
            }
        }
        printf("%08x %llu\n", rep, (unsigned long long)sz);
        covered += sz; norb++;
    }
    fprintf(stderr, "n=%d orbits=%d covered=%llu of %llu\n", n, norb,
            (unsigned long long)covered, (unsigned long long)ncl);
    return covered == ncl ? 0 : 1;
}
