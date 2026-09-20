/* Exact mean distance from a uniform xi in {-1,1}^(2^k) to the signed
 * first-order Reed-Muller code, for k = n+1 with n = 5 (k = 6), by an
 * affine-class split.  Validation mode n = 4 reproduces the k = 5 values
 * already recorded in hadamard-gadget-deletion-ratio-window.
 *
 * Quantity (full primaries P, HHM+15 Def 2.24):
 *   E max_i |W_i|,  W_i = sum_{a in F_2^k} xi_a (-1)^(a.i),
 *   delta_k = 1/2 - E max|W| / 2^(k+1).
 * Punctured primaries P' (a != 0): W'_i = W_i - xi_0,
 *   delta'_k = 1/2 - E max|W'| / (2 (2^k - 1)).
 *
 * Split a = (a', a_k), i = (i', i_k), a', i' in F_2^n.  With
 *   A_{i'} = sum_{a'} xi_{(a',0)} (-1)^(a'.i')     (a' != 0 only for P')
 *   B_{i'} = sum_{a'} xi_{(a',1)} (-1)^(a'.i')
 * we have W_{(i',i_k)} = A_{i'} + (-1)^(i_k) B_{i'}, so
 *   max_i |W_i| = max_{i'} ( |A_{i'}| + |B_{i'}| ).                   (1)
 * Let F(f0) = sum_{f1} max_{i'}(|A_{i'}| + |B_{i'}|), f0, f1 the sign
 * patterns (truth tables, bit a' set <=> xi = -1) of the two halves.
 *
 * Invariances of F (each is a bijection on f1 plus a permutation of i',
 * or leaves |A| unchanged):
 *   - f0 -> f0 o M, M in GL(n): apply the same to f1; (A,B) are permuted
 *     by M^{-T} on i'.
 *   - f0 -> f0 + <c,.>: apply the same to f1; (A,B) shift i' -> i'+c.
 *   - f0 -> f0 + 1 (on the positions present): A -> -A.
 *   - (P only) f0 -> f0(. + b): A_{i'} -> (-1)^(b.i') A_{i'}, |A| fixed.
 * So for P, F is constant on AGL(n)-orbits of cosets of RM(1,n); for P',
 * F depends on f0 restricted to a' != 0, modulo linear functions and the
 * constant, and is constant on GL(n)-orbits of these classes.
 *
 * Coset representatives.  P: zero f0 on the information set
 * {0, e_1..e_n} of RM(1,n) by adding the unique affine function; the other
 * 2^n - n - 1 bits index the coset.  P': set bit 0 to 0 (absent), then zero
 * f0 on {e_1..e_n, e_1+e_2} by adding the unique function <c,.> + d (the
 * evaluation map at these n+1 points is invertible on span(linear, 1)); the
 * remaining 2^n - n - 2 bits index the class.
 *
 * Orbits are found by search over a bitmap with generators
 *   (x_1..x_n) -> cyclic shift, x_1 <-> x_2, x_1 += x_2, and (P only) x_1 += 1,
 * which generate GL(n) (resp. AGL(n)).
 *
 * For each orbit rep, F is summed exactly over f1 by a Gray code, updating
 * B by +-2 (-1)^(p.i') when bit p flips, with f1's top bit fixed to 0 and
 * the result doubled (f1 -> complement sends B -> -B).
 *
 * Exactness: all arithmetic is integer (uint64 per job, unsigned __int128
 * totals).  With T = sum_orbits |orbit| F(rep) and D = (#classes) 2^(2^n),
 *   E max|W| = T / D   (each class has the same number 2^(n+1) of f0).
 *
 * Build: gcc -O3 -mavx2 -mbmi2 -pthread -o rm1six rm1_six_exact.c
 * Run:   ./rm1six 4 full ; ./rm1six 4 punct ; ./rm1six 5 full ; ./rm1six 5 punct
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
#include <immintrin.h>

typedef unsigned __int128 u128;

static int n, N, punct;
static uint32_t freemask, fullmask;
static int nfree;
static uint32_t aff_tt[2][32];       /* aff_tt[d][c] = truth table of d + <c,x> */
static int gens[4][32], ngens;

static int parity(unsigned v) { return __builtin_popcount(v) & 1; }

static uint32_t apply_gen(uint32_t f, const int *pi) {
    uint32_t r = 0;
    for (int x = 0; x < N; x++) r |= ((f >> pi[x]) & 1u) << x;
    return r;
}

static uint32_t canon(uint32_t f) {
    f &= fullmask;
    if (!punct) {
        uint32_t c = f & 1u, l = 0;
        for (int j = 0; j < n; j++) l |= (((f >> (1 << j)) & 1u) ^ c) << j;
        return f ^ aff_tt[c][l];
    } else {
        f &= ~1u;
        uint32_t fe[8] = {0};
        for (int j = 0; j < n; j++) fe[j] = (f >> (1 << j)) & 1u;
        uint32_t d = ((f >> 3) & 1u) ^ fe[0] ^ fe[1];
        uint32_t c = 0;
        for (int j = 0; j < n; j++) c |= (fe[j] ^ d) << j;
        return (f ^ aff_tt[d][c]) & ~1u;
    }
}

/* orbit data */
static uint32_t *orep;
static uint64_t *osize;
static int norb;

/* jobs */
#define HIBITS 4
static int LBITS;
static volatile int next_job;
static int njobs;
static uint64_t *jobsum;             /* per (orbit, hi) */
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;

static int8_t chi2[32][32];          /* chi2[p][i] = 2 (-1)^(p.i) */

static void walsh_vec(uint32_t f, int skip0, int *out) {
    for (int i = 0; i < N; i++) {
        int s = 0;
        for (int a = skip0 ? 1 : 0; a < N; a++)
            s += (((f >> a) & 1u) ^ (uint32_t)parity((unsigned)(a & i))) ? -1 : 1;
        out[i] = s;
    }
}

static void *worker(void *arg) {
    (void)arg;
    for (;;) {
        int j;
        pthread_mutex_lock(&mu);
        j = next_job++;
        pthread_mutex_unlock(&mu);
        if (j >= njobs) break;
        int o = j >> HIBITS, hi = j & ((1 << HIBITS) - 1);
        int A[32], B[32];
        walsh_vec(orep[o], punct, A);
        uint32_t f1 = (uint32_t)hi << LBITS;
        walsh_vec(f1, 0, B);
        int8_t ab[32], bb[32];
        memset(ab, 0, 32); memset(bb, 0, 32);
        for (int i = 0; i < N; i++) { ab[i] = (int8_t)(A[i] < 0 ? -A[i] : A[i]); bb[i] = (int8_t)B[i]; }
        __m256i absA = _mm256_loadu_si256((const __m256i *)ab);
        __m256i vb = _mm256_loadu_si256((const __m256i *)bb);
        __m256i dv[32];
        for (int p = 0; p < N; p++) dv[p] = _mm256_loadu_si256((const __m256i *)chi2[p]);
        uint64_t sum = 0;
        uint64_t cnt = 1ULL << LBITS;
        uint32_t st = 0;             /* low-bit state of f1 */
        for (uint64_t g = 0;; g++) {
            __m256i x = _mm256_add_epi8(_mm256_abs_epi8(vb), absA);
            __m128i y = _mm_max_epu8(_mm256_castsi256_si128(x), _mm256_extracti128_si256(x, 1));
            y = _mm_max_epu8(y, _mm_srli_si128(y, 8));
            y = _mm_max_epu8(y, _mm_srli_si128(y, 4));
            y = _mm_max_epu8(y, _mm_srli_si128(y, 2));
            y = _mm_max_epu8(y, _mm_srli_si128(y, 1));
            sum += (uint32_t)(_mm_cvtsi128_si32(y) & 0xff);
            if (g + 1 == cnt) break;
            int p = __builtin_ctzll(g + 1);
            if ((st >> p) & 1u) vb = _mm256_add_epi8(vb, dv[p]);   /* -1 -> +1 */
            else vb = _mm256_sub_epi8(vb, dv[p]);                 /* +1 -> -1 */
            st ^= 1u << p;
        }
        jobsum[j] = sum;
    }
    return NULL;
}

static void print_u128(u128 v) {
    char buf[64]; int k = 0;
    if (v == 0) { printf("0"); return; }
    while (v) { buf[k++] = (char)('0' + (int)(v % 10)); v /= 10; }
    while (k) putchar(buf[--k]);
}

static u128 gcd128(u128 a, u128 b) { while (b) { u128 t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    n = argc > 1 ? atoi(argv[1]) : 4;
    punct = argc > 2 && strcmp(argv[2], "punct") == 0;
    int nthreads = argc > 3 ? atoi(argv[3]) : 4;
    if (n < 3 || n > 5) { fprintf(stderr, "n in 3..5\n"); return 1; }
    N = 1 << n;
    fullmask = N == 32 ? 0xffffffffu : ((1u << N) - 1);
    for (uint32_t d = 0; d < 2; d++)
        for (uint32_t c = 0; c < (uint32_t)N; c++) {
            uint32_t t = 0;
            for (int x = 0; x < N; x++) t |= (d ^ (uint32_t)parity(c & (unsigned)x)) << x;
            aff_tt[d][c] = t;
        }
    freemask = fullmask & ~1u;
    for (int j = 0; j < n; j++) freemask &= ~(1u << (1 << j));
    if (punct) freemask &= ~(1u << 3);
    nfree = __builtin_popcount(freemask);
    /* generators: g(x) = f(pi(x)) */
    ngens = 0;
    for (int x = 0; x < N; x++) {                       /* cyclic shift of variables */
        int y = ((x << 1) | (x >> (n - 1))) & (N - 1);
        gens[ngens][x] = y;
    }
    ngens++;
    for (int x = 0; x < N; x++) {                       /* swap x1, x2 */
        int b0 = x & 1, b1 = (x >> 1) & 1;
        gens[ngens][x] = (x & ~3) | (b0 << 1) | b1;
    }
    ngens++;
    for (int x = 0; x < N; x++) gens[ngens][x] = x ^ ((x >> 1) & 1);   /* x1 += x2 */
    ngens++;
    if (!punct) { for (int x = 0; x < N; x++) gens[ngens][x] = x ^ 1; ngens++; }   /* x1 += 1 */

    /* sanity: canon is idempotent and constant on classes */
    for (int t = 0; t < 1000; t++) {
        uint32_t f = (uint32_t)rand() * 2654435761u ^ (uint32_t)rand();
        f &= fullmask;
        uint32_t r = canon(f);
        if (r & ~freemask) { fprintf(stderr, "canon not reduced\n"); return 1; }
        if (canon(r) != r) { fprintf(stderr, "canon not idempotent\n"); return 1; }
        uint32_t d = (uint32_t)(rand() & 1), c = (uint32_t)(rand() % N);
        if (canon(f ^ aff_tt[d][c]) != r) { fprintf(stderr, "canon not class-invariant\n"); return 1; }
        if (punct && canon(f ^ 1u) != r) { fprintf(stderr, "canon depends on bit 0\n"); return 1; }
    }

    uint64_t nclass = 1ULL << nfree;
    uint8_t *vis = calloc(nclass / 8 + 1, 1);
    uint32_t *stack = malloc(sizeof(uint32_t) * nclass);
    orep = malloc(sizeof(uint32_t) * 4096);
    osize = malloc(sizeof(uint64_t) * 4096);
    norb = 0;
    uint64_t covered = 0;
    for (uint64_t idx = 0; idx < nclass; idx++) {
        if (vis[idx >> 3] & (1 << (idx & 7))) continue;
        uint32_t rep = _pdep_u32((uint32_t)idx, freemask);
        vis[idx >> 3] |= (uint8_t)(1 << (idx & 7));
        uint64_t sp = 0, sz = 0;
        stack[sp++] = rep;
        while (sp) {
            uint32_t r = stack[--sp];
            sz++;
            for (int g = 0; g < ngens; g++) {
                uint32_t h = canon(apply_gen(r, gens[g]));
                uint32_t hi = _pext_u32(h, freemask);
                if (!(vis[hi >> 3] & (1 << (hi & 7)))) { vis[hi >> 3] |= (uint8_t)(1 << (hi & 7)); stack[sp++] = h; }
            }
        }
        if (norb >= 4096) { fprintf(stderr, "too many orbits\n"); return 1; }
        orep[norb] = rep; osize[norb] = sz; norb++;
        covered += sz;
    }
    free(stack); free(vis);
    printf("n=%d (k=%d) %s: %d free bits, %llu classes, %d orbits under %s(%d), covered %llu\n",
           n, n + 1, punct ? "punctured P'" : "full P", nfree, (unsigned long long)nclass, norb,
           punct ? "GL" : "AGL", n, (unsigned long long)covered);
    fflush(stdout);
    if (covered != nclass) { fprintf(stderr, "orbit sizes do not cover\n"); return 1; }

    for (int p = 0; p < 32; p++)
        for (int i = 0; i < 32; i++) chi2[p][i] = (p < N && i < N) ? (int8_t)(parity((unsigned)(p & i)) ? -2 : 2) : 0;
    LBITS = (N - 1) - HIBITS;
    njobs = norb << HIBITS;
    jobsum = calloc((size_t)njobs, sizeof(uint64_t));
    next_job = 0;
    pthread_t th[64];
    for (int t = 0; t < nthreads; t++) pthread_create(&th[t], NULL, worker, NULL);
    for (int t = 0; t < nthreads; t++) pthread_join(th[t], NULL);

    u128 T = 0;
    for (int o = 0; o < norb; o++) {
        u128 F = 0;
        for (int h = 0; h < (1 << HIBITS); h++) F += jobsum[(o << HIBITS) + h];
        F *= 2;                                   /* complement symmetry of f1 */
        T += F * (u128)osize[o];
        double ef = (double)F / (double)(1ULL << (N - 1)) / 2.0;
        printf("  orbit %3d rep %08x size %10llu  sum_f1 max = ", o, orep[o], (unsigned long long)osize[o]);
        print_u128(F);
        printf("  (mean %.6f)\n", ef);
    }
    /* E = T / D, D = nclass * 2^N */
    u128 D = (u128)nclass << N;
    int L = punct ? 2 * N - 1 : 2 * N;           /* code length 2^k or 2^k - 1 */
    printf("T = sum |orbit| F = "); print_u128(T); printf("\nD = "); print_u128(D);
    printf("\nE max|W| = T/D = %.12f\n", (double)T / (double)D);
    /* delta = (L D - T) / (2 L D) */
    u128 num = (u128)L * D - T, den = (u128)2 * L * D;
    u128 gg = gcd128(num, den);
    printf("delta = "); print_u128(num / gg); printf(" / "); print_u128(den / gg);
    printf(" = %.12f\n", (double)num / (double)den);
    int K = 2 * N;
    /* kill iff delta (3 - 4/K) < 1  <=>  num (3K - 4) < den K / ... exact: */
    /* delta < K/(3K-4)  <=>  num (3K-4) < den K */
    u128 lhs = num * (u128)(3 * K - 4), rhs = den * (u128)K;
    printf("bound 1 + delta(3 - 4/K) = %.12f ; threshold K/(3K-4) = %d/%d = %.12f ; delta < threshold: %s\n",
           1.0 + (double)num / (double)den * (3.0 - 4.0 / K), K, 3 * K - 4, (double)K / (3 * K - 4),
           lhs < rhs ? "YES" : "NO");
    return 0;
}
