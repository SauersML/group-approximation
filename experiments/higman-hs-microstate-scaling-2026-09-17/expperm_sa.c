/* Simulated annealing for "exponential permutations" (Helfgott--Juschenko form).
 *
 * Find f in Sym(Z/n) with f^k = id (fixed cycle type: floor(n/k) k-cycles + fixed points)
 * minimizing  B(f) = #{x in Z/n : f(x+1) != m f(x) mod n}.
 *
 * (k,m) = (4,2): existence of f with B(f) <= eps n for all large odd n  <=>  Higman's
 *                group H4 has a nontrivial sofic quotient.
 * (k,m) = (3,2),(2,2): Higman's 3- and 2-cycles are trivial, so B(f)/n must stay
 *                bounded below for large n (calibration: floor).
 * (k,m) = (4,3): Kassabov--Kuperberg--Riley / Glebsky--Szegedy: permutations exist for m>2
 *                (calibration: decay, with a possibly astronomical threshold).
 *
 * Moves: conjugation f <- tau f tau by a transposition tau=(u v) (preserves cycle type).
 *   directed: pick a bad x, put u = f(x+1), v = m f(x)  (or the backward analogue);
 *   random:   u, v uniform.
 * Metropolis acceptance with geometric cooling.  Exact incremental energy.
 *
 * usage: expperm_sa n m k sweeps seed [T0 T1]   (sweeps = moves / n)
 * output: one JSON line.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int64_t n, m, minv, k;
static int64_t *f, *finv;         /* permutation and inverse */
static int64_t *badlist, *badpos; /* set of bad x with O(1) insert/delete */
static int64_t nbad;

static inline int isbad(int64_t x) {
    int64_t x1 = x + 1 == n ? 0 : x + 1;
    return f[x1] != (int64_t)(((__int128)m * f[x]) % n);
}
static inline void setbad(int64_t x, int b) {
    if (b && badpos[x] < 0) { badpos[x] = nbad; badlist[nbad++] = x; }
    else if (!b && badpos[x] >= 0) {
        int64_t p = badpos[x], y = badlist[--nbad];
        badlist[p] = y; badpos[y] = p; badpos[x] = -1;
    }
}
static int64_t modinv(int64_t a, int64_t mod) {
    int64_t t = 0, nt = 1, r = mod, nr = a % mod;
    while (nr) { int64_t q = r / nr, tmp = t - q * nt; t = nt; nt = tmp; tmp = r - q * nr; r = nr; nr = tmp; }
    if (r != 1) return -1;
    return (t % mod + mod) % mod;
}
/* conjugate f by (u v) */
static void conj_swap(int64_t u, int64_t v) {
    int64_t fu = f[u], fv = f[v], iu = finv[u], iv = finv[v];
    /* new f' = tau f tau: f'(x) = tau(f(tau(x))) */
    /* collect affected x: u, v, iu, iv */
    int64_t xs[4] = {u, v, iu, iv}, nv[4];
    for (int i = 0; i < 4; i++) {
        int64_t x = xs[i];
        int64_t tx = x == u ? v : (x == v ? u : x);
        int64_t y = f[tx];
        nv[i] = y == u ? v : (y == v ? u : y);
    }
    (void)fu; (void)fv;
    for (int i = 0; i < 4; i++) f[xs[i]] = nv[i];
    for (int i = 0; i < 4; i++) finv[nv[i]] = xs[i];
}
static int collect(int64_t u, int64_t v, int64_t *S) {
    int64_t A[4] = {u, v, finv[u], finv[v]};
    int c = 0;
    for (int i = 0; i < 4; i++) {
        int64_t c0 = A[i], c1 = A[i] == 0 ? n - 1 : A[i] - 1;
        int64_t cand[2] = {c0, c1};
        for (int j = 0; j < 2; j++) {
            int dup = 0;
            for (int t = 0; t < c; t++) if (S[t] == cand[j]) { dup = 1; break; }
            if (!dup) S[c++] = cand[j];
        }
    }
    return c;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: n m k sweeps seed [T0 T1]\n"); return 1; }
    n = atoll(argv[1]); m = atoll(argv[2]); k = atoll(argv[3]);
    double sweeps = atof(argv[4]); rs = 0x9E3779B97F4A7C15ull ^ (uint64_t)atoll(argv[5]) * 0x2545F4914F6CDD1Dull;
    double T0 = argc > 6 ? atof(argv[6]) : 1.5, T1 = argc > 7 ? atof(argv[7]) : 0.08;
    for (int i = 0; i < 20; i++) rnd();
    minv = modinv(m, n);
    if (minv < 0) { fprintf(stderr, "m not invertible mod n\n"); return 1; }
    f = malloc(n * sizeof *f); finv = malloc(n * sizeof *finv);
    badlist = malloc(n * sizeof *badlist); badpos = malloc(n * sizeof *badpos);
    int64_t *perm = malloc(n * sizeof *perm);
    for (int64_t i = 0; i < n; i++) perm[i] = i;
    for (int64_t i = n - 1; i > 0; i--) { int64_t j = rnd() % (i + 1), t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    int64_t nc = n / k;
    for (int64_t c = 0; c < nc; c++)
        for (int64_t j = 0; j < k; j++) f[perm[c * k + j]] = perm[c * k + (j + 1) % k];
    for (int64_t i = nc * k; i < n; i++) f[perm[i]] = perm[i];
    for (int64_t i = 0; i < n; i++) finv[f[i]] = i;
    nbad = 0;
    for (int64_t i = 0; i < n; i++) badpos[i] = -1;
    for (int64_t i = 0; i < n; i++) setbad(i, isbad(i));
    int64_t best = nbad;
    int64_t *bestf = malloc(n * sizeof *bestf);
    for (int64_t i = 0; i < n; i++) bestf[i] = f[i];
    double moves = sweeps * (double)n;
    double lograte = log(T1 / T0) / moves;
    clock_t t0 = clock();
    int64_t S[8];
    for (double it = 0; it < moves; it += 1) {
        double T = T0 * exp(lograte * it);
        int64_t u, v;
        double r = urand();
        if (nbad > 0 && r < 0.9) {
            int64_t x = badlist[rnd() % nbad];
            int64_t x1 = x + 1 == n ? 0 : x + 1;
            if (rnd() & 1) { u = f[x1]; v = (int64_t)(((__int128)m * f[x]) % n); }
            else { u = f[x]; v = (int64_t)(((__int128)minv * f[x1]) % n); }
        } else { u = rnd() % n; v = rnd() % n; }
        if (u == v) continue;
        int c = collect(u, v, S);
        int before = 0, after = 0;
        for (int i = 0; i < c; i++) before += badpos[S[i]] >= 0;
        conj_swap(u, v);
        /* affected set may differ after swap (finv changed): union of old and new */
        int64_t U[16]; int cu = 0;
        int64_t Snew[8]; int cn = collect(u, v, Snew);
        for (int i = 0; i < c; i++) U[cu++] = S[i];
        for (int i = 0; i < cn; i++) { int dup = 0; for (int t = 0; t < cu; t++) if (U[t] == Snew[i]) { dup = 1; break; } if (!dup) U[cu++] = Snew[i]; }
        /* before-count must also cover the extra indices */
        for (int i = c; i < cu; i++) before += badpos[U[i]] >= 0;
        for (int i = 0; i < cu; i++) after += isbad(U[i]);
        int dE = after - before;
        if (dE <= 0 || urand() < exp(-dE / T)) {
            for (int i = 0; i < cu; i++) setbad(U[i], isbad(U[i]));
            if (nbad < best) { best = nbad; for (int64_t i = 0; i < n; i++) bestf[i] = f[i]; }
        } else {
            conj_swap(u, v); /* tau is an involution: undo */
        }
    }
    /* verify best */
    for (int64_t i = 0; i < n; i++) f[i] = bestf[i];
    int64_t chk = 0, ord = 0;
    for (int64_t i = 0; i < n; i++) chk += isbad(i);
    for (int64_t i = 0; i < n; i++) { int64_t y = i; for (int j = 0; j < k; j++) y = f[y]; ord += (y != i); }
    printf("{\"n\": %lld, \"m\": %lld, \"k\": %lld, \"sweeps\": %g, \"best_bad\": %lld, \"frac\": %.6f, \"verify_bad\": %lld, \"fk_moved\": %lld, \"secs\": %.1f}\n",
           (long long)n, (long long)m, (long long)k, sweeps, (long long)best, (double)best / n, (long long)chk, (long long)ord,
           (double)(clock() - t0) / CLOCKS_PER_SEC);
    if (argc > 8) { FILE *fp = fopen(argv[8], "w"); for (int64_t i = 0; i < n; i++) fprintf(fp, "%lld\n", (long long)bestf[i]); fclose(fp); }
    return 0;
}
