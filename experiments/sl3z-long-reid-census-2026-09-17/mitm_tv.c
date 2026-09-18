/* Directional meet-in-the-middle search for transvections in rho_k(F), F = <x,y>.
 *
 * Fix a primitive direction v in Z^3 and a 2x3 integer matrix B with ker B = Qv.
 * For reduced words a, b of length <= m, B a = B b (as 2x3 matrices) iff a - b = v r^T,
 * iff T = a b^{-1} = I + v (r^T b^{-1}) is a transvection with direction v (det T = 1 forces
 * u.v = 0).  So hashing B*rho_k(a) mod p over the ball of radius m finds every transvection
 * with direction v that factors as a b^{-1} with |a|,|b| <= m, i.e. every such transvection
 * of word length <= 2m (split at the middle).  Candidates are re-checked exactly by verify.py.
 *
 * usage: mitm_tv k m v1 v2 v3
 * Pairs with equal full matrices (relations a = b in rho_k(F)) are separated out as REL.
 * output: "TV k=.. v=(..) a=WORD b=WORD" per collision (up to 50), REL lines (up to 5) and a SUMMARY line.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef unsigned __int128 u128;
static const uint64_t P = 2305843009213693951ULL; /* 2^61 - 1 */

static uint64_t md(u128 x) {
    uint64_t lo = (uint64_t)(x & P), hi = (uint64_t)(x >> 61);
    uint64_t s = lo + hi;
    if (s >= P) s -= P;
    return s;
}
static uint64_t mulm(uint64_t a, uint64_t b) { return md((u128)a * b); }
static uint64_t addm(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }
static uint64_t fromll(long long x) { return x >= 0 ? (uint64_t)x % P : (P - ((uint64_t)(-x) % P)) % P; }

typedef struct { uint64_t m[3][3]; } M3;

static M3 G[4]; /* x, X, y, Y */
static uint64_t Bm[2][3];
static int MAXL;

typedef struct { uint64_t key; uint64_t full; uint64_t code; } Ent;
static Ent *tab;
static size_t ntab, captab;

static void mul3(const M3 *a, const M3 *b, M3 *c) {
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) {
            uint64_t s = 0;
            for (int l = 0; l < 3; l++) s = addm(s, mulm(a->m[i][l], b->m[l][j]));
            c->m[i][j] = s;
        }
}

static uint64_t keyof(const M3 *A) {
    uint64_t h = 0x9E3779B97F4A7C15ULL;
    for (int r = 0; r < 2; r++)
        for (int j = 0; j < 3; j++) {
            uint64_t s = 0;
            for (int l = 0; l < 3; l++) s = addm(s, mulm(Bm[r][l], A->m[l][j]));
            h ^= s + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2);
            h *= 0xff51afd7ed558ccdULL;
        }
    return h;
}

static uint64_t fullof(const M3 *A) {
    uint64_t h = 0x243F6A8885A308D3ULL;
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) {
            h ^= A->m[i][j] + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2);
            h *= 0xc4ceb9fe1a85ec53ULL;
        }
    return h;
}

static void dfs(const M3 *A, int len, int last, uint64_t code) {
    if (len >= 1) {
        if (ntab == captab) {
            captab = captab ? 2 * captab : 1 << 20;
            tab = realloc(tab, captab * sizeof(Ent));
            if (!tab) { fprintf(stderr, "oom\n"); exit(1); }
        }
        tab[ntab].key = keyof(A);
        tab[ntab].full = fullof(A);
        tab[ntab].code = code;
        ntab++;
    }
    if (len == MAXL) return;
    for (int g = 0; g < 4; g++) {
        if (last >= 0 && (g ^ 1) == last) continue;
        M3 C;
        mul3(A, &G[g], &C);
        dfs(&C, len + 1, g, (code << 2) | (uint64_t)g);
    }
}

static int cmpent(const void *a, const void *b) {
    const Ent *x = a, *y = b;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    if (x->full != y->full) return x->full < y->full ? -1 : 1;
    return x->code < y->code ? -1 : (x->code > y->code);
}

static void decode(uint64_t code, char *out) {
    char tmp[64];
    int n = 0;
    const char *L = "xXyY";
    while (code > 1) { tmp[n++] = L[code & 3]; code >>= 2; }
    for (int i = 0; i < n; i++) out[i] = tmp[n - 1 - i];
    out[n] = 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: mitm_tv k m v1 v2 v3\n"); return 1; }
    long long k = atoll(argv[1]);
    MAXL = atoi(argv[2]);
    long long v[3] = {atoll(argv[3]), atoll(argv[4]), atoll(argv[5])};
    long long X[3][3] = {{1, -2, 3}, {0, k, -1 - 2 * k}, {0, 1, -2}};
    long long Y[3][3] = {{-2 - k, -1, 1}, {-2 - k, -2, 3}, {-1, -1, 2}};
    /* inverses = adjugates (det 1) */
    long long Xi[3][3], Yi[3][3];
    for (int t = 0; t < 2; t++) {
        long long (*A)[3] = t ? Y : X;
        long long (*Ai)[3] = t ? Yi : Xi;
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < 3; j++) {
                int i1 = (j + 1) % 3, i2 = (j + 2) % 3, j1 = (i + 1) % 3, j2 = (i + 2) % 3;
                Ai[i][j] = A[i1][j1] * A[i2][j2] - A[i1][j2] * A[i2][j1];
            }
    }
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) {
            G[0].m[i][j] = fromll(X[i][j]);
            G[1].m[i][j] = fromll(Xi[i][j]);
            G[2].m[i][j] = fromll(Y[i][j]);
            G[3].m[i][j] = fromll(Yi[i][j]);
        }
    /* sanity: X*Xi = I */
    M3 c;
    mul3(&G[0], &G[1], &c);
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            if (c.m[i][j] != (uint64_t)(i == j)) { fprintf(stderr, "inverse error\n"); return 1; }
    /* B: rows = two independent vectors among e_i x v */
    long long rows[3][3];
    for (int i = 0; i < 3; i++) {
        long long e[3] = {0, 0, 0};
        e[i] = 1;
        rows[i][0] = e[1] * v[2] - e[2] * v[1];
        rows[i][1] = e[2] * v[0] - e[0] * v[2];
        rows[i][2] = e[0] * v[1] - e[1] * v[0];
    }
    /* (e_i x v) x (e_j x v) = ((e_i x e_j) . v) v = v_l v with l the third index: pick i<j with v_l != 0 */
    int pi = -1, pj = -1;
    for (int l = 2; l >= 0; l--)
        if (v[l] != 0) { pi = (l + 1) % 3; pj = (l + 2) % 3; break; }
    if (pi < 0) { fprintf(stderr, "v = 0\n"); return 1; }
    for (int j = 0; j < 3; j++) { Bm[0][j] = fromll(rows[pi][j]); Bm[1][j] = fromll(rows[pj][j]); }
    {
        uint64_t c0 = addm(mulm(Bm[0][1], Bm[1][2]), P - mulm(Bm[0][2], Bm[1][1]));
        uint64_t c1 = addm(mulm(Bm[0][2], Bm[1][0]), P - mulm(Bm[0][0], Bm[1][2]));
        uint64_t c2 = addm(mulm(Bm[0][0], Bm[1][1]), P - mulm(Bm[0][1], Bm[1][0]));
        if (!c0 && !c1 && !c2) { fprintf(stderr, "B rank < 2\n"); return 1; }
    }
    M3 I;
    memset(&I, 0, sizeof I);
    for (int i = 0; i < 3; i++) I.m[i][i] = 1;
    dfs(&I, 0, -1, 1);
    qsort(tab, ntab, sizeof(Ent), cmpent);
    long hits = 0, rels = 0;
    int minlen = 1000, minrel = 1000;
    char a[64], b[64];
    /* identity class: words a with B a = B I; transvections unless a = I (a relation) */
    uint64_t kI = keyof(&I), fI = fullof(&I);
    for (size_t i = 0; i < ntab; i++)
        if (tab[i].key == kI) {
            decode(tab[i].code, a);
            if (tab[i].full == fI) {
                if (rels < 5) printf("REL k=%lld a=%s b=\n", k, a);
                rels++;
                if ((int)strlen(a) < minrel) minrel = strlen(a);
                continue;
            }
            if (hits < 50) printf("TV k=%lld v=(%lld,%lld,%lld) a=%s b=\n", k, v[0], v[1], v[2], a);
            hits++;
            if ((int)strlen(a) < minlen) minlen = strlen(a);
        }
    for (size_t i = 0; i + 1 < ntab; i++) {
        if (tab[i].key != tab[i + 1].key) continue;
        if (tab[i].key == kI) continue;
        decode(tab[i].code, a);
        decode(tab[i + 1].code, b);
        int la = strlen(a), lb = strlen(b);
        /* a b^-1 reduced length */
        int c0 = 0;
        while (c0 < la && c0 < lb && a[la - 1 - c0] == b[lb - 1 - c0]) c0++;
        int L = la + lb - 2 * c0;
        if (L == 0) continue;
        if (tab[i].full == tab[i + 1].full) {
            if (rels < 5) printf("REL k=%lld a=%s b=%s\n", k, a, b);
            rels++;
            if (L < minrel) minrel = L;
            continue;
        }
        if (hits < 50) printf("TV k=%lld v=(%lld,%lld,%lld) a=%s b=%s\n", k, v[0], v[1], v[2], a, b);
        hits++;
        if (L < minlen) minlen = L;
    }
    printf("SUMMARY k=%lld m=%d v=(%lld,%lld,%lld) words=%zu collisions=%ld minlen=%d relation_pairs=%ld minrel=%d\n", k,
           MAXL, v[0], v[1], v[2], ntab, hits, minlen, rels, minrel);
    return 0;
}
