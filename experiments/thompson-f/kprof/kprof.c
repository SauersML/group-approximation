/* kprof.c: exact F_2 kernel dimension k_D(a,b) = dim{(u,v) in V x V : a u = b v},
   V = F_2[M_(k,N)], N = k + noff, for Guba's Problem sets over the positive monoid M of
   Thompson's group F (normal forms x_{i_1}...x_{i_d}, i_1 <= ... <= i_d; x_j x_i = x_i x_{j+1}, i<j).

   Left multiplication by x_p on a normal form m: q = p, j = 0; while j < d and m[j] < q: q++, j++;
   insert q at position j.  A degree-2 monomial s = x_i x_j acts as x_i (x_j m).

   Mode "free": free monoid (concatenation, no rewriting), used as a non-Ore control.

   The matrix [A | B] has columns a.u, b.v (u, v in V) over rows = normal forms of degree k+2.
   rank is computed by (1) singleton-row peeling, valid since a row with one nonzero entry at column c
   gives rank(M) = 1 + rank(M minus row and column c), then (2) sparse incremental F_2 elimination on
   the remaining core (pivot = largest row index, sorted-merge XOR).
   kernel = 2|V| - rank.

   Usage: kprof SET k noff mode a b [a b ...]
     SET in {X2, S24, S35}; mode in {ore, free}; a, b are bitmasks over SET in the order of
     ore_linalg.py SETS.
   Output: one JSON line per pair.
*/
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
typedef struct { int d; uint8_t w[MAXD]; } mono;

static int FREE_MODE = 0;

static void left_mul_letter(const mono *m, int p, mono *out) {
    if (FREE_MODE) {
        out->d = m->d + 1; out->w[0] = (uint8_t)p;
        for (int t = 0; t < m->d; t++) out->w[t + 1] = m->w[t];
        return;
    }
    int q = p, j = 0;
    while (j < m->d && m->w[j] < q) { q++; j++; }
    out->d = m->d + 1;
    for (int t = 0; t < j; t++) out->w[t] = m->w[t];
    out->w[j] = (uint8_t)q;
    for (int t = j; t < m->d; t++) out->w[t + 1] = m->w[t];
}

static uint64_t key_of(const mono *m) {
    uint64_t k = (uint64_t)m->d;
    for (int t = 0; t < m->d; t++) k = (k << 5) | (uint64_t)(m->w[t] & 31);
    return k;
}

/* open-addressing hash: key -> row id */
static uint64_t *HK; static int32_t *HV; static uint64_t HCAP; static int32_t NROWS = 0;
static int32_t row_id(uint64_t k) {
    uint64_t h = (k * 0x9E3779B97F4A7C15ULL) & (HCAP - 1);
    while (HV[h] >= 0) { if (HK[h] == k) return HV[h]; h = (h + 1) & (HCAP - 1); }
    HK[h] = k; HV[h] = NROWS; return NROWS++;
}

static int SET_N; static int SET_W[16][2];
static void set_load(const char *name) {
    /* monomials as (i, j) with i <= j, order of ore_linalg.py SETS */
    if (!strcmp(name, "X2")) { SET_N = 3; int w[3][2] = {{0,-1},{1,-1},{2,-1}}; memcpy(SET_W, w, sizeof w); }
    else if (!strcmp(name, "S24")) { SET_N = 5; int w[5][2] = {{0,0},{0,1},{0,2},{1,1},{1,2}}; memcpy(SET_W, w, sizeof w); }
    else if (!strcmp(name, "S35")) { SET_N = 9; int w[9][2] = {{0,0},{0,1},{0,2},{0,3},{1,1},{1,2},{1,3},{2,2},{2,3}}; memcpy(SET_W, w, sizeof w); }
    else { fprintf(stderr, "unknown set\n"); exit(2); }
}
static void mul_set(int si, const mono *u, mono *out) {
    mono t;
    if (SET_W[si][1] < 0) { left_mul_letter(u, SET_W[si][0], out); return; }
    left_mul_letter(u, SET_W[si][1], &t);   /* x_i x_j u = x_i (x_j u) */
    left_mul_letter(&t, SET_W[si][0], out);
}

/* sparse vector helpers */
typedef struct { int32_t n, cap; int32_t *v; } svec;
static void sv_push(svec *s, int32_t x) { if (s->n == s->cap) { s->cap = s->cap ? 2 * s->cap : 8; s->v = realloc(s->v, s->cap * sizeof(int32_t)); } s->v[s->n++] = x; }
static int cmp32(const void *a, const void *b) { int32_t x = *(const int32_t *)a, y = *(const int32_t *)b; return (x > y) - (x < y); }
/* out = a XOR b, both sorted ascending */
static void sv_xor(const svec *a, const svec *b, svec *out) {
    out->n = 0; int i = 0, j = 0;
    while (i < a->n || j < b->n) {
        if (j >= b->n || (i < a->n && a->v[i] < b->v[j])) sv_push(out, a->v[i++]);
        else if (i >= a->n || b->v[j] < a->v[i]) sv_push(out, b->v[j++]);
        else { i++; j++; }
    }
}

int main(int argc, char **argv) {
    /* pairs from argv, or from stdin ("a b" per line) when argv[5] is "-" */
    int from_stdin = (argc == 6 && !strcmp(argv[5], "-"));
    if (!from_stdin && (argc < 7 || (argc - 5) % 2)) { fprintf(stderr, "usage: kprof SET k noff mode (a b [a b ...] | -)\n"); return 2; }
    long npairs = 0, cappairs = 16; long *PA = malloc(cappairs * sizeof(long)), *PB = malloc(cappairs * sizeof(long));
    if (from_stdin) {
        long x, y;
        while (scanf("%ld %ld", &x, &y) == 2) {
            if (npairs == cappairs) { cappairs *= 2; PA = realloc(PA, cappairs * sizeof(long)); PB = realloc(PB, cappairs * sizeof(long)); }
            PA[npairs] = x; PB[npairs] = y; npairs++;
        }
    } else {
        for (int ai = 5; ai + 1 < argc; ai += 2) {
            if (npairs == cappairs) { cappairs *= 2; PA = realloc(PA, cappairs * sizeof(long)); PB = realloc(PB, cappairs * sizeof(long)); }
            PA[npairs] = atol(argv[ai]); PB[npairs] = atol(argv[ai + 1]); npairs++;
        }
    }
    set_load(argv[1]);
    int k = atoi(argv[2]), noff = atoi(argv[3]);
    FREE_MODE = !strcmp(argv[4], "free");
    int N = k + noff;
    if (k + 2 > MAXD || N + 2 > 31) { fprintf(stderr, "too large\n"); return 2; }
    /* enumerate V = nondecreasing sequences of length k over 0..N */
    int64_t nV = 0, capV = 1024; mono *V = malloc(capV * sizeof(mono));
    {
        int w[MAXD]; for (int t = 0; t < k; t++) w[t] = 0;
        for (;;) {
            if (nV == capV) { capV *= 2; V = realloc(V, capV * sizeof(mono)); }
            V[nV].d = k; for (int t = 0; t < k; t++) V[nV].w[t] = (uint8_t)w[t]; nV++;
            if (k == 0) break;
            int t = k - 1; while (t >= 0 && w[t] == N) t--;
            if (t < 0) break;
            w[t]++; for (int s = t + 1; s < k; s++) w[s] = w[t];
        }
        if (FREE_MODE) { /* free monoid: all words of length k over 0..N */
            int64_t tot = 1; for (int t = 0; t < k; t++) tot *= (N + 1);
            free(V); V = malloc(tot * sizeof(mono)); nV = 0;
            int ww[MAXD]; for (int t = 0; t < k; t++) ww[t] = 0;
            for (int64_t c = 0; c < tot; c++) {
                int64_t x = c; V[nV].d = k;
                for (int t = k - 1; t >= 0; t--) { V[nV].w[t] = (uint8_t)(x % (N + 1)); x /= (N + 1); }
                nV++;
            }
            (void)ww;
        }
    }
    /* images: img[si][u] = row id of s_si . u */
    HCAP = 1; while (HCAP < (uint64_t)(nV * SET_N * 2 + 16)) HCAP <<= 1;
    HK = malloc(HCAP * sizeof(uint64_t)); HV = malloc(HCAP * sizeof(int32_t));
    int32_t **img = malloc(SET_N * sizeof(int32_t *));
    for (int si = 0; si < SET_N; si++) {
        img[si] = malloc(nV * sizeof(int32_t));
    }
    for (uint64_t h = 0; h < HCAP; h++) HV[h] = -1;
    for (int si = 0; si < SET_N; si++) for (int64_t u = 0; u < nV; u++) { mono o; mul_set(si, &V[u], &o); img[si][u] = row_id(key_of(&o)); }
    int32_t nrows = NROWS;
    for (long pi = 0; pi < npairs; pi++) {
        long a = PA[pi], b = PB[pi];
        clock_t t0 = clock();
        int64_t ncol = 2 * nV;
        /* column entries */
        int32_t *cw = calloc(ncol, sizeof(int32_t)); int64_t *cst = malloc((ncol + 1) * sizeof(int64_t));
        int wa = __builtin_popcountl(a), wb = __builtin_popcountl(b);
        cst[0] = 0;
        for (int64_t c = 0; c < ncol; c++) cst[c + 1] = cst[c] + (c < nV ? wa : wb);
        int32_t *cent = malloc(cst[ncol] * sizeof(int32_t));
        for (int64_t c = 0; c < ncol; c++) {
            long m = c < nV ? a : b; int64_t u = c < nV ? c : c - nV; int64_t p = cst[c];
            for (int si = 0; si < SET_N; si++) if (m >> si & 1) cent[p++] = img[si][u];
            cw[c] = (int32_t)(p - cst[c]);
        }
        /* row incidence CSR */
        int32_t *rw = calloc(nrows, sizeof(int32_t));
        for (int64_t e = 0; e < cst[ncol]; e++) rw[cent[e]]++;
        int64_t *rst = malloc((nrows + 1) * sizeof(int64_t)); rst[0] = 0;
        for (int32_t r = 0; r < nrows; r++) rst[r + 1] = rst[r] + rw[r];
        int64_t *rpos = malloc(nrows * sizeof(int64_t)); for (int32_t r = 0; r < nrows; r++) rpos[r] = rst[r];
        int32_t *rent = malloc(cst[ncol] * sizeof(int32_t));
        for (int64_t c = 0; c < ncol; c++) for (int64_t e = cst[c]; e < cst[c + 1]; e++) rent[rpos[cent[e]]++] = (int32_t)c;
        /* singleton peeling */
        char *cdead = calloc(ncol, 1), *rdead = calloc(nrows, 1);
        int32_t *queue = malloc(nrows * sizeof(int32_t)); int64_t qh = 0, qt = 0;
        for (int32_t r = 0; r < nrows; r++) if (rw[r] == 1) queue[qt++] = r;
        int64_t rank = 0;
        while (qh < qt) {
            int32_t r = queue[qh++];
            if (rdead[r] || rw[r] != 1) continue;
            int32_t c = -1;
            for (int64_t e = rst[r]; e < rst[r + 1]; e++) if (!cdead[rent[e]]) { c = rent[e]; break; }
            rdead[r] = 1; if (c < 0) continue;
            cdead[c] = 1; rank++;
            for (int64_t e = cst[c]; e < cst[c + 1]; e++) { int32_t r2 = cent[e]; if (!rdead[r2]) { rw[r2]--; if (rw[r2] == 1) queue[qt++] = r2; } }
        }
        int64_t core_cols = 0, core_rows = 0;
        for (int64_t c = 0; c < ncol; c++) if (!cdead[c]) core_cols++;
        for (int32_t r = 0; r < nrows; r++) if (!rdead[r] && rw[r] >= 2) core_rows++;
        double t_peel = (double)(clock() - t0) / CLOCKS_PER_SEC;
        /* sparse elimination on the core: pivot table indexed by row id */
        svec *piv = calloc(nrows, sizeof(svec)); char *haspiv = calloc(nrows, 1);
        svec cur = {0}, tmp = {0};
        int64_t core_rank = 0, max_fill = 0;
        for (int64_t c = 0; c < ncol; c++) {
            if (cdead[c]) continue;
            cur.n = 0;
            for (int64_t e = cst[c]; e < cst[c + 1]; e++) if (!rdead[cent[e]]) sv_push(&cur, cent[e]);
            qsort(cur.v, cur.n, sizeof(int32_t), cmp32);
            while (cur.n > 0) {
                int32_t h = cur.v[cur.n - 1];
                if (!haspiv[h]) break;
                sv_xor(&cur, &piv[h], &tmp);
                svec sw = cur; cur = tmp; tmp = sw;
            }
            if (cur.n > 0) {
                int32_t h = cur.v[cur.n - 1]; haspiv[h] = 1;
                piv[h].n = 0; for (int32_t t = 0; t < cur.n; t++) sv_push(&piv[h], cur.v[t]);
                core_rank++; if (cur.n > max_fill) max_fill = cur.n;
            }
        }
        rank += core_rank;
        int64_t kernel = ncol - rank;
        double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
        printf("{\"set\":\"%s\",\"mode\":\"%s\",\"k\":%d,\"N\":%d,\"a\":%ld,\"b\":%ld,\"V\":%lld,\"rows\":%d,"
               "\"rank\":%lld,\"kernel\":%lld,\"core_cols\":%lld,\"core_rows\":%lld,\"max_fill\":%lld,"
               "\"peel_secs\":%.2f,\"secs\":%.2f}\n",
               argv[1], argv[4], k, N, a, b, (long long)nV, nrows, (long long)rank, (long long)kernel,
               (long long)core_cols, (long long)core_rows, (long long)max_fill, t_peel, secs);
        fflush(stdout);
        for (int32_t r = 0; r < nrows; r++) if (haspiv[r]) free(piv[r].v);
        free(piv); free(haspiv); free(cur.v); free(tmp.v);
        free(cw); free(cst); free(cent); free(rw); free(rst); free(rpos); free(rent); free(cdead); free(rdead); free(queue);
    }
    return 0;
}
