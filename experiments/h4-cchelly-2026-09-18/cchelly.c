/* cchelly.c -- exact Case 1 commutator search for research/h4-case1-helly-is-a-commutator-double-coset-problem.md.
 * (H'') : a != b in F, u, v in N, [u,a] = [v,b] = k != 1  ==>  u^-1 v in C_N(a) C_N(b).
 * For every f in the F-ball (length <= LA in p1..p3) and u in the N-ball (length <= LB in x0..x11), the exact Garside
 * normal form of [u,f] is hashed.  For a commutator value k shared by two F-elements a, b put U_a = {u : [u,a] = k},
 * U_b = {v : [v,b] = k} (all hits re-verified exactly in normal form; collisions are counted and dropped).
 * Then (w13, (K)): w = u is a vertex centre iff u in U_b, w = v iff v in U_a, and any w in U_a cap U_b is a pure centre.
 * VCFAIL = #(u,v) in (U_a \ U_b) x (U_b \ U_a); HBALL = those with U_a cap U_b nonempty; HCAND = the rest.
 * The Garside engine (left-greedy normal forms over Coxeter tables) is copied from
 * experiments/h4-artin-complex-6cycles-2026-09-17/tsearch.c; tables and generators come from dumpch.py.
 * usage: cchelly PRE LA LB all | hash F0 F1 OUT | pair HASHFILES...        build: cc -O2 -o cchelly cchelly.c */
#include <stdio.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXF 200
static int n, N, W0, MX, MY, MZ;
static int *len_, *inv_, *ld_, *rd_, *supp_, *tau_, *lmul_, *rmul_, *wlen_, *words_, *dcache_;
#define LMUL(w, i) lmul_[(w) * n + (i)]
#define RMUL(w, i) rmul_[(w) * n + (i)]
#define WORD(w) (words_ + (w) * 64)

typedef struct { int k; int len; uint16_t P[MAXF]; } elt;

static int wmul(int a, int b) {
    int x = a, *wd = WORD(b), L = wlen_[b];
    for (int j = 0; j < L; j++) x = RMUL(x, wd[j]);
    return x;
}
static int meet(int u, int v) {
    int res = 0;
    for (;;) {
        int c = ld_[u] & ld_[v];
        if (!c) return res;
        int i = __builtin_ctz(c);
        res = RMUL(res, i); u = LMUL(u, i); v = LMUL(v, i);
    }
}
static int parabolic_prefix(int w, int mask) {
    int t = 0;
    for (;;) {
        int c = ld_[w] & mask;
        if (!c) return t;
        int i = __builtin_ctz(c);
        t = RMUL(t, i); w = LMUL(w, i);
    }
}
static int parabolic_w0(int mask) {
    int t = 0;
    for (;;) {
        int c = mask & ~rd_[t];
        if (!c) return t;
        int i = __builtin_ctz(c);
        t = RMUL(t, i);
    }
}
#define CACHEBITS 22
static uint32_t npk[1 << CACHEBITS];
static uint16_t npa[1 << CACHEBITS], npb[1 << CACHEBITS];
static void overflow(void) { fprintf(stderr, "MAXF overflow\n"); exit(2); }

/* append simple y to normal form (k,P) */
static void append(elt *g, int y) {
    if (y == 0) return;
    int L = g->len;
    if (L + 1 >= MAXF) overflow();
    int cur = y;
    uint16_t R[MAXF];
    for (int i = L - 1; i >= 0; i--) {
        int a = g->P[i];
        uint32_t key = (uint32_t)a * (uint32_t)N + (uint32_t)cur;
        uint32_t hsh = (key * 2654435761u) >> (32 - CACHEBITS);
        int a2, b2;
        if (npk[hsh] == key + 1) { a2 = npa[hsh]; b2 = npb[hsh]; }
        else {
            int t = meet(dcache_[a], cur);
            a2 = wmul(a, t);
            b2 = wmul(inv_[t], cur);
            npk[hsh] = key + 1; npa[hsh] = (uint16_t)a2; npb[hsh] = (uint16_t)b2;
        }
        R[i] = (uint16_t)b2;
        cur = a2;
    }
    uint16_t out[MAXF];
    out[0] = (uint16_t)cur;
    for (int i = 0; i < L; i++) out[i + 1] = R[i];
    int m = L + 1, j = 0;
    while (j < m && out[j] == W0) j++;
    g->k += j;
    int e = m;
    while (e > j && out[e - 1] == 0) e--;
    g->len = e - j;
    for (int i = 0; i < g->len; i++) g->P[i] = out[j + i];
}
static void tau_inplace(elt *g, int m) {
    if (m & 1) for (int i = 0; i < g->len; i++) g->P[i] = (uint16_t)tau_[g->P[i]];
}
static void mul(const elt *g, const elt *h, elt *r) {
    elt t = *g;
    tau_inplace(&t, h->k);
    t.k += h->k;
    for (int i = 0; i < h->len; i++) append(&t, h->P[i]);
    *r = t;
}
static void inverse(const elt *g, elt *r) {
    elt res; res.k = 0; res.len = 0;
    for (int i = g->len - 1; i >= 0; i--) {
        elt f; f.k = -1; f.len = 1; f.P[0] = (uint16_t)tau_[dcache_[g->P[i]]];
        if (f.P[0] == 0) f.len = 0;
        elt tmp; mul(&res, &f, &tmp); res = tmp;
    }
    elt d; d.k = -g->k; d.len = 0;
    elt tmp; mul(&res, &d, &tmp);
    *r = tmp;
}

/* ---------------- cchelly: exact commutator Helly search (see header) ---------------- */
typedef struct { int k; int len; uint32_t off; } celt;
static uint16_t *pool; static size_t pool_n = 0, pool_cap = 0;
static celt store(const elt *g) {
    if (pool_n + g->len > pool_cap) { pool_cap = pool_cap ? 2 * pool_cap : (1 << 20); pool = realloc(pool, 2 * pool_cap); }
    celt c; c.k = g->k; c.len = g->len; c.off = (uint32_t)pool_n;
    memcpy(pool + pool_n, g->P, 2 * g->len); pool_n += g->len;
    return c;
}
static void load(const celt *c, elt *g) { g->k = c->k; g->len = c->len; memcpy(g->P, pool + c->off, 2 * c->len); }
static uint64_t ehash(const elt *g) {
    uint64_t h = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)(uint32_t)g->k << 32) ^ (uint64_t)g->len;
    for (int i = 0; i < g->len; i++) { h ^= g->P[i]; h *= 0xff51afd7ed558ccdULL; h ^= h >> 31; }
    h ^= h >> 33; h *= 0xc4ceb9fe1a85ec53ULL; h ^= h >> 29;
    return h;
}
static int eq(const elt *a, const elt *b) {
    return a->k == b->k && a->len == b->len && !memcmp(a->P, b->P, 2 * a->len);
}
#define MAXG 32
static int ng[2]; static char glab[2][MAXG][8]; static elt gel[2][MAXG];
typedef struct { int n; celt *e, *ei; uint8_t (*w)[8]; uint8_t *wl; } ball_t;
static void build_ball(int t, int L, ball_t *B) {
    size_t cap = 1024, cnt = 1;
    B->e = malloc(cap * sizeof(celt)); B->w = malloc(cap * 8); B->wl = malloc(cap);
    elt one; one.k = 0; one.len = 0; B->e[0] = store(&one); B->wl[0] = 0;
    size_t hs = 1 << 24; uint64_t *H = calloc(hs, 8); uint64_t mask = hs - 1;
    #define HINS(h) ({ uint64_t _h = (h) | 1, _i = _h & mask; int _new = 1; \
        while (H[_i]) { if (H[_i] == _h) { _new = 0; break; } _i = (_i + 1) & mask; } if (_new) H[_i] = _h; _new; })
    HINS(ehash(&one));
    size_t f0 = 0, f1 = 1;
    for (int l = 0; l < L; l++) {
        for (size_t i = f0; i < f1; i++) {
            elt g; load(&B->e[i], &g);
            for (int x = 0; x < ng[t]; x++) {
                elt h; mul(&g, &gel[t][x], &h);
                if (!HINS(ehash(&h))) continue;
                if (cnt == cap) { cap *= 2; B->e = realloc(B->e, cap * sizeof(celt)); B->w = realloc(B->w, cap * 8); B->wl = realloc(B->wl, cap); }
                B->e[cnt] = store(&h); memcpy(B->w[cnt], B->w[i], 8); B->wl[cnt] = B->wl[i] + 1; B->w[cnt][B->wl[i]] = (uint8_t)x;
                cnt++;
            }
        }
        f0 = f1; f1 = cnt;
    }
    free(H);
    B->n = (int)cnt; B->ei = malloc(cnt * sizeof(celt));
    for (size_t i = 0; i < cnt; i++) { elt g, gi; load(&B->e[i], &g); inverse(&g, &gi); B->ei[i] = store(&gi); }
}
static void spell(FILE *o, int t, ball_t *B, int i) {
    if (!B->wl[i]) fprintf(o, "1");
    for (int j = 0; j < B->wl[i]; j++) fprintf(o, "%s%s", j ? " " : "", glab[t][B->w[i][j]]);
}
static ball_t FB, NB;
static void comm(int j, int f, elt *r) {       /* r = [u_j, f] = u f u^-1 f^-1 */
    elt u, ui, g, gi, t1, t2;
    load(&NB.e[j], &u); load(&NB.ei[j], &ui); load(&FB.e[f], &g); load(&FB.ei[f], &gi);
    mul(&u, &g, &t1); mul(&t1, &ui, &t2); mul(&t2, &gi, r);
}
static void read_tab(const char *pre) {
    char fn[512]; snprintf(fn, sizeof fn, "%s.tab", pre);
    FILE *f = fopen(fn, "r");
    if (!f || fscanf(f, "%d %d %d %d %d %d", &n, &N, &W0, &MX, &MY, &MZ) != 6) exit(3);
    len_ = malloc(4 * N); inv_ = malloc(4 * N); ld_ = malloc(4 * N); rd_ = malloc(4 * N);
    supp_ = malloc(4 * N); tau_ = malloc(4 * N); dcache_ = malloc(4 * N); wlen_ = malloc(4 * N);
    lmul_ = malloc(4 * N * n); rmul_ = malloc(4 * N * n); words_ = malloc(4 * N * 64);
    for (int w = 0; w < N; w++) {
        if (fscanf(f, "%d %d %d %d %d %d", &len_[w], &inv_[w], &ld_[w], &rd_[w], &supp_[w], &tau_[w]) != 6) exit(3);
        for (int i = 0; i < n; i++) if (fscanf(f, "%d", &LMUL(w, i)) != 1) exit(3);
        for (int i = 0; i < n; i++) if (fscanf(f, "%d", &RMUL(w, i)) != 1) exit(3);
        if (fscanf(f, "%d", &wlen_[w]) != 1) exit(3);
        for (int j = 0; j < wlen_[w]; j++) if (fscanf(f, "%d", &WORD(w)[j]) != 1) exit(3);
    }
    fclose(f);
    for (int w = 0; w < N; w++) dcache_[w] = wmul(inv_[w], W0);
    snprintf(fn, sizeof fn, "%s.gens", pre);
    f = fopen(fn, "r");
    for (int t = 0; t < 2; t++) {
        if (fscanf(f, "%d", &ng[t]) != 1) exit(3);
        for (int i = 0; i < ng[t]; i++) {
            elt *g = &gel[t][i];
            if (fscanf(f, "%7s %d %d", glab[t][i], &g->k, &g->len) != 3) exit(3);
            for (int j = 0; j < g->len; j++) { int x; if (fscanf(f, "%d", &x) != 1) exit(3); g->P[j] = (uint16_t)x; }
        }
    }
    fclose(f);
}
typedef struct __attribute__((packed)) { uint64_t h; uint32_t fj; } ent;
static int entcmp(const void *x, const void *y) {
    const ent *a = x, *b = y;
    if (a->h != b->h) return a->h < b->h ? -1 : 1;
    return a->fj < b->fj ? -1 : a->fj > b->fj;
}
static uint64_t chash(int j, int f) {           /* 0 exactly for the identity */
    elt c; comm(j, f, &c);
    if (c.k == 0 && c.len == 0) return 0;
    uint64_t h = ehash(&c); return h ? h : 1;
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: cchelly PRE LA LB hash F0 F1 OUT | pair FILES... | all\n"); return 1; }
    double t0 = now();
    read_tab(argv[1]);
    int LA = atoi(argv[2]), LB = atoi(argv[3]);
    build_ball(0, LA, &FB); build_ball(1, LB, &NB);
    int maxl = 0; for (int j = 0; j < NB.n; j++) if (NB.e[j].len > maxl) maxl = NB.e[j].len;
    printf("F-ball %d N-ball %d (max NF length %d) %.0f s\n", FB.n, NB.n, maxl, now() - t0); fflush(stdout);
    uint64_t *H = NULL; int nF = FB.n, M = NB.n;
    if (!strcmp(argv[4], "hash")) {
        int F0 = atoi(argv[5]), F1 = atoi(argv[6]); if (F1 > nF) F1 = nF;
        FILE *o = fopen(argv[7], "wb"); int hd[3] = {F0, F1, M}; fwrite(hd, 4, 3, o);
        uint64_t *row = malloc(8 * (size_t)M);
        for (int f = F0; f < F1; f++) {
            for (int j = 0; j < M; j++) row[j] = chash(j, f);
            fwrite(row, 8, M, o); fflush(o);
            printf("hashed f=%d %.0f s\n", f, now() - t0); fflush(stdout);
        }
        fclose(o); return 0;
    }
    H = malloc(8 * (size_t)nF * M);
    for (size_t i = 0; i < (size_t)M; i++) H[i] = 0;          /* f = 0 is the identity */
    if (!strcmp(argv[4], "all")) {
        for (int f = 1; f < nF; f++) for (int j = 0; j < M; j++) H[(size_t)f * M + j] = chash(j, f);
    } else {
        char *have = calloc(nF, 1); have[0] = 1;
        for (int a = 5; a < argc; a++) {
            FILE *in = fopen(argv[a], "rb"); int hd[3];
            if (!in || fread(hd, 4, 3, in) != 3 || hd[2] != M) { fprintf(stderr, "bad %s\n", argv[a]); return 3; }
            for (int f = hd[0]; f < hd[1]; f++) {
                if (fread(H + (size_t)f * M, 8, M, in) != (size_t)M) { fprintf(stderr, "short %s\n", argv[a]); return 3; }
                have[f] = 1;
            }
            fclose(in);
        }
        for (int f = 0; f < nF; f++) if (!have[f]) { fprintf(stderr, "missing f=%d\n", f); return 3; }
    }
    printf("hashes ready %.0f s\n", now() - t0); fflush(stdout);
    size_t ne = 0; ent *E = malloc(sizeof(ent) * (size_t)nF * M);
    for (int f = 1; f < nF; f++) for (int j = 0; j < M; j++) {
        uint64_t h = H[(size_t)f * M + j];
        if (h) { E[ne].h = h; E[ne].fj = (uint32_t)((size_t)f * M + j); ne++; }
    }
    qsort(E, ne, sizeof(ent), entcmp);
    printf("sorted %zu nontrivial commutators %.0f s\n", ne, now() - t0); fflush(stdout);
    long long pairs = (long long)(nF - 1) * (nF - 2) / 2, tuples = 0, vcfail = 0, hball = 0, hcand = 0, coll = 0, classes = 0;
    int nprint = 0;
    char *bad = malloc(1 << 20); int *gs = malloc(sizeof(int) * (1 << 20)), *ge = malloc(sizeof(int) * (1 << 20));
    for (size_t r0 = 0; r0 < ne;) {
        size_t r1 = r0; while (r1 < ne && E[r1].h == E[r0].h) r1++;
        if (E[r1 - 1].fj / M != E[r0].fj / M) {                 /* at least two distinct f share k */
            size_t L = r1 - r0; if (L > (1 << 20)) { fprintf(stderr, "run too long\n"); return 4; }
            elt kref; comm(E[r0].fj % M, E[r0].fj / M, &kref);
            for (size_t i = r0; i < r1; i++) { elt c; comm(E[i].fj % M, E[i].fj / M, &c); bad[i - r0] = !eq(&c, &kref); coll += bad[i - r0]; }
            int ngp = 0;                                         /* groups: maximal runs of one f, bad entries dropped */
            for (size_t i = r0; i < r1;) {
                size_t i1 = i; while (i1 < r1 && E[i1].fj / M == E[i].fj / M) i1++;
                gs[ngp] = (int)(i - r0); ge[ngp] = (int)(i1 - r0); ngp++; i = i1;
            }
            classes++;
            for (int p = 0; p < ngp; p++) for (int q = p + 1; q < ngp; q++) {
                long long na = 0, nb = 0, nab = 0, nax, nbx;
                int ia = gs[p], ib = gs[q];                      /* merge on j */
                for (int i = gs[p]; i < ge[p]; i++) na += !bad[i];
                for (int i = gs[q]; i < ge[q]; i++) nb += !bad[i];
                while (ia < ge[p] && ib < ge[q]) {
                    if (bad[ia]) { ia++; continue; } if (bad[ib]) { ib++; continue; }
                    uint32_t ja = E[r0 + ia].fj % M, jb = E[r0 + ib].fj % M;
                    if (ja == jb) { nab++; ia++; ib++; } else if (ja < jb) ia++; else ib++;
                }
                if (!na || !nb) continue;
                tuples += na * nb; nax = na - nab; nbx = nb - nab;
                if (getenv("CLS") && nprint < atoi(getenv("CLS")) && (na != nab || nb != nab || na > 1)) {
                    int fa = E[r0 + gs[p]].fj / M, fb = E[r0 + gs[q]].fj / M; nprint++;
                    printf("CLASS a="); spell(stdout, 0, &FB, fa); printf(" | b="); spell(stdout, 0, &FB, fb);
                    printf(" | |U_a|=%lld |U_b|=%lld common=%lld | U_a:", na, nb, nab);
                    for (int i = gs[p], c = 0; i < ge[p] && c < 4; i++) if (!bad[i]) { printf(" ["); spell(stdout, 1, &NB, E[r0 + i].fj % M); printf("]"); c++; }
                    printf(" | U_b:");
                    for (int i = gs[q], c = 0; i < ge[q] && c < 4; i++) if (!bad[i]) { printf(" ["); spell(stdout, 1, &NB, E[r0 + i].fj % M); printf("]"); c++; }
                    printf("\n");
                }
                if (nax && nbx) {
                    vcfail += nax * nbx;
                    int fa = E[r0 + gs[p]].fj / M, fb = E[r0 + gs[q]].fj / M;
                    if (nab) hball += nax * nbx; else hcand += nax * nbx;
                    if (!nab || nprint < 50) {
                        nprint++;
                        printf("%s a=", nab ? "HBALL" : "HCAND"); spell(stdout, 0, &FB, fa); printf(" | b="); spell(stdout, 0, &FB, fb);
                        printf(" | |U_a|=%lld |U_b|=%lld common=%lld | u=", na, nb, nab);
                        for (int i = gs[p]; i < ge[p]; i++) if (!bad[i]) { spell(stdout, 1, &NB, E[r0 + i].fj % M); break; }
                        printf(" | v="); for (int i = gs[q]; i < ge[q]; i++) if (!bad[i]) { spell(stdout, 1, &NB, E[r0 + i].fj % M); break; }
                        printf("\n"); fflush(stdout);
                    }
                }
            }
        }
        r0 = r1;
    }
    printf("RESULT LA=%d LB=%d |FB|=%d |NB|=%d unordered_pairs=%lld shared_classes=%lld tuples(unordered)=%lld VCFAIL=%lld HBALL=%lld HCAND=%lld hash_collisions=%lld  %.0f s\n",
           LA, LB, nF, M, pairs, classes, tuples, vcfail, hball, hcand, coll, now() - t0);
    return 0;
}
