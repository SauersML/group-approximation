/* glift.c -- (jlift.c with per-relator exponents e=n1,n2,n3,n4) orderly generation of j-odometer models of H(n1,n2,n3,n4) (optionally / <<[a,c]^2>>) on the binary tree.
 *
 * Model at level k: permutations a,b,c,d of Z/2^k that are tree automorphisms (vertex x at level k has children
 * x and x+2^k), satisfying b^a=b^n, c^b=c^n, d^c=d^n, a^d=a^n (and [a,c]^2 if R), with a fixed:
 *     a(x) = x + 2^J  (mod 2^k),   so a is trivial on the top J levels and an odometer on each of the 2^J subtrees.
 * Right actions (GAP conventions): gh = first g then h, x^y = y^-1 x y.
 *
 * Lifting level k -> k+1 with a's lift fixed is an inhomogeneous F_2-linear system in the switch bits of b,c,d.
 * Classes are taken up to conjugation by the full centralizer C_k of a in W_k:
 *     C_k = { g(x) = x + r[x mod 2^J] : i -> i + r[i] (mod 2^J) is in W_J }.
 * Orderly generation: tuples are ordered lexicographically level by level (level-m block = switch bits of b, then
 * c, then d, at vertices 0..2^(m-1)-1).  The orbit minimum of a lift L of a canonical T restricts to T, so L is
 * canonical iff no g in C_(k+1) lying over Stab_(C_k)(T) makes it smaller.  Every class is visited exactly once.
 *
 * usage: jlift J MAXLEV [noR] [first] [n=3]   ; prints per-level class counts and order profiles.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <signal.h>
#include <time.h>

#define MAXK 11
#define MAXN (1 << MAXK)
#define MAXW ((3 * MAXN + 1 + 63) / 64 + 1)

static int J, MAXLEV, USE_R = 1, FIRST = 0, BASE = 3, TRANS = 0;   /* TRANS: quotient by translations only */
static int rels[5][64], rexp[5][64], rlen[5], nrels;    /* letters: +(g+1) or -(g+1), letter power rexp */
static int EXPS[4] = {0, 0, 0, 0};   /* e=n1,n2,n3,n4 : b^a=b^n1, c^b=c^n2, d^c=d^n3, a^d=a^n4 */
/* a letter g^e is walked (e mod 2N) steps at level k (N = 2^k): cycle lengths divide N, so endpoint and switch
   parities agree with the full power */
static inline int steps(int e, int N) { return e % (2 * N); }
static long long cnt[MAXK + 2], cand[MAXK + 2], phic[MAXK + 2][16];   /* phi mask: generators moving level 1 */
static int maxlo[MAXK + 2][4], maxfree[MAXK + 2];
static long long prof[MAXK + 2][MAXK + 1][MAXK + 1][MAXK + 1];   /* log2 ord b,c,d at each level */
static volatile sig_atomic_t stopall = 0, interrupted = 0;
static int SPL = -1, SPP = 1, SPR = 0;   /* split=L,P,R: below level L descend only from nodes #i with i%P==R */
static long long splitctr = 0;
static int DUMP = 0;   /* dump: print every canonical class at MAXLEV as one line 'b... | c... | d...' */
static int RANDM = 0;   /* rand=M,seed : existence search, M random lifts per node, no isomorph rejection */
static uint64_t rng = 88172645463325252ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static time_t t0, tlast;
static void onterm(int s) { (void)s; interrupted = 1; stopall = 1; }
static void report(FILE *f, const char *tag);

static void addrel(const char *s) {
    int L = 0;
    for (; *s; s++) {
        int c = *s, g = (c >= 'a') ? c - 'a' : c - 'A';
        rexp[nrels][L] = 1; rels[nrels][L++] = (c >= 'a') ? g + 1 : -(g + 1);
    }
    rlen[nrels++] = L;
}
static void conjrel(char x, char y, int n) {   /* y^-1 x y x^-n */
    char buf[64]; int L = 0;
    buf[L++] = y - 32; buf[L++] = x; buf[L++] = y; buf[L++] = x - 32;
    buf[L] = 0; addrel(buf); rexp[nrels - 1][3] = n;
}

typedef struct { int k; uint16_t p[4][MAXN]; } Tup;

static int ilog2(int x) { int l = 0; while (x > 1) { x >>= 1; l++; } return l; }
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int order(const uint16_t *p, int N) {
    static char seen[MAXN]; memset(seen, 0, N); int o = 1;
    for (int i = 0; i < N; i++) if (!seen[i]) {
        int l = 0, j = i; while (!seen[j]) { seen[j] = 1; j = p[j]; l++; }
        o = o / gcd(o, l) * l;
    }
    return o;
}
static void inv(const uint16_t *p, uint16_t *q, int N) { for (int i = 0; i < N; i++) q[p[i]] = i; }

/* group element: g(x) = x + r[x mod 2^J] mod 2^k ; stored as r[0..2^J-1] */
typedef struct { int n; int *r; } GList;   /* n elements, r has n*2^J entries */

static void gl_push(GList *G, const int *r) {
    int m = 1 << J;
    G->r = realloc(G->r, (size_t)(G->n + 1) * m * sizeof(int));
    memcpy(G->r + (size_t)G->n * m, r, m * sizeof(int)); G->n++;
}

/* compare the conjugate g p g^-1 (p = b,c,d) with T, lexicographically over level blocks mlo..k (level-m block =
   bit m-1 of p(y) for y < 2^(m-1)).  returns -1 if conj < T, 0 if equal, 1 if greater.  N = 2^k points. */
static int cmp_conj(const Tup *T, const int *r, int N, int mlo) {
    int msk = (1 << J) - 1;
    static uint16_t g[MAXN], gi[MAXN], pc[3][MAXN];
    for (int x = 0; x < N; x++) g[x] = (x + r[x & msk]) & (N - 1);
    inv(g, gi, N);
    for (int t = 1; t < 4; t++) { const uint16_t *p = T->p[t]; for (int y = 0; y < N; y++) pc[t-1][y] = g[p[gi[y]]]; }
    for (int m = mlo; m <= T->k; m++) {
        int h = 1 << (m - 1);
        for (int t = 1; t < 4; t++) {
            const uint16_t *p = T->p[t];
            for (int y = 0; y < h; y++) {
                int b1 = (pc[t-1][y] >> (m - 1)) & 1, b0 = (p[y] >> (m - 1)) & 1;
                if (b1 != b0) return b1 < b0 ? -1 : 1;
            }
        }
    }
    return 0;
}

/* ---------- F_2 linear algebra: rows of W words, bit 3N = rhs ---------- */
static int NW;
typedef struct { uint64_t w[MAXW]; } Row;
static inline int getb(const Row *r, int i) { return (r->w[i >> 6] >> (i & 63)) & 1; }
static inline void flipb(Row *r, int i) { r->w[i >> 6] ^= 1ULL << (i & 63); }
static inline void rxor(Row *a, const Row *b) { for (int i = 0; i < NW; i++) a->w[i] ^= b->w[i]; }

/* lift T (level k, N points) to level k+1; for each canonical lift call cb */
static void dfs(const Tup *T, const GList *S);

static void record(const Tup *T) {
    int k = T->k, N = 1 << k, lo[4];
    for (int t = 0; t < 4; t++) { lo[t] = ilog2(order(T->p[t], N)); if (lo[t] > maxlo[k][t]) maxlo[k][t] = lo[t]; }
    prof[k][lo[1]][lo[2]][lo[3]]++;
    { int ph = 0; for (int t = 0; t < 4; t++) if (T->p[t][0] & 1) ph |= 1 << t; phic[k][ph]++; }
    cnt[k]++;
}

static void build_lift(const Tup *T, Tup *L, const Row *sol, int N) {
    L->k = T->k + 1;
    for (int t = 0; t < 4; t++)
        for (int x = 0; x < N; x++) {
            int v;
            if (t == 0) v = ((x + (1 << J)) >= N);                     /* carry of a(x) = x + 2^J */
            else v = getb(sol, (t - 1) * N + x);
            L->p[t][x] = T->p[t][x] + (v ? N : 0);
            L->p[t][x + N] = T->p[t][x] + (v ? 0 : N);
        }
}

static void try_lift(const Tup *T, const GList *S, const Row *sol, int N) {
    static Tup Ls[MAXK + 2];
    Tup *L = &Ls[T->k + 1];
    build_lift(T, L, sol, N);
    cand[L->k]++;
    int m = 1 << J;
    GList S2 = {0, NULL};
    int *r = malloc(m * sizeof(int));
    for (int s = 0; s < S->n; s++)
        for (int e = 0; e < (1 << m); e++) {
            if (TRANS && e != 0 && e != (1 << m) - 1) continue;
            for (int i = 0; i < m; i++) r[i] = S->r[(size_t)s * m + i] + (((e >> i) & 1) ? N : 0);
            int c = cmp_conj(L, r, 2 * N, L->k);
            if (c < 0) { free(r); free(S2.r); return; }
            if (c == 0) gl_push(&S2, r);
        }
    free(r);
    dfs(L, &S2);
    free(S2.r);
}

static void dfs(const Tup *T, const GList *S) {
    if (stopall) return;
    record(T);
    int k = T->k, N = 1 << k;
    if (k == SPL && (splitctr++ % SPP) != SPR) return;
    if (time(NULL) - tlast >= 120) { tlast = time(NULL); report(stderr, "progress"); }
    if (k == MAXLEV) {
        if (DUMP) {
            printf("M");
            for (int t = 1; t < 4; t++) { printf(" |"); for (int x = 0; x < N; x++) printf(" %d", T->p[t][x]); }
            printf("\n");
        }
        if (FIRST) {
            stopall = 1;
            FILE *f = fopen("model.g", "w");   /* GAP permutations on 1..N (point x -> x+1) */
            fprintf(f, "# first %d-odometer model at level %d found by jlift\nmodel := [\n", J, k);
            for (int t = 0; t < 4; t++) {
                fprintf(f, "  PermList([");
                for (int x = 0; x < N; x++) fprintf(f, "%d%s", T->p[t][x] + 1, x + 1 < N ? "," : "");
                fprintf(f, "])%s\n", t < 3 ? "," : "");
            }
            fprintf(f, "];\n"); fclose(f);
        }
        return;
    }
    int nv = 3 * N; NW = (nv + 1 + 63) / 64;
    static uint16_t ivs[MAXK + 2][4][MAXN];
    uint16_t (*iv)[MAXN] = ivs[k];
    for (int t = 0; t < 4; t++) inv(T->p[t], iv[t], N);
    /* build and eliminate */
    Row *piv = calloc(nv, sizeof(Row)); char *has = calloc(nv, 1);
    Row e;
    for (int q = 0; q < nrels; q++)
        for (int x = 0; x < N; x++) {
            memset(&e, 0, sizeof e);
            int p = x;
            for (int l = 0; l < rlen[q]; l++) {
                int g = abs(rels[q][l]) - 1, s = rels[q][l] > 0;
                for (int st = steps(rexp[q][l], N); st > 0; st--) {
                    if (!s) p = iv[g][p];
                    if (g == 0) { if (p + (1 << J) >= N) flipb(&e, nv); }
                    else flipb(&e, (g - 1) * N + p);
                    if (s) p = T->p[g][p];
                }
            }
            /* reduce */
            for (int i = nv - 1; i >= 0; i--) if (getb(&e, i) && has[i]) rxor(&e, &piv[i]);
            int hb = -1; for (int i = nv - 1; i >= 0; i--) if (getb(&e, i)) { hb = i; break; }
            if (hb < 0) { if (getb(&e, nv)) { free(piv); free(has); return; } continue; }
            for (int i = 0; i < nv; i++) if (has[i] && getb(&piv[i], hb)) rxor(&piv[i], &e);
            piv[hb] = e; has[hb] = 1;
        }
    /* particular solution and free columns */
    int nf = 0; int *fr = malloc(nv * sizeof(int));
    for (int i = 0; i < nv; i++) if (!has[i]) fr[nf++] = i;
    if (nf > maxfree[k + 1]) maxfree[k + 1] = nf;
    if (nf > 40) { fprintf(stderr, "too many free vars %d at level %d\n", nf, k); exit(2); }
    Row sol; memset(&sol, 0, sizeof sol);
    for (int i = 0; i < nv; i++) if (has[i] && getb(&piv[i], nv)) flipb(&sol, i);
    Row *col = calloc(nf ? nf : 1, sizeof(Row));
    for (int f = 0; f < nf; f++) {
        flipb(&col[f], fr[f]);
        for (int i = 0; i < nv; i++) if (has[i] && getb(&piv[i], fr[f])) flipb(&col[f], i);
    }
    free(piv); free(has);
    int nw = NW;
    if (RANDM) {
        GList E = {0, NULL}; Row base0 = sol;
        for (int it = 0; it < RANDM && !stopall; it++) {
            Row s2 = base0;
            for (int f = 0; f < nf; f++) if (xr() & 1) rxor(&s2, &col[f]);
            static Tup Lr[MAXK + 2]; build_lift(T, &Lr[k + 1], &s2, N); cand[k + 1]++;
            dfs(&Lr[k + 1], &E); NW = nw;
        }
        free(col); free(fr); return;
    }
    /* Gray code enumeration */
    for (uint64_t it = 0; ; it++) {
        try_lift(T, S, &sol, N);
        NW = nw;
        if (stopall) break;
        if (it + 1 == (1ULL << nf)) break;
        int f = __builtin_ctzll(it + 1);
        rxor(&sol, &col[f]);
    }
    free(col); free(fr);
}

/* ---------- base level J: a = 1, (b,c,d) in W_J satisfying the relators, canonical under all of W_J ---------- */
static int nWJ; static uint16_t (*WJ)[MAXN];
static void gen_W(int k) {   /* all tree automorphisms of level k */
    int n = 1; WJ = malloc(sizeof *WJ); WJ[0][0] = 0;
    for (int l = 0; l < k; l++) {
        int N = 1 << l, n2 = n << N;
        uint16_t (*W2)[MAXN] = malloc((size_t)n2 * sizeof *W2);
        for (int i = 0; i < n; i++) for (int v = 0; v < (1 << N); v++) {
            uint16_t *q = W2[(size_t)i * (1 << N) + v];
            for (int x = 0; x < N; x++) { int s = (v >> x) & 1;
                q[x] = WJ[i][x] + (s ? N : 0); q[x + N] = WJ[i][x] + (s ? 0 : N); }
        }
        free(WJ); WJ = W2; n = n2;
    }
    nWJ = n;
}
static int relok(const Tup *T) {
    int N = 1 << T->k; static uint16_t iv[4][MAXN];
    for (int t = 0; t < 4; t++) inv(T->p[t], iv[t], N);
    for (int q = 0; q < nrels; q++) for (int x = 0; x < N; x++) {
        int p = x;
        for (int l = 0; l < rlen[q]; l++) { int g = abs(rels[q][l]) - 1;
            for (int st = steps(rexp[q][l], N); st > 0; st--) p = rels[q][l] > 0 ? T->p[g][p] : iv[g][p]; }
        if (p != x) return 0;
    }
    return 1;
}
static void base(void) {
    gen_W(J); int N = 1 << J;
    fprintf(stderr, "|W_%d| = %d\n", J, nWJ);
    Tup T; T.k = J; for (int x = 0; x < N; x++) T.p[0][x] = (x + (1 << J)) & (N - 1);
    int *r = malloc(N * sizeof(int));
    for (int ib = 0; ib < nWJ; ib++) for (int ic = 0; ic < nWJ; ic++) for (int id = 0; id < nWJ; id++) {
        memcpy(T.p[1], WJ[ib], N * 2); memcpy(T.p[2], WJ[ic], N * 2); memcpy(T.p[3], WJ[id], N * 2);
        if (!relok(&T)) continue;
        GList S = {0, NULL}; int ok = 1;
        for (int g = 0; g < nWJ && ok; g++) {
            for (int i = 0; i < N; i++) r[i] = (WJ[g][i] - i) & (N - 1);
            if (TRANS) { int cst = 1; for (int i = 1; i < N; i++) cst &= r[i] == r[0]; if (!cst) continue; }
            int c = cmp_conj(&T, r, N, 1);
            if (c < 0) ok = 0; else if (c == 0) gl_push(&S, r);
        }
        if (ok) dfs(&T, &S);
        free(S.r);
        if (stopall) break;
    }
    free(r);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: jlift J MAXLEV [noR] [first] [n=3]\n"); return 1; }
    J = atoi(argv[1]); MAXLEV = atoi(argv[2]);
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "noR")) USE_R = 0;
        else if (!strcmp(argv[i], "first")) FIRST = 1;
        else if (!strcmp(argv[i], "dump")) DUMP = 1;
        else if (!strcmp(argv[i], "trans")) TRANS = 1;
        else if (!strncmp(argv[i], "n=", 2)) BASE = atoi(argv[i] + 2);
        else if (!strncmp(argv[i], "e=", 2)) sscanf(argv[i] + 2, "%d,%d,%d,%d", &EXPS[0], &EXPS[1], &EXPS[2], &EXPS[3]);
        else if (!strncmp(argv[i], "rand=", 5)) { unsigned long long sd = 1; sscanf(argv[i] + 5, "%d,%llu", &RANDM, &sd); rng ^= sd * 0x9E3779B97F4A7C15ULL; xr(); }
        else if (!strncmp(argv[i], "split=", 6)) sscanf(argv[i] + 6, "%d,%d,%d", &SPL, &SPP, &SPR);
    }
    if (MAXLEV > MAXK - 1) MAXLEV = MAXK - 1;
    for (int t = 0; t < 4; t++) if (!EXPS[t]) EXPS[t] = BASE;
    conjrel('b', 'a', EXPS[0]); conjrel('c', 'b', EXPS[1]); conjrel('d', 'c', EXPS[2]); conjrel('a', 'd', EXPS[3]);
    if (USE_R) addrel("ACacACac");
    signal(SIGTERM, onterm); t0 = tlast = time(NULL);
    base();
    report(stdout, interrupted ? "INTERRUPTED (partial counts)" : "complete");
    return 0;
}

static void report(FILE *f, const char *tag) {
    fprintf(f, "exponents %d,%d,%d,%d ", EXPS[0], EXPS[1], EXPS[2], EXPS[3]);
    fprintf(f, "J %d base n %d R %d first %d split %d,%d,%d : %s after %lds\n", J, BASE, USE_R, FIRST, SPL, SPP, SPR,
            tag, (long)(time(NULL) - t0));
    for (int k = J; k <= MAXLEV; k++) {
        fprintf(f, "level %d classes %lld (lifts tried %lld, max free %d) max log2 ord(a,b,c,d) (%d,%d,%d,%d)%s\n",
               k, cnt[k], cand[k], maxfree[k], maxlo[k][0], maxlo[k][1], maxlo[k][2], maxlo[k][3],
               (SPL >= 0 && k > SPL) ? " [this shard]" : "");
        if (f == stdout) {
            fprintf(f, "   level-1 swap pattern (a,b,c,d):");
            for (int ph = 0; ph < 16; ph++) if (phic[k][ph]) fprintf(f, " %d%d%d%d:%lld", ph & 1, (ph >> 1) & 1, (ph >> 2) & 1, (ph >> 3) & 1, phic[k][ph]);
            fprintf(f, "\n");
        }
        if (f == stdout)
            for (int x = 0; x <= k; x++) for (int y = 0; y <= k; y++) for (int z = 0; z <= k; z++)
                if (prof[k][x][y][z]) fprintf(f, "   log2 ord(b,c,d) = (%d,%d,%d): %lld\n", x, y, z, prof[k][x][y][z]);
        if (!cnt[k]) { fprintf(f, "NO %d-ODOMETER MODEL AT LEVEL %d%s\n", J, k, SPL >= 0 && k > SPL ? " in this shard" : ""); break; }
    }
    fflush(f);
}
