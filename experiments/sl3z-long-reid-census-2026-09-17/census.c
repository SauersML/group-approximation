/* Long-Reid rho_k word census (Exp. Math. 20 (2011) 412-425, Prop 2.1).
 *
 * usage: census k L m nmax threads
 *   Phase 1: DFS over all freely reduced words of length <= L in x,X,y,Y
 *            (X = x^-1), computing rho_k(word) mod p = 2^61-1 together with
 *            its inverse. Flags, for cyclically reduced words:
 *              REL   word == I              (kernel element of rho_k|F)
 *              TOR t tr w = tr w^-1 = t in {0,1,2}   (finite order 3,4,6)
 *              NEG   tr w = tr w^-1 = -1    (-(unipotent) or order 2)
 *              UNI r tr w = tr w^-1 = 3, w != I, r = rank(w - I)
 *                    (r = 1: rank-one unipotent = transvection)
 *   Phase 2: hash table of all reduced words of length <= m; equal matrices
 *            u != v give relators u v^-1 (MITM, lengths <= 2m).
 *   Phase 3: for n = 1..nmax, DFS over words v of length <= m and look up
 *            Z^n v in the table: a hit means Z^n = u v^-1 lies in rho_k(F).
 * All hits are candidates mod p; they are re-verified exactly (big integers)
 * by verify.py.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
#include <stdatomic.h>

typedef uint64_t u64;
typedef int64_t i64;
typedef unsigned __int128 u128;
#define P ((1ULL << 61) - 1)

static inline u64 red(u128 x) {
    u64 lo = (u64)(x & P), hi = (u64)(x >> 61);
    u64 r = lo + hi;
    if (r >= P) r -= P;
    return r;
}
static inline u64 mulm(u64 a, u64 b) { return red((u128)a * b); }
static inline u64 addm(u64 a, u64 b) { u64 r = a + b; if (r >= P) r -= P; return r; }
static inline u64 modi(i64 a) { i64 r = a % (i64)P; if (r < 0) r += P; return (u64)r; }

typedef struct { u64 a[9]; } Mat;

static inline void mul(const Mat *A, const Mat *B, Mat *C) {
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) {
            u128 s = 0;
            for (int l = 0; l < 3; l++) s += (u128)A->a[3 * i + l] * B->a[3 * l + j];
            /* each product < 2^122, sum of 3 < 2^124: reduce twice */
            u64 lo = (u64)(s & P);
            u128 hi = s >> 61;
            u64 r = red((u128)lo + hi);
            C->a[3 * i + j] = r;
        }
}

static Mat G[4];   /* x, X, y, Y */
static Mat Zp;     /* z */
static int K, L, M, NMAX, NT;
static const char LET[4] = {'x', 'X', 'y', 'Y'};
static inline int inv(int c) { return c ^ 1; }

static void setmat(Mat *A, i64 v[9]) { for (int i = 0; i < 9; i++) A->a[i] = modi(v[i]); }

static void init(int k) {
    i64 x[9] = {1, -2, 3, 0, k, -1 - 2 * k, 0, 1, -2};
    i64 y[9] = {-2 - k, -1, 1, -2 - k, -2, 3, -1, -1, 2};
    i64 z[9] = {0, 0, 1, 1, 0, -k, 0, 1, -1 - k};
    /* inverses by adjugate (det = 1) */
    i64 xi[9], yi[9];
    i64 *s[2] = {x, y}, *d[2] = {xi, yi};
    for (int t = 0; t < 2; t++) {
        i64 *a = s[t], *b = d[t];
        b[0] = a[4] * a[8] - a[5] * a[7]; b[1] = a[2] * a[7] - a[1] * a[8]; b[2] = a[1] * a[5] - a[2] * a[4];
        b[3] = a[5] * a[6] - a[3] * a[8]; b[4] = a[0] * a[8] - a[2] * a[6]; b[5] = a[2] * a[3] - a[0] * a[5];
        b[6] = a[3] * a[7] - a[4] * a[6]; b[7] = a[1] * a[6] - a[0] * a[7]; b[8] = a[0] * a[4] - a[1] * a[3];
    }
    setmat(&G[0], x); setmat(&G[1], xi); setmat(&G[2], y); setmat(&G[3], yi); setmat(&Zp, z);
}

static inline u64 tr(const Mat *A) { return addm(addm(A->a[0], A->a[4]), A->a[8]); }
static inline int isI(const Mat *A) {
    return A->a[0] == 1 && A->a[4] == 1 && A->a[8] == 1 && A->a[1] == 0 && A->a[2] == 0 && A->a[3] == 0 &&
           A->a[5] == 0 && A->a[6] == 0 && A->a[7] == 0;
}
static int rankMI(const Mat *A) {
    u64 b[9];
    for (int i = 0; i < 9; i++) b[i] = A->a[i];
    b[0] = (b[0] + P - 1) % P; b[4] = (b[4] + P - 1) % P; b[8] = (b[8] + P - 1) % P;
    int nz = 0;
    for (int i = 0; i < 9; i++) if (b[i]) nz = 1;
    if (!nz) return 0;
    for (int r1 = 0; r1 < 3; r1++)
        for (int r2 = r1 + 1; r2 < 3; r2++)
            for (int c1 = 0; c1 < 3; c1++)
                for (int c2 = c1 + 1; c2 < 3; c2++) {
                    u64 m = (mulm(b[3 * r1 + c1], b[3 * r2 + c2]) + P - mulm(b[3 * r1 + c2], b[3 * r2 + c1])) % P;
                    if (m) return 2;
                }
    return 1;
}

static pthread_mutex_t outmu = PTHREAD_MUTEX_INITIALIZER;
#define NCAT 9
static atomic_llong cnt[NCAT];      /* REL TOR0 TOR1 TOR2 NEG UNI2 UNI1 NODES EIG1 */
static atomic_int minlen[NCAT];
static atomic_int printed[NCAT];
static const char *CATN[NCAT] = {"REL", "TOR3", "TOR4", "TOR6", "NEG", "UNI-regular", "UNI-transvection", "nodes", "EIG1-other"};
static int PRINTLIM[NCAT] = {40, 20, 20, 20, 20, 30, 200, 0, 0};

static inline u64 adjtr(const Mat *A);
static int PALMODE = 0;

/* canonical: lexicographically minimal among cyclic rotations, and primitive
 * (in palindrome mode only primitivity is required) */
static int canonical(const int *w, int len) {
    for (int r = 1; r < len; r++) {
        if (PALMODE) {
            if (len % r) continue;
            int eq = 1;
            for (int i = 0; i < len && eq; i++) if (w[(i + r) % len] != w[i]) eq = 0;
            if (eq) return 0;
            continue;
        }
        int cmp = 0;
        for (int i = 0; i < len && !cmp; i++) {
            int a = w[(i + r) % len], b = w[i];
            if (a != b) cmp = a < b ? -1 : 1;
        }
        if (cmp < 0) return 0;
        if (cmp == 0) return 0; /* proper power */
    }
    return 1;
}

#define MAXTV 16
static Mat TV[MAXTV];
static int TVw[MAXTV][128], TVlen[MAXTV];
static atomic_int ntv;

static void report(int cat, const int *w, int len) {
    if (!canonical(w, len)) return;
    cnt[cat]++;
    int ml = minlen[cat];
    while (len < ml && !atomic_compare_exchange_weak(&minlen[cat], &ml, len));
    if (printed[cat] >= PRINTLIM[cat]) return;
    printed[cat]++;
    char buf[256];
    for (int i = 0; i < len; i++) buf[i] = LET[w[i]];
    buf[len] = 0;
    pthread_mutex_lock(&outmu);
    printf("HIT k=%d %s len=%d %s\n", K, CATN[cat], len, buf);
    fflush(stdout);
    pthread_mutex_unlock(&outmu);
}

static void examine(const Mat *A, const Mat *Ai, const int *w, int len) {
    if (len > 1 && w[0] == inv(w[len - 1])) return; /* not cyclically reduced */
    u64 t = tr(A), s = Ai ? tr(Ai) : adjtr(A);
    if (t != s) return;
    if (t == 3) {
        if (isI(A)) { report(0, w, len); return; }
        int r = rankMI(A);
        report(r == 1 ? 6 : 5, w, len);
        if (r == 1 && canonical(w, len)) {
            pthread_mutex_lock(&outmu);
            int j = ntv;
            if (j < MAXTV) {
                TV[j] = *A; TVlen[j] = len;
                for (int i = 0; i < len; i++) TVw[j][i] = w[i];
                ntv = j + 1;
            }
            pthread_mutex_unlock(&outmu);
        }
    } else if (t == 0) report(1, w, len);
    else if (t == 1) report(2, w, len);
    else if (t == 2) report(3, w, len);
    else if (t == P - 1) report(4, w, len);
    else report(8, w, len);
}

typedef struct { int pre[3]; } Job;
static Job jobs[64];
static int njobs;
static atomic_int nextjob;

static void *worker(void *arg) {
    (void)arg;
    Mat st[128], sti[128];
    int w[128], ch[128];
    long long nodes = 0;
    for (;;) {
        int j = atomic_fetch_add(&nextjob, 1);
        if (j >= njobs) break;
        int *pre = jobs[j].pre;
        /* build prefix */
        mul(&G[pre[0]], &G[pre[1]], &st[1]);
        mul(&G[inv(pre[1])], &G[inv(pre[0])], &sti[1]);
        mul(&st[1], &G[pre[2]], &st[2]);
        mul(&G[inv(pre[2])], &sti[1], &sti[2]);
        w[0] = pre[0]; w[1] = pre[1]; w[2] = pre[2];
        examine(&st[2], &sti[2], w, 3);
        nodes++;
        /* depth d means word length d+1 stored at st[d] */
        int d = 2;
        ch[3] = -1;
        while (d >= 2) {
            if (d + 1 >= L) { d--; continue; }
            int c = ++ch[d + 1];
            if (c > 3) { d--; continue; }
            if (c == inv(w[d])) continue;
            w[d + 1] = c;
            mul(&st[d], &G[c], &st[d + 1]);
            mul(&G[inv(c)], &sti[d], &sti[d + 1]);
            nodes++;
            examine(&st[d + 1], &sti[d + 1], w, d + 2);
            d++;
            ch[d + 1] = -1;
        }
    }
    cnt[7] += nodes;
    return NULL;
}

/* ---- phase 2/3: hash table ---- */
static inline u64 hmat(const Mat *A) {
    static const u64 R[9] = {0x9E3779B97F4A7C15ULL, 0xC2B2AE3D27D4EB4FULL, 0x165667B19E3779F9ULL,
                             0xD6E8FEB86659FD93ULL, 0xFF51AFD7ED558CCDULL, 0xC4CEB9FE1A85EC53ULL,
                             0x94D049BB133111EBULL, 0xBF58476D1CE4E5B9ULL, 0x2545F4914F6CDD1DULL};
    u64 h = 0;
    for (int i = 0; i < 9; i++) h += A->a[i] * R[i] ^ (A->a[i] >> 29);
    h ^= h >> 31; h *= 0x7FB5D329728EA185ULL; h ^= h >> 27;
    return h | 1; /* 0 = empty */
}
static u64 *TH;   /* hash */
static u64 *TW;   /* word code: letters in 2 bits, length in top 6 bits */
static u64 TMASK;

static u64 encode(const int *w, int len) {
    u64 c = (u64)len << 58;
    for (int i = 0; i < len; i++) c |= (u64)w[i] << (2 * i);
    return c;
}
static int decode(u64 c, int *w) {
    int len = (int)(c >> 58);
    for (int i = 0; i < len; i++) w[i] = (c >> (2 * i)) & 3;
    return len;
}
static void wstr(const int *w, int len, char *buf) { for (int i = 0; i < len; i++) buf[i] = LET[w[i]]; buf[len] = 0; }

static int relprinted = 0, relmin = 1000;
static long long relcount = 0;

static void insert(const Mat *A, const int *w, int len) {
    u64 h = hmat(A), i = h & TMASK;
    while (TH[i]) {
        if (TH[i] == h) {
            int u[64];
            int lu = decode(TW[i], u);
            /* relator u * w^-1 ; free reduction cancels common suffix */
            int a = lu, b = len;
            while (a > 0 && b > 0 && u[a - 1] == w[b - 1]) { a--; b--; }
            int rl = a + b;
            if (rl == 0) return;
            relcount++;
            if (rl < relmin) relmin = rl;
            if (relprinted < 40) {
                char s1[128], s2[128];
                wstr(u, lu, s1); wstr(w, len, s2);
                printf("MITM k=%d relator_len=%d u=%s v=%s\n", K, rl, s1, s2);
                relprinted++;
            }
            return;
        }
        i = (i + 1) & TMASK;
    }
    TH[i] = h; TW[i] = encode(w, len);
}
static long long lookup(const Mat *A) {
    u64 h = hmat(A), i = h & TMASK;
    while (TH[i]) { if (TH[i] == h) return (long long)i; i = (i + 1) & TMASK; }
    return -1;
}

static void dfs_table(int mode, const Mat *start, int n) {
    /* mode 0: insert all reduced words length <= M; mode 1: lookup start*v */
    Mat st[64];
    int w[64], ch[64];
    st[0] = *start;
    if (mode == 0) insert(&st[0], w, 0);
    else {
        long long j = lookup(&st[0]);
        if (j >= 0) { int u[64]; int lu = decode(TW[j], u); char s1[128]; wstr(u, lu, s1); printf("ZPOW k=%d n=%d Z^n = %s\n", K, n, s1); }
    }
    int d = 0;
    ch[0] = -1;
    int found = 0;
    while (d >= 0) {
        if (d >= M) { d--; continue; }
        int c = ++ch[d];
        if (c > 3) { d--; continue; }
        if (d > 0 && c == inv(w[d - 1])) continue;
        w[d] = c;
        mul(&st[d], &G[c], &st[d + 1]);
        if (mode == 0) insert(&st[d + 1], w, d + 1);
        else if (found < 5) {
            long long j = lookup(&st[d + 1]);
            if (j >= 0) {
                int u[64]; int lu = decode(TW[j], u);
                char s1[128], s2[128]; wstr(u, lu, s1);
                /* Z^n v = u  => Z^n = u v^-1 */
                int vi[64]; for (int i = 0; i <= d; i++) vi[i] = inv(w[d - i]);
                wstr(vi, d + 1, s2);
                printf("ZPOW k=%d n=%d Z^n = %s.%s\n", K, n, s1, s2);
                found++;
            }
        }
        d++;
        ch[d] = -1;
    }
}

/* Partner search: for a transvection t = I + v w^T, words g with w^T g v = 0 = w^T g^-1 v
 * give a conjugate g t g^-1 = I + (g v)(w^T g^-1) commuting with t; it generates Z^2 with t
 * unless g v || v and w^T g^-1 || w^T. */
static void partner_search(int L2) {
    int nt = ntv;
    for (int j = 0; j < nt; j++) {
        Mat *A = &TV[j];
        u64 b[9];
        for (int i = 0; i < 9; i++) b[i] = A->a[i];
        b[0] = (b[0] + P - 1) % P; b[4] = (b[4] + P - 1) % P; b[8] = (b[8] + P - 1) % P;
        u64 v[3] = {0, 0, 0}, wv[3] = {0, 0, 0};
        for (int c = 0; c < 3; c++) if (b[c] || b[3 + c] || b[6 + c]) { v[0] = b[c]; v[1] = b[3 + c]; v[2] = b[6 + c]; break; }
        for (int r = 0; r < 3; r++) if (b[3 * r] || b[3 * r + 1] || b[3 * r + 2]) { wv[0] = b[3 * r]; wv[1] = b[3 * r + 1]; wv[2] = b[3 * r + 2]; break; }
        char s[256]; wstr(TVw[j], TVlen[j], s);
        int found = 0;
        Mat st[64], sti[64];
        int w[64], ch[64];
        Mat I = {{1, 0, 0, 0, 1, 0, 0, 0, 1}};
        st[0] = I; sti[0] = I;
        int d = 0; ch[0] = -1;
        while (d >= 0 && found < 3) {
            if (d >= L2) { d--; continue; }
            int c = ++ch[d];
            if (c > 3) { d--; continue; }
            if (d > 0 && c == inv(w[d - 1])) continue;
            w[d] = c;
            mul(&st[d], &G[c], &st[d + 1]);
            mul(&G[inv(c)], &sti[d], &sti[d + 1]);
            d++; ch[d] = -1;
            u64 gv[3], giv[3];
            for (int r = 0; r < 3; r++) {
                gv[r] = addm(addm(mulm(st[d].a[3 * r], v[0]), mulm(st[d].a[3 * r + 1], v[1])), mulm(st[d].a[3 * r + 2], v[2]));
                giv[r] = addm(addm(mulm(sti[d].a[3 * r], v[0]), mulm(sti[d].a[3 * r + 1], v[1])), mulm(sti[d].a[3 * r + 2], v[2]));
            }
            u64 e1 = addm(addm(mulm(wv[0], gv[0]), mulm(wv[1], gv[1])), mulm(wv[2], gv[2]));
            if (e1) continue;
            u64 e2 = addm(addm(mulm(wv[0], giv[0]), mulm(wv[1], giv[1])), mulm(wv[2], giv[2]));
            if (e2) continue;
            /* parallel test: gv || v and w^T g^-1 || w^T */
            int par1 = 1, par2 = 1;
            for (int r1 = 0; r1 < 3; r1++) for (int r2 = r1 + 1; r2 < 3; r2++)
                if ((mulm(gv[r1], v[r2]) + P - mulm(gv[r2], v[r1])) % P) par1 = 0;
            u64 wg[3];
            for (int c2 = 0; c2 < 3; c2++)
                wg[c2] = addm(addm(mulm(wv[0], sti[d].a[c2]), mulm(wv[1], sti[d].a[3 + c2])), mulm(wv[2], sti[d].a[6 + c2]));
            for (int r1 = 0; r1 < 3; r1++) for (int r2 = r1 + 1; r2 < 3; r2++)
                if ((mulm(wg[r1], wv[r2]) + P - mulm(wg[r2], wv[r1])) % P) par2 = 0;
            if (par1 && par2) continue;
            char s2[128]; wstr(w, d, s2);
            printf("PAIR k=%d t=%s g=%s (t, g t g^-1 commute, independent)\n", K, s, s2);
            fflush(stdout);
            found++;
        }
        if (!found) printf("NOPAIR k=%d t=%s L2=%d\n", K, s, L2);
    }
}

/* ---- palindrome-type search: words a . phi(a), phi a signed-permutation anti-automorphism ---- */
static int PHI[8][4];
static int NPHI = 0;

static inline u64 adjtr(const Mat *A) {
    const u64 *a = A->a;
    u64 m0 = (mulm(a[4], a[8]) + P - mulm(a[5], a[7])) % P;
    u64 m1 = (mulm(a[0], a[8]) + P - mulm(a[2], a[6])) % P;
    u64 m2 = (mulm(a[0], a[4]) + P - mulm(a[1], a[3])) % P;
    return addm(addm(m0, m1), m2);
}

static void pal_examine(const Mat *A, const Mat *R, const int *w, int n, int f) {
    int c0 = w[0], cl = w[n - 1];
    if (PHI[f][cl] == inv(cl)) return;   /* a.phi(a) not freely reduced */
    if (PHI[f][c0] == inv(c0)) return;   /* not cyclically reduced */
    Mat Pm;
    mul(A, R, &Pm);
    u64 t = tr(&Pm);
    if (t != 3) {
        if (t == 0 || t == 1 || t == 2 || t == P - 1) {
            if (adjtr(&Pm) == t) {
                int full[256];
                for (int i = 0; i < n; i++) { full[i] = w[i]; full[2 * n - 1 - i] = PHI[f][w[i]]; }
                examine(&Pm, NULL, full, 2 * n);
            }
        }
        return;
    }
    if (adjtr(&Pm) != 3) return;
    int full[256];
    for (int i = 0; i < n; i++) { full[i] = w[i]; full[2 * n - 1 - i] = PHI[f][w[i]]; }
    examine(&Pm, NULL, full, 2 * n);
}

static void *pal_worker(void *arg) {
    (void)arg;
    Mat st[128];
    Mat rt[8][128];
    int w[128], ch[128];
    long long nodes = 0;
    for (;;) {
        int j = atomic_fetch_add(&nextjob, 1);
        if (j >= njobs) break;
        int *pre = jobs[j].pre;
        mul(&G[pre[0]], &G[pre[1]], &st[1]);
        mul(&st[1], &G[pre[2]], &st[2]);
        for (int f = 0; f < NPHI; f++) {
            mul(&G[PHI[f][pre[1]]], &G[PHI[f][pre[0]]], &rt[f][1]);
            mul(&G[PHI[f][pre[2]]], &rt[f][1], &rt[f][2]);
        }
        w[0] = pre[0]; w[1] = pre[1]; w[2] = pre[2];
        for (int f = 0; f < NPHI; f++) pal_examine(&st[2], &rt[f][2], w, 3, f);
        int d = 2;
        ch[3] = -1;
        while (d >= 2) {
            if (d + 1 >= L) { d--; continue; }
            int c = ++ch[d + 1];
            if (c > 3) { d--; continue; }
            if (c == inv(w[d])) continue;
            w[d + 1] = c;
            mul(&st[d], &G[c], &st[d + 1]);
            for (int f = 0; f < NPHI; f++) {
                mul(&G[PHI[f][c]], &rt[f][d], &rt[f][d + 1]);
                pal_examine(&st[d + 1], &rt[f][d + 1], w, d + 2, f);
            }
            nodes++;
            d++;
            ch[d + 1] = -1;
        }
    }
    cnt[7] += nodes;
    return NULL;
}

static void pal_main(void) {
    /* signed permutations: phi(x) in {x,X,y,Y}, phi(y) in the other pair; exclude phi = inverse */
    for (int ix = 0; ix < 4; ix++)
        for (int s = 0; s < 2; s++) {
            int iy = ((ix >> 1) ^ 1) << 1 | s;
            if (ix == 1 && iy == 3) continue;
            int *ph = PHI[NPHI];
            ph[0] = ix; ph[1] = inv(ix); ph[2] = iy; ph[3] = inv(iy);
            NPHI++;
        }
    for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) for (int c = 0; c < 4; c++) {
        if (b == inv(a) || c == inv(b)) continue;
        jobs[njobs].pre[0] = a; jobs[njobs].pre[1] = b; jobs[njobs].pre[2] = c; njobs++;
    }
    pthread_t th[64];
    for (int t = 0; t < NT; t++) pthread_create(&th[t], NULL, pal_worker, NULL);
    for (int t = 0; t < NT; t++) pthread_join(th[t], NULL);
    printf("PALSUMMARY k=%d halfL=%d nphi=%d", K, L, NPHI);
    for (int c = 0; c < NCAT; c++) printf(" %s=%lld(min %d)", CATN[c], (long long)cnt[c], c == 7 ? 0 : minlen[c]);
    printf("\n");
    fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: census k L m nmax threads [L2]\n"); return 1; }
    K = atoi(argv[1]); L = atoi(argv[2]); M = atoi(argv[3]); NMAX = atoi(argv[4]); NT = atoi(argv[5]);
    int L2 = argc > 6 ? atoi(argv[6]) : 12;
    if (getenv("EIG1LIM")) PRINTLIM[8] = atoi(getenv("EIG1LIM"));
    init(K);
    for (int c = 0; c < NCAT; c++) minlen[c] = 1000;
    if (argc > 7 && !strcmp(argv[7], "pal")) {
        PALMODE = 1;
        pal_main();
        partner_search(L2);
        return 0;
    }
    /* phase 1 */
    if (L >= 1) {
        int w[4];
        Mat A, Ai, B, Bi;
        for (int a = 0; a < 4; a++) {
            w[0] = a; examine(&G[a], &G[inv(a)], w, 1);
            for (int b = 0; b < 4; b++) {
                if (b == inv(a) || L < 2) continue;
                w[1] = b; mul(&G[a], &G[b], &A); mul(&G[inv(b)], &G[inv(a)], &Ai);
                examine(&A, &Ai, w, 2);
            }
        }
        (void)B; (void)Bi;
        if (L >= 3) {
            for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) for (int c = 0; c < 4; c++) {
                if (b == inv(a) || c == inv(b)) continue;
                jobs[njobs].pre[0] = a; jobs[njobs].pre[1] = b; jobs[njobs].pre[2] = c; njobs++;
            }
            pthread_t th[64];
            for (int t = 0; t < NT; t++) pthread_create(&th[t], NULL, worker, NULL);
            for (int t = 0; t < NT; t++) pthread_join(th[t], NULL);
        }
        printf("SUMMARY k=%d L=%d", K, L);
        for (int c = 0; c < NCAT; c++) printf(" %s=%lld(min %d)", CATN[c], (long long)cnt[c], c == 7 ? 0 : minlen[c]);
        printf("\n");
        fflush(stdout);
        partner_search(L2);
    }
    /* phase 2 */
    if (M >= 1) {
        u64 total = 1;
        u64 p3 = 1;
        for (int j = 1; j <= M; j++) { total += 4 * p3; p3 *= 3; }
        u64 sz = 1;
        while (sz < total * 2) sz <<= 1;
        TMASK = sz - 1;
        TH = calloc(sz, 8); TW = calloc(sz, 8);
        if (!TH || !TW) { fprintf(stderr, "alloc failed\n"); return 2; }
        Mat I = {{1, 0, 0, 0, 1, 0, 0, 0, 1}};
        dfs_table(0, &I, 0);
        printf("MITMSUMMARY k=%d m=%d words=%llu collisions=%lld shortest_relator=%d\n", K, M, (unsigned long long)total,
               relcount, relcount ? relmin : -1);
        fflush(stdout);
        /* phase 3 */
        Mat Zn = I, T;
        for (int n = 1; n <= NMAX; n++) {
            mul(&Zn, &Zp, &T); Zn = T;
            dfs_table(1, &Zn, n);
        }
        printf("ZPOWDONE k=%d nmax=%d\n", K, NMAX);
    }
    return 0;
}
