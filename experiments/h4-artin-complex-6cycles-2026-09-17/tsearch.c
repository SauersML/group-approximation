/* Bottom-triple search in the Artin complex of a linear spherical diagram s1-...-sn (see search.py).
 * Garside normal forms (left-greedy, Delta^k * P) over tables dumped by dump.py.
 *
 * Triple model: x1 = A_X, y1 = A_Y, x2 = aA_X (a in R_Y(La)), y2 = abA_Y (b in R_X(Lb)),
 * x3 = abcA_X (c in R_Y(Lc)).  The pair {x1,x3} is upper bounded by uA_Y (u in A_X) iff
 * u^{-1}abc in A_Y A_X.  uA_Y is a quasi-centre iff additionally u^{-1}a in A_Y A_X.
 * y2 is a quasi-centre iff ab in A_X A_Y.
 * For each (a,b,c) with x3 != x1: if y2 is not a quasi-centre, scan u in R_X(Lu):
 *   P(u): u^{-1}abc in A_YA_X (padding K);  Q(u): u^{-1}a in A_YA_X.
 *   found  = some u with P and Q;  bounded = some u with P.
 * bounded && !found  -> candidate, rescanned with R_X(Lu2).
 * usage: tsearch PREFIX K K2 [selftest]   (env A0, A1 restrict the a-index range [A0,A1))
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXF 96
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
/* g positive (k>=0): strip maximal left A_mask^+ divisor, return remainder in r */
static void strip_left(const elt *g, int mask, elt *r) {
    elt h = *g;
    for (;;) {
        int first;
        if (h.k > 0) first = W0; else if (h.len > 0) first = h.P[0]; else { *r = h; return; }
        int t = parabolic_prefix(first, mask);
        if (t == 0) { *r = h; return; }
        /* rebuild: (inv[t]*first), rest */
        elt nh; nh.k = 0; nh.len = 0;
        append(&nh, wmul(inv_[t], first));
        if (h.k > 0) { for (int j = 1; j < h.k; j++) append(&nh, W0); for (int j = 0; j < h.len; j++) append(&nh, h.P[j]); }
        else { for (int j = 1; j < h.len; j++) append(&nh, h.P[j]); }
        h = nh;
    }
}
static int in_parabolic_positive(const elt *g, int mask) {
    if (g->k < 0) return 0;
    if (g->k > 0 && (supp_[W0] & ~mask)) return 0;
    for (int i = 0; i < g->len; i++) if (supp_[g->P[i]] & ~mask) return 0;
    return 1;
}
static elt DY, DX, DYn, DXn; /* padding Delta_Y^{2K}, Delta_X^{2K} precomputed */
static int padK = -1;
static void setpad(int K, int maskY, int maskX, elt *dy, elt *dx) {
    elt sy; sy.k = 0; sy.len = 1; sy.P[0] = (uint16_t)parabolic_w0(maskY);
    elt sx; sx.k = 0; sx.len = 1; sx.P[0] = (uint16_t)parabolic_w0(maskX);
    elt a; a.k = 0; a.len = 0; elt b = a, t;
    for (int i = 0; i < 2 * K; i++) { mul(&a, &sy, &t); a = t; mul(&b, &sx, &t); b = t; }
    *dy = a; *dx = b;
}
/* exact at padding K: Delta_Y^{2K} g Delta_X^{2K} in A_Y^+ A_X^+ */
static int in_product(const elt *g, const elt *dy, const elt *dx, int maskY, int maskX) {
    elt h, t;
    mul(dy, g, &t); mul(&t, dx, &h);
    if (h.k < 0) return 0;
    strip_left(&h, maskY, &t);
    return in_parabolic_positive(&t, maskX);
}
static int in_parabolic(const elt *g, const elt *dx, int maskX) {
    elt h; mul(dx, g, &h);
    return in_parabolic_positive(&h, maskX);
}

typedef struct { elt g; int pw; } rep;
static rep *readreps(FILE *f, int *cnt) {
    if (fscanf(f, "%d", cnt) != 1) exit(3);
    rep *R = malloc(sizeof(rep) * (*cnt));
    for (int i = 0; i < *cnt; i++) {
        int k, pw, L;
        if (fscanf(f, "%d %d %d", &k, &pw, &L) != 3) exit(3);
        R[i].g.k = k; R[i].g.len = L; R[i].pw = pw;
        for (int j = 0; j < L; j++) { int x; if (fscanf(f, "%d", &x) != 1) exit(3); R[i].g.P[j] = (uint16_t)x; }
    }
    return R;
}
static void printelt(FILE *o, const elt *g) {
    fprintf(o, "(%d,(", g->k);
    for (int i = 0; i < g->len; i++) fprintf(o, "%d,", g->P[i]);
    fprintf(o, "))");
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: tsearch PREFIX K [K2] [selftest]\n"); return 1; }
    char fn[512];
    int K = atoi(argv[2]);
    int K2 = argc > 3 ? atoi(argv[3]) : K;
    snprintf(fn, sizeof fn, "%s.tab", argv[1]);
    FILE *f = fopen(fn, "r");
    if (!f || fscanf(f, "%d %d %d %d %d %d", &n, &N, &W0, &MX, &MY, &MZ) != 6) return 3;
    len_ = malloc(4 * N); inv_ = malloc(4 * N); ld_ = malloc(4 * N); rd_ = malloc(4 * N);
    supp_ = malloc(4 * N); tau_ = malloc(4 * N); dcache_ = malloc(4 * N); wlen_ = malloc(4 * N);
    lmul_ = malloc(4 * N * n); rmul_ = malloc(4 * N * n); words_ = malloc(4 * N * 64);
    for (int w = 0; w < N; w++) {
        if (fscanf(f, "%d %d %d %d %d %d", &len_[w], &inv_[w], &ld_[w], &rd_[w], &supp_[w], &tau_[w]) != 6) return 3;
        for (int i = 0; i < n; i++) if (fscanf(f, "%d", &LMUL(w, i)) != 1) return 3;
        for (int i = 0; i < n; i++) if (fscanf(f, "%d", &RMUL(w, i)) != 1) return 3;
        if (fscanf(f, "%d", &wlen_[w]) != 1) return 3;
        for (int j = 0; j < wlen_[w]; j++) if (fscanf(f, "%d", &WORD(w)[j]) != 1) return 3;
    }
    fclose(f);
    for (int w = 0; w < N; w++) dcache_[w] = wmul(inv_[w], W0);
    snprintf(fn, sizeof fn, "%s.reps", argv[1]);
    f = fopen(fn, "r");
    int na, nb, nc, nu, nu2;
    rep *Ra = readreps(f, &na), *Rb = readreps(f, &nb), *Rc = readreps(f, &nc), *RU = readreps(f, &nu), *RU2 = readreps(f, &nu2);
    fclose(f);

    if (argc > 4) { /* selftest: print products a*b, inverses, and membership bits for python cross-check */
        setpad(K, MY, MX, &DY, &DX);
        for (int i = 0; i < na && i < 40; i++) for (int j = 0; j < nb && j < 40; j++) {
            elt ab, iab, t;
            mul(&Ra[i].g, &Rb[j].g, &ab); inverse(&ab, &iab); mul(&ab, &iab, &t);
            printf("%d %d ", i, j); printelt(stdout, &ab); printf(" "); printelt(stdout, &iab);
            printf(" %d %d %d\n", t.k == 0 && t.len == 0, in_product(&ab, &DY, &DX, MY, MX), in_product(&iab, &DY, &DX, MY, MX));
        }
        return 0;
    }

    /* W-level filter: WYX membership table */
    char *WYX = calloc(N, 1);
    {
        for (int y = 0; y < N; y++) if (!(supp_[y] & ~MY))
            for (int x = 0; x < N; x++) if (!(supp_[x] & ~MX)) WYX[wmul(y, x)] = 1;
    }
    elt dy, dx, dxy, dyx, dxX, dy2, dx2;
    setpad(K, MY, MX, &dy, &dx);      /* for A_Y A_X tests */
    setpad(K, MX, MY, &dxy, &dyx);    /* for A_X A_Y tests: left pad Delta_X, right pad Delta_Y */
    { elt tmp; setpad(K, MX, MX, &dxX, &tmp); }
    setpad(K2, MY, MX, &dy2, &dx2);
    elt *RUi = malloc(sizeof(elt) * nu); int *RUpi = malloc(4 * nu);
    for (int i = 0; i < nu; i++) { inverse(&RU[i].g, &RUi[i]); RUpi[i] = inv_[RU[i].pw]; }
    elt *RU2i = malloc(sizeof(elt) * nu2); int *RU2pi = malloc(4 * nu2);
    for (int i = 0; i < nu2; i++) { inverse(&RU2[i].g, &RU2i[i]); RU2pi[i] = inv_[RU2[i].pw]; }
    char *Qa = malloc((size_t)na * nu);
    for (int ia = 0; ia < na; ia++) for (int iu = 0; iu < nu; iu++) {
        Qa[(size_t)ia * nu + iu] = 0;
        if (!WYX[wmul(RUpi[iu], Ra[ia].pw)]) continue;
        elt t; mul(&RUi[iu], &Ra[ia].g, &t);
        Qa[(size_t)ia * nu + iu] = (char)in_product(&t, &dy, &dx, MY, MX);
    }
    long long triples = 0, deg = 0, triv2 = 0, bounded = 0, found = 0, cand = 0, resolved = 0, unresolved = 0;
    long long *uhist = calloc(nu, sizeof(long long));
    int A0 = getenv("A0") ? atoi(getenv("A0")) : 0, A1 = getenv("A1") ? atoi(getenv("A1")) : na;
    if (A1 > na) A1 = na;
    for (int ia = A0; ia < A1; ia++) for (int ib = 0; ib < nb; ib++) {
        elt ab; mul(&Ra[ia].g, &Rb[ib].g, &ab);
        int pab = wmul(Ra[ia].pw, Rb[ib].pw);
        int y2triv = in_product(&ab, &dxy, &dyx, MX, MY);
        for (int ic = 0; ic < nc; ic++) {
            elt abc; mul(&ab, &Rc[ic].g, &abc);
            int pabc = wmul(pab, Rc[ic].pw);
            triples++;
            if (!(supp_[pabc] & ~MX) && in_parabolic(&abc, &dxX, MX)) { deg++; continue; }
            if (y2triv) { triv2++; continue; }
            int isb = 0, isf = 0;
            for (int iu = 0; iu < nu; iu++) {
                if (!WYX[wmul(RUpi[iu], pabc)]) continue;
                elt t; mul(&RUi[iu], &abc, &t);
                if (!in_product(&t, &dy, &dx, MY, MX)) continue;
                isb = 1;
                if (Qa[(size_t)ia * nu + iu]) { isf = 1; uhist[iu]++; break; }
            }
            if (!isb) continue;
            bounded++;
            if (isf) { found++; continue; }
            cand++;
            /* rescan with the larger ball */
            int ok = 0;
            elt a = Ra[ia].g;
            for (int iu = 0; iu < nu2 && !ok; iu++) {
                if (!WYX[wmul(RU2pi[iu], pabc)] || !WYX[wmul(RU2pi[iu], Ra[ia].pw)]) continue;
                elt t; mul(&RU2i[iu], &abc, &t);
                if (!in_product(&t, &dy2, &dx2, MY, MX)) continue;
                mul(&RU2i[iu], &a, &t);
                if (in_product(&t, &dy2, &dx2, MY, MX)) ok = 1;
            }
            if (ok) resolved++;
            else {
                unresolved++;
                if (unresolved <= 20) {
                    printf("UNRESOLVED a=%d b=%d c=%d  ", ia, ib, ic);
                    printelt(stdout, &Ra[ia].g); printf(" "); printelt(stdout, &Rb[ib].g); printf(" "); printelt(stdout, &Rc[ic].g); printf("\n");
                    fflush(stdout);
                }
            }
        }
        if (ib == nb - 1) { fprintf(stderr, "a %d/%d bounded=%lld found=%lld cand=%lld unres=%lld\n", ia + 1, na, bounded, found, cand, unresolved); }
    }
    int maxu = 0; for (int iu = 0; iu < nu; iu++) if (uhist[iu]) maxu = iu;
    printf("{\"arange\":[%d,%d],\"sizes\":[%d,%d,%d,%d,%d],\"K\":%d,\"K2\":%d,\"triples\":%lld,\"x3_eq_x1\":%lld,\"y2_quasi_centre\":%lld,"
           "\"bounded_nontrivial\":%lld,\"found\":%lld,\"candidates\":%lld,\"resolved_Lu2\":%lld,\"unresolved\":%lld,\"max_u_index_used\":%d}\n",
           A0, A1, na, nb, nc, nu, nu2, K, K2, triples, deg, triv2, bounded, found, cand, resolved, unresolved, maxu);
    return 0;
}
