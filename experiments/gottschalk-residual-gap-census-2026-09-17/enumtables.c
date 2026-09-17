/* Enumerate orbit representatives of closed-candidate forward tables.
 *
 * Labels S = {0..ns-1}, M = {0..nm-1}, label 0 is the identity on both sides.
 * A forward table is a rook-independent partition of S x M (cell (s,m) = x_s x_m),
 * written as a restricted growth string over the ns*nm cells in row-major order.
 *
 * Output: one line per orbit (under Sym(S minus 0) x Sym(M minus 0), plus the
 * inversion/transpose symmetry when ns == nm) that survives the sound
 * difference-closure prefilter:
 *   nodes D_S(a,b) = b^{-1} a and D_M(a,b) = b a^{-1};
 *   a cell relation (s,m) ~ (s',m') means D_S(s,s') = D_M(m,m');
 *   closure rules, valid in every group:
 *     R1  D(a,b) = D(c,d)                      =>  D(b,a) = D(d,c)
 *     R2  D(a,b) = D(c,d), D(b,e) = D(d,f)     =>  D(a,e) = D(c,f)
 *   all D(a,a) are the identity.
 * Rejected: a nontrivial difference equal to the identity (label collision: the
 * table is never exactly realized with distinct labels), or D_S(s,s') = D_M(m,m')
 * for cells in different blocks (the table group derives a forward coincidence
 * outside T: NOTCLOSED). Every rejection is a genuine group-theoretic consequence
 * of the relators, so no realizable table is lost.
 *
 * usage: enumtables ns nm > reps.txt ; stats on stderr
 *        enumtables ns nm rejected > sample.txt  (every rejected orbit whose orbit index is divisible by 97)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int ns, nm, nc, emit_rejected = 0;
static int cls[16];
static int rowmask[16], colmask[16];
static long long raw = 0, orbits = 0, survivors = 0, rej_coll = 0, rej_nc = 0;

static int perms3[24][4];
static int nperm_s, nperm_m;
static int ps_list[24][4], pm_list[24][4];

static void gen_perms(int n, int list[][4], int *cnt) {
    /* permutations of {1..n-1}, 0 fixed */
    int p[4];
    *cnt = 0;
    int k = n - 1;
    int idx[3] = {0, 1, 2};
    (void)perms3; (void)idx;
    /* brute force */
    for (int a = 0; a < 4; a++)
        for (int b = 0; b < 4; b++)
            for (int c = 0; c < 4; c++) {
                int v[3] = {a, b, c};
                int ok = 1;
                for (int i = 0; i < k; i++) {
                    if (v[i] < 1 || v[i] > k) ok = 0;
                    for (int j = 0; j < i; j++) if (v[i] == v[j]) ok = 0;
                }
                for (int i = k; i < 3; i++) if (v[i] != 0) ok = 0;
                if (!ok) continue;
                p[0] = 0;
                for (int i = 0; i < k; i++) p[i + 1] = v[i];
                for (int i = 0; i < 4; i++) list[*cnt][i] = (i < n) ? p[i] : 0;
                (*cnt)++;
            }
}

/* returns 1 if cls is the lexicographically minimal image */
static int is_canonical(void) {
    int img[16], ren[16];
    for (int t = 0; t < (ns == nm ? 2 : 1); t++) {
        for (int i = 0; i < nperm_s; i++)
            for (int j = 0; j < nperm_m; j++) {
                int *ps = ps_list[i], *pm = pm_list[j];
                /* image cell (ps[s], pm[m]) gets class of (s,m); transpose: (pm[m], ps[s]) gets class of (s,m) */
                for (int s = 0; s < ns; s++)
                    for (int m = 0; m < nm; m++) {
                        if (t == 0) img[ps[s] * nm + pm[m]] = cls[s * nm + m];
                        else img[pm[m] * nm + ps[s]] = cls[s * nm + m];
                    }
                for (int k = 0; k < nc; k++) ren[k] = -1;
                int nxt = 0;
                for (int c = 0; c < nc; c++) {
                    int v = img[c];
                    if (ren[v] < 0) ren[v] = nxt++;
                    int r = ren[v];
                    if (r < cls[c]) return 0;
                    if (r > cls[c]) break;
                }
            }
    }
    return 1;
}

/* union-find on 32 nodes: side*16 + a*4 + b */
static int uf[32];
static int fnd(int x) { while (uf[x] != x) { uf[x] = uf[uf[x]]; x = uf[x]; } return x; }
static int uni(int x, int y) { x = fnd(x); y = fnd(y); if (x == y) return 0; if (x < y) uf[y] = x; else uf[x] = y; return 1; }
static inline int D(int side, int a, int b) { return side * 16 + a * 4 + b; }

static int closure_ok(void) {
    for (int i = 0; i < 32; i++) uf[i] = i;
    int id = D(0, 0, 0);
    for (int a = 0; a < ns; a++) uni(id, D(0, a, a));
    for (int a = 0; a < nm; a++) uni(id, D(1, a, a));
    for (int c1 = 0; c1 < nc; c1++)
        for (int c2 = 0; c2 < nc; c2++)
            if (c1 != c2 && cls[c1] == cls[c2]) {
                int s = c1 / nm, m = c1 % nm, s2 = c2 / nm, m2 = c2 % nm;
                uni(D(0, s, s2), D(1, m, m2));
            }
    int nn[2] = {ns, nm};
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int x = 0; x < 32; x++) {
            int sx = x / 16, a = (x / 4) % 4, b = x % 4;
            if (a >= nn[sx] || b >= nn[sx]) continue;
            for (int y = 0; y < 32; y++) {
                if (fnd(x) != fnd(y)) continue;
                int sy = y / 16, c = (y / 4) % 4, d = y % 4;
                if (c >= nn[sy] || d >= nn[sy]) continue;
                changed |= uni(D(sx, b, a), D(sy, d, c));
                for (int e = 0; e < nn[sx]; e++)
                    for (int f = 0; f < nn[sy]; f++)
                        if (fnd(D(sx, b, e)) == fnd(D(sy, d, f)))
                            changed |= uni(D(sx, a, e), D(sy, c, f));
            }
        }
    }
    int r = fnd(id);
    for (int side = 0; side < 2; side++)
        for (int a = 0; a < nn[side]; a++)
            for (int b = 0; b < nn[side]; b++)
                if (a != b && fnd(D(side, a, b)) == r) { rej_coll++; return 0; }
    for (int c1 = 0; c1 < nc; c1++)
        for (int c2 = 0; c2 < nc; c2++) {
            int s = c1 / nm, m = c1 % nm, s2 = c2 / nm, m2 = c2 % nm;
            if (s == s2 || m == m2) continue;
            if (cls[c1] != cls[c2] && fnd(D(0, s, s2)) == fnd(D(1, m, m2))) { rej_nc++; return 0; }
        }
    return 1;
}

static void rec(int i, int ncls) {
    if (i == nc) {
        raw++;
        if (!is_canonical()) return;
        orbits++;
        if (!closure_ok()) {
            if (emit_rejected && (orbits % 97) == 0)
                for (int c = 0; c < nc; c++) printf("%d%c", cls[c], c + 1 == nc ? '\n' : ' ');
            return;
        }
        survivors++;
        if (emit_rejected) return;
        for (int c = 0; c < nc; c++) printf("%d%c", cls[c], c + 1 == nc ? '\n' : ' ');
        return;
    }
    int s = i / nm, m = i % nm;
    for (int k = 0; k <= ncls; k++) {
        if (k < ncls && ((rowmask[k] >> s) & 1 || (colmask[k] >> m) & 1)) continue;
        int om = rowmask[k], oc = colmask[k];
        if (k == ncls) { rowmask[k] = 0; colmask[k] = 0; }
        rowmask[k] |= 1 << s; colmask[k] |= 1 << m;
        cls[i] = k;
        rec(i + 1, k == ncls ? ncls + 1 : ncls);
        if (k == ncls) { rowmask[k] = 0; colmask[k] = 0; } else { rowmask[k] = om; colmask[k] = oc; }
    }
}

int main(int argc, char **argv) {
    ns = atoi(argv[1]); nm = atoi(argv[2]); nc = ns * nm;
    emit_rejected = argc > 3;
    gen_perms(ns, ps_list, &nperm_s);
    gen_perms(nm, pm_list, &nperm_m);
    rec(0, 0);
    fprintf(stderr, "ns=%d nm=%d raw=%lld orbits=%lld survivors=%lld rej_collision=%lld rej_notclosed=%lld\n",
            ns, nm, raw, orbits, survivors, rej_coll, rej_nc);
    return 0;
}
