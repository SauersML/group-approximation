/* Orderly enumeration of closed-candidate forward tables up to six labels per side.
 *
 * This generalizes enumtables.c of experiments/gottschalk-residual-gap-census-2026-09-17 (at most four labels per
 * side) to at most six per side, and adds in-search pruning by the same difference closure.
 *
 * Labels S = {0..ns-1}, M = {0..nm-1}, label 0 is the identity on both sides. A forward table is a
 * rook-independent partition of S x M, written as a restricted growth string over the cells in row-major order.
 *
 * Difference closure (valid in every group): nodes D_S(a,b) = b^-1 a and D_M(a,b) = b a^-1; a relation
 * (s,m) ~ (s',m') means D_S(s,s') = D_M(m,m');
 *   R1  D(a,b) = D(c,d)                    =>  D(b,a) = D(d,c)
 *   R2  D(a,b) = D(c,d), D(b,e) = D(d,f)   =>  D(a,e) = D(c,f)
 * and every D(a,a) is the identity. A table is rejected when a nontrivial difference is the identity (label
 * collision) or when D_S(s,s') = D_M(m,m') for two cells in different blocks (NOTCLOSED).
 *
 * In-search pruning (mode "prune"): after each completed row the closure is run on the cells assigned so far.
 * The relations of a partial table are a subset of those of every completion, and the blocks of assigned cells
 * never change, so a rejection of the partial table is a rejection of every completion. No survivor is lost.
 * Mode "full" checks only complete tables and reproduces the counts of enumtables.c.
 *
 * usage: enumtables6 ns nm full|prune > reps.txt ; stats on stderr
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 6
#define MAXC (MAXN * MAXN)
#define NODES (2 * MAXC)

static int ns, nm, nc, prune = 0;
static int cls[MAXC];
static int rowmask[MAXC], colmask[MAXC];
static long long raw = 0, orbits = 0, survivors = 0, rej_coll = 0, rej_nc = 0, pruned = 0;
static int ps_list[120][MAXN], pm_list[120][MAXN];
static int nperm_s, nperm_m;

static void perms_rec(int n, int k, int *p, int used, int list[][MAXN], int *cnt) {
    if (k == n) {
        for (int i = 0; i < MAXN; i++) list[*cnt][i] = i < n ? p[i] : 0;
        (*cnt)++;
        return;
    }
    for (int v = 1; v < n; v++)
        if (!((used >> v) & 1)) {
            p[k] = v;
            perms_rec(n, k + 1, p, used | (1 << v), list, cnt);
        }
}

static void gen_perms(int n, int list[][MAXN], int *cnt) {
    int p[MAXN];
    p[0] = 0;
    *cnt = 0;
    perms_rec(n, 1, p, 0, list, cnt);
}

/* returns 1 if cls is the lexicographically minimal image */
static int is_canonical(void) {
    int img[MAXC], ren[MAXC];
    for (int t = 0; t < (ns == nm ? 2 : 1); t++) {
        for (int i = 0; i < nperm_s; i++)
            for (int j = 0; j < nperm_m; j++) {
                int *ps = ps_list[i], *pm = pm_list[j];
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

static int uf[NODES];
static int fnd(int x) { while (uf[x] != x) { uf[x] = uf[uf[x]]; x = uf[x]; } return x; }
static int uni(int x, int y) { x = fnd(x); y = fnd(y); if (x == y) return 0; if (x < y) uf[y] = x; else uf[x] = y; return 1; }
static inline int D(int side, int a, int b) { return side * MAXC + a * MAXN + b; }

/* closure on the first ncells cells; returns 1 if not rejected */
static int closure_ok(int ncells, int count) {
    for (int i = 0; i < NODES; i++) uf[i] = i;
    int id = D(0, 0, 0);
    for (int a = 0; a < ns; a++) uni(id, D(0, a, a));
    for (int a = 0; a < nm; a++) uni(id, D(1, a, a));
    for (int c1 = 0; c1 < ncells; c1++)
        for (int c2 = 0; c2 < ncells; c2++)
            if (c1 != c2 && cls[c1] == cls[c2]) {
                int s = c1 / nm, m = c1 % nm, s2 = c2 / nm, m2 = c2 % nm;
                uni(D(0, s, s2), D(1, m, m2));
            }
    int nn[2] = {ns, nm};
    int nodes[NODES], side[NODES], na[NODES], nb[NODES], nnodes = 0;
    for (int sd = 0; sd < 2; sd++)
        for (int a = 0; a < nn[sd]; a++)
            for (int b = 0; b < nn[sd]; b++) {
                nodes[nnodes] = D(sd, a, b); side[nnodes] = sd; na[nnodes] = a; nb[nnodes] = b; nnodes++;
            }
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < nnodes; i++) {
            int x = nodes[i], sx = side[i], a = na[i], b = nb[i];
            for (int j = 0; j < nnodes; j++) {
                int y = nodes[j];
                if (fnd(x) != fnd(y)) continue;
                int sy = side[j], c = na[j], d = nb[j];
                changed |= uni(D(sx, b, a), D(sy, d, c));
                for (int e = 0; e < nn[sx]; e++)
                    for (int f = 0; f < nn[sy]; f++)
                        if (fnd(D(sx, b, e)) == fnd(D(sy, d, f)))
                            changed |= uni(D(sx, a, e), D(sy, c, f));
            }
        }
    }
    int r = fnd(id);
    for (int sd = 0; sd < 2; sd++)
        for (int a = 0; a < nn[sd]; a++)
            for (int b = 0; b < nn[sd]; b++)
                if (a != b && fnd(D(sd, a, b)) == r) { if (count) rej_coll++; return 0; }
    for (int c1 = 0; c1 < ncells; c1++)
        for (int c2 = 0; c2 < ncells; c2++) {
            int s = c1 / nm, m = c1 % nm, s2 = c2 / nm, m2 = c2 % nm;
            if (s == s2 || m == m2) continue;
            if (cls[c1] != cls[c2] && fnd(D(0, s, s2)) == fnd(D(1, m, m2))) { if (count) rej_nc++; return 0; }
        }
    return 1;
}

static void rec(int i, int ncls, int joined) {
    if (i == nc) {
        raw++;
        if (!is_canonical()) return;
        orbits++;
        if (!closure_ok(nc, 1)) return;
        survivors++;
        for (int c = 0; c < nc; c++) printf("%d%c", cls[c], c + 1 == nc ? '\n' : ' ');
        return;
    }
    (void)joined;
    if (prune && i > 0 && i % nm == 0 && i < nc && !closure_ok(i, 0)) { pruned++; return; }
    int s = i / nm, m = i % nm;
    for (int k = 0; k <= ncls; k++) {
        if (k < ncls && (((rowmask[k] >> s) & 1) || ((colmask[k] >> m) & 1))) continue;
        int om = rowmask[k], oc = colmask[k];
        if (k == ncls) { rowmask[k] = 0; colmask[k] = 0; }
        rowmask[k] |= 1 << s; colmask[k] |= 1 << m;
        cls[i] = k;
        rec(i + 1, k == ncls ? ncls + 1 : ncls, k < ncls);
        if (k == ncls) { rowmask[k] = 0; colmask[k] = 0; } else { rowmask[k] = om; colmask[k] = oc; }
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: enumtables6 ns nm full|prune\n"); return 1; }
    ns = atoi(argv[1]); nm = atoi(argv[2]); nc = ns * nm;
    if (ns < 1 || nm < 1 || ns > MAXN || nm > MAXN) { fprintf(stderr, "sizes 1..%d\n", MAXN); return 1; }
    prune = strcmp(argv[3], "prune") == 0;
    gen_perms(ns, ps_list, &nperm_s);
    gen_perms(nm, pm_list, &nperm_m);
    rec(0, 0, 0);
    fprintf(stderr, "ns=%d nm=%d mode=%s raw=%lld orbits=%lld survivors=%lld rej_collision=%lld rej_notclosed=%lld pruned_subtrees=%lld\n",
            ns, nm, prune ? "prune" : "full", raw, orbits, survivors, rej_coll, rej_nc, pruned);
    return 0;
}
