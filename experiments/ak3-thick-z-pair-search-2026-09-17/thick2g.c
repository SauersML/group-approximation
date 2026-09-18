/* thick2g.c: thick2.c (experiments/ac-thickenable-orbit-2026-09-17) with a genus bound.
   thick2g(nrel,lens,letters,cap,d) returns 1 iff some rotation system has total link-surface genus <= d
   (d = 0 is exactly thick2); 0 if none, -1 not cyclically reduced, -2 node cap hit.
   Sum over faces (len-2) = 2V - 4c + 4g, so the target X becomes 2V - 4c + 4d and a leaf succeeds when <= X.
   Neuwirth thickenability test, face-tracing DFS with bigon-first propagation.
   int thick2(int nrel, const int *lens, const int *letters): letters +-(g+1), g<8.
   Link graph: half-edge id 2k+s (k = occurrence, s=0 side o, s=1 side i).
   rot(k,o) = (sigma(k),o), rot(k,i) = (sigma^{-1}(k),i), sigma_g one cycle per generator.
   Face permutation phi(h) = twin(rot(h)); planar iff sum over faces (len-2) = X = 2V-4c.
   Returns 1 thickenable, 0 not, -1 not cyclically reduced.
   Build: gcc -O2 -shared -fPIC -o libthick2.so thick2.c */
#include <string.h>
#define MAXN 512
static int N, H, X, twin[2 * MAXN], gen[MAXN], ngen[8];
static int sig[MAXN], sinv[MAXN];
static long nodes, node_cap;

static inline int rot(int h) {
    int k = h >> 1, s = h & 1;
    if (s == 0) return sig[k] < 0 ? -1 : 2 * sig[k];
    return sinv[k] < 0 ? -1 : 2 * sinv[k] + 1;
}
static inline int phi(int h) { int r = rot(h); return r < 0 ? -1 : twin[r]; }

static int ph[2 * MAXN], haspred[2 * MAXN], seen[2 * MAXN], plen[2 * MAXN], ptail[2 * MAXN];
static int premature(int a, int b);
/* can the open path head..tail be closed by the single assignment rot(tail) = twin(head)? */
static int can_close(int head, int tail) {
    int t = twin[head];
    int kt = tail >> 1, st = tail & 1, kh = t >> 1, sh = t & 1;
    if (st != sh || gen[kt] != gen[kh]) return 0;
    if (st == 0) { /* sigma(kt) = kh */
        if (sinv[kh] >= 0) return 0;
        if (kt == kh) return ngen[gen[kt]] == 1;
        return !premature(kt, kh);
    } else {       /* sigma^{-1}(kt) = kh, i.e. sigma(kh) = kt */
        if (sig[kh] >= 0) return 0;
        if (kt == kh) return ngen[gen[kt]] == 1;
        return !premature(kh, kt);
    }
}
/* lower bound on excess; also returns best open path tail (h with phi unknown, maximal length) */
static int lb(int *best_tail) {
    int i, tot = 0, bl = -1, bt = -1;
    for (i = 0; i < H; i++) { haspred[i] = 0; seen[i] = 0; }
    for (i = 0; i < H; i++) { ph[i] = phi(i); if (ph[i] >= 0) haspred[ph[i]] = 1; }
    for (i = 0; i < H; i++) {
        if (haspred[i]) continue;
        int x = i, n = 0, last = i;
        while (x >= 0) { seen[x] = 1; n++; last = x; x = ph[x]; }
        if (n >= 2) tot += n - 2 + (can_close(i, last) ? 0 : 1);
        if (n > bl) { bl = n; bt = last; }
        if (tot > X) return tot;
    }
    for (i = 0; i < H; i++) {
        if (seen[i]) continue;
        int x = i, n = 0;
        while (!seen[x]) { seen[x] = 1; n++; x = ph[x]; }
        tot += n - 2;
        if (tot > X) return tot;
    }
    *best_tail = bt;
    return tot;
}
/* would sigma(a)=b close a premature cycle? path of sigma starting at b ends at a? */
static int premature(int a, int b) {
    int x = b, n = 1;
    while (sig[x] >= 0) { x = sig[x]; n++; }
    return x == a && n < ngen[gen[a]];
}
static int dfs(void) {
    int tail = -1;
    if (++nodes > node_cap) return -2;
    int l = lb(&tail);
    if (l > X) return 0;
    if (tail < 0) return l <= X;
    int k = tail >> 1, s = tail & 1, g = gen[k];
    int cand[MAXN], cl[MAXN], nc = 0, j;
    for (j = 0; j < N; j++) {
        if (gen[j] != g) continue;
        int a, b;
        if (s == 0) { if (sinv[j] >= 0) continue; a = k; b = j; }
        else { if (sig[j] >= 0) continue; a = j; b = k; }
        if (a == b && ngen[g] > 1) continue;
        if (premature(a, b)) continue;
        sig[a] = b; sinv[b] = a;
        int t2; cl[nc] = lb(&t2); cand[nc] = j; nc++;
        sig[a] = -1; sinv[b] = -1;
    }
    /* order by lower bound (insertion sort) */
    int i2;
    for (i2 = 1; i2 < nc; i2++) {
        int c = cand[i2], v = cl[i2], m = i2;
        while (m > 0 && cl[m - 1] > v) { cand[m] = cand[m - 1]; cl[m] = cl[m - 1]; m--; }
        cand[m] = c; cl[m] = v;
    }
    for (i2 = 0; i2 < nc; i2++) {
        if (cl[i2] > X) break;
        int j2 = cand[i2], a, b;
        if (s == 0) { a = k; b = j2; } else { a = j2; b = k; }
        sig[a] = b; sinv[b] = a;
        int r = dfs();
        sig[a] = -1; sinv[b] = -1;
        if (r != 0) return r;
    }
    return 0;
}
static int par[16];
static int fnd(int v) { while (par[v] != v) v = par[v] = par[par[v]]; return v; }

long thick2g_nodes(void) { return nodes; }

int thick2g(int nrel, const int *lens, const int *letters, long cap, int dgen) {
    int ri, j, pos = 0, g;
    N = 0; for (ri = 0; ri < nrel; ri++) N += lens[ri];
    if (N > MAXN) return -3;
    H = 2 * N;
    memset(ngen, 0, sizeof ngen);
    for (j = 0; j < N; j++) { int a = letters[j]; gen[j] = (a > 0 ? a : -a) - 1; ngen[gen[j]]++; sig[j] = sinv[j] = -1; }
    for (j = 0; j < 16; j++) par[j] = j;
    for (ri = 0; ri < nrel; ri++) {
        int L = lens[ri];
        for (j = 0; j < L; j++) {
            int k1 = pos + j, k2 = pos + (j + 1) % L;
            int a = letters[k1], b = letters[k2];
            if (L > 1 && a == -b) return -1;
            int h1 = 2 * k1 + (a > 0 ? 1 : 0);  /* end(a): x -> i, X -> o */
            int h2 = 2 * k2 + (b > 0 ? 0 : 1);  /* start(b): x -> o, X -> i */
            twin[h1] = h2; twin[h2] = h1;
            par[fnd(2 * gen[k1] + (h1 & 1))] = fnd(2 * gen[k2] + (h2 & 1));
        }
        pos += L;
    }
    int V = 0, c = 0;
    for (g = 0; g < 8; g++) if (ngen[g]) { V += 2; if (fnd(2 * g) == 2 * g) c++; if (fnd(2 * g + 1) == 2 * g + 1) c++; }
    X = 2 * V - 4 * c + 4 * dgen;
    if (X < 0) return 0;
    nodes = 0; node_cap = cap > 0 ? cap : 1L << 40;
    return dfs();
}
