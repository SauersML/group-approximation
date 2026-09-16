/* C port of thicken.dfs(variant="orient"); same half-edge conventions.
   stdin: one presentation per line, relators separated by spaces
   (lowercase = generator, uppercase = inverse).
   stdout: "<0|1> <dfs nodes>" per line.
   Build: gcc -O2 -o thick thick.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAXH 512
#define NG 26
static int H, limit, merges, sp, ngen;
static long nodes;
static int alpha_[MAXH], pstart[MAXH], pend_[MAXH];
static int st_s[4 * MAXH], st_ps[4 * MAXH], st_e[4 * MAXH], st_pe[4 * MAXH], st_m[4 * MAXH];
static int gocc[NG], gbase[NG], gorder[NG];

static inline int hid(int g, int s, int k) { return gbase[g] + s * gocc[g] + k; }
static inline void add(int u, int w) {
    int s = pstart[u], e = pend_[w];
    if (s == w) { st_m[sp++] = 0; return; }
    st_s[sp] = s; st_ps[sp] = pend_[s]; st_e[sp] = e; st_pe[sp] = pstart[e]; st_m[sp] = 1; sp++;
    pend_[s] = e; pstart[e] = s; merges++;
}
static inline void undo(void) {
    sp--;
    if (st_m[sp]) { pend_[st_s[sp]] = st_ps[sp]; pstart[st_e[sp]] = st_pe[sp]; merges--; }
}
static inline void link(int g, int a, int b) {
    add(alpha_[hid(g, 0, a)], hid(g, 0, b));
    add(alpha_[hid(g, 1, b)], hid(g, 1, a));
}
static int gen_step(int gi);
static int extend(int gi, int last, int len, unsigned long long used) {
    int g = gorder[gi], d = gocc[g];
    nodes++;
    if (len == d) {
        int ok = 0;
        link(g, last, 0);
        if (merges <= limit) ok = gen_step(gi + 1);
        undo(); undo();
        return ok;
    }
    for (int k = 1; k < d; k++) {
        if ((used >> k) & 1ULL) continue;
        link(g, last, k);
        if (merges <= limit && extend(gi, k, len + 1, used | (1ULL << k))) { undo(); undo(); return 1; }
        undo(); undo();
    }
    return 0;
}
static int gen_step(int gi) {
    if (gi == ngen) return merges == limit;
    return extend(gi, 0, 1, 1ULL);
}
static int ufp[2 * NG];
static int find(int u) { while (ufp[u] != u) { ufp[u] = ufp[ufp[u]]; u = ufp[u]; } return u; }

int main(void) {
    char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        int occ[NG] = {0}, present[NG] = {0};
        int L = (int)strlen(line);
        for (int i = 0; i < L; i++) if (isalpha((unsigned char)line[i])) { int g = tolower(line[i]) - 'a'; occ[g]++; present[g] = 1; }
        ngen = 0; H = 0;
        int gidx[NG];
        for (int g = 0; g < NG; g++) if (present[g]) { gidx[g] = ngen; gocc[ngen] = occ[g]; gbase[ngen] = H; H += 2 * occ[g]; ngen++; }
        if (H == 0 || H > MAXH) { printf("-1 0\n"); continue; }
        for (int i = 0; i < H; i++) alpha_[i] = -1;
        int cnt[NG] = {0};
        int i = 0;
        while (i < L) {
            while (i < L && !isalpha((unsigned char)line[i])) i++;
            int j = i;
            while (j < L && isalpha((unsigned char)line[j])) j++;
            int n = j - i;
            if (n > 0) {
                int gs[1024], es[1024], ks[1024];
                for (int p = 0; p < n; p++) {
                    char ch = line[i + p]; int g = gidx[tolower(ch) - 'a'];
                    gs[p] = g; es[p] = islower((unsigned char)ch) ? 1 : -1; ks[p] = cnt[g]++;
                }
                for (int p = 0; p < n; p++) {
                    int q = (p + 1) % n;
                    int h1 = hid(gs[p], es[p] == 1 ? 1 : 0, ks[p]);
                    int h2 = hid(gs[q], es[q] == 1 ? 0 : 1, ks[q]);
                    alpha_[h1] = h2; alpha_[h2] = h1;
                }
            }
            i = j;
        }
        for (int v = 0; v < 2 * ngen; v++) ufp[v] = v;
        for (int h = 0; h < H; h++) {
            int g1 = 0, g2 = 0;
            for (int g = 0; g < ngen; g++) { if (h >= gbase[g] && h < gbase[g] + 2 * gocc[g]) g1 = g; if (alpha_[h] >= gbase[g] && alpha_[h] < gbase[g] + 2 * gocc[g]) g2 = g; }
            int v1 = 2 * g1 + (h - gbase[g1]) / gocc[g1], v2 = 2 * g2 + (alpha_[h] - gbase[g2]) / gocc[g2];
            int a = find(v1), b = find(v2);
            if (a != b) ufp[a] = b;
        }
        int c = 0;
        for (int v = 0; v < 2 * ngen; v++) if (find(v) == v) c++;
        int E = H / 2, V = 2 * ngen, Ft = E - V + 2 * c;
        limit = H - Ft;
        /* generators sorted by occurrence count, ties by index (as in thicken.py) */
        for (int g = 0; g < ngen; g++) gorder[g] = g;
        for (int a = 1; a < ngen; a++) { /* stable insertion sort, like Python sorted() */
            int t = gorder[a], b = a - 1;
            while (b >= 0 && gocc[gorder[b]] > gocc[t]) { gorder[b + 1] = gorder[b]; b--; }
            gorder[b + 1] = t;
        }
        for (int h = 0; h < H; h++) { pstart[h] = h; pend_[h] = h; }
        merges = 0; sp = 0; nodes = 0;
        int ok = gen_step(0);
        printf("%d %ld\n", ok, nodes);
        fflush(stdout);
    }
    return 0;
}
