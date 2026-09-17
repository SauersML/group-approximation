/* Low-index subgroups (Sims) for a 2-generator finitely presented group.
 * Same algorithm as lowindex.py, in C for speed.
 * stdin: nmax nrels, then each relator: len l_1 ... l_len  (letters 0=a 1=A 2=b 3=B)
 * stdout: one line per transitive rep up to isomorphism: k a[0..k-1] b[0..k-1]
 * Build: gcc -O2 -o lowindex lowindex.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define G 4
#define MAXN 64
#define MAXROT 4096
#define MAXL 128

static int nmax;
static int T[G][MAXN];
static int rotlen[G][MAXROT];
static int rot[G][MAXROT][MAXL];
static int nrot[G];
static int trail_g[1 << 20], trail_c[1 << 20];
static long trail_n = 0;
static int q_c[1 << 20], q_g[1 << 20];
static long found = 0;
static long nodes = 0;

static inline int inv(int x) { return x ^ 1; }

static inline void define(int c, int g, int d, int *qn) {
    T[g][c] = d;
    T[inv(g)][d] = c;
    trail_g[trail_n] = g; trail_c[trail_n] = c; trail_n++;
    trail_g[trail_n] = inv(g); trail_c[trail_n] = d; trail_n++;
    q_c[*qn] = c; q_g[*qn] = g; (*qn)++;
    q_c[*qn] = d; q_g[*qn] = inv(g); (*qn)++;
}

static void undo(long mark) {
    while (trail_n > mark) {
        trail_n--;
        T[trail_g[trail_n]][trail_c[trail_n]] = -1;
    }
}

static int scan(int c, const int *w, int L, int *qn) {
    int f = c, i = 0;
    while (i < L) {
        int nx = T[w[i]][f];
        if (nx < 0) break;
        f = nx; i++;
    }
    if (i == L) return f == c;
    int b = c, j = L - 1;
    while (j >= i) {
        int nx = T[inv(w[j])][b];
        if (nx < 0) break;
        b = nx; j--;
    }
    if (j < i) return b == f;
    if (j == i) define(f, w[i], b, qn);
    return 1;
}

static int process(int qn) {
    while (qn > 0) {
        qn--;
        int c = q_c[qn], g = q_g[qn];
        for (int r = 0; r < nrot[g]; r++) {
            if (!scan(c, rot[g][r], rotlen[g][r], &qn)) return 0;
        }
    }
    return 1;
}

static int canonical(int k) {
    int perm[MAXN], order[MAXN];
    for (int base = 1; base < k; base++) {
        for (int i = 0; i < k; i++) perm[i] = -1;
        perm[base] = 0; order[0] = base;
        int len = 1, decided = 0;
        for (int i = 0; i < len && !decided; i++) {
            int old = order[i];
            for (int g = 0; g < G; g++) {
                int x = T[g][i], yo = T[g][old];
                if (x < 0 || yo < 0) { decided = 1; break; }
                if (perm[yo] < 0) { perm[yo] = len; order[len++] = yo; }
                int y = perm[yo];
                if (y < x) return 0;
                if (y > x) { decided = 1; break; }
            }
        }
    }
    return 1;
}

static void search(int k) {
    nodes++;
    int c0 = -1, g0 = -1;
    for (int c = 0; c < k && c0 < 0; c++)
        for (int g = 0; g < G; g++)
            if (T[g][c] < 0) { c0 = c; g0 = g; break; }
    if (c0 < 0) {
        found++;
        printf("%d", k);
        for (int i = 0; i < k; i++) printf(" %d", T[0][i]);
        for (int i = 0; i < k; i++) printf(" %d", T[2][i]);
        printf("\n");
        fflush(stdout);
        return;
    }
    int ig = inv(g0);
    for (int d = 0; d <= k; d++) {
        if (d == k && k >= nmax) break;
        if (d < k && T[ig][d] >= 0) continue;
        long mark = trail_n;
        int qn = 0;
        define(c0, g0, d, &qn);
        int k2 = (d == k) ? k + 1 : k;
        if (process(qn) && canonical(k2)) search(k2);
        undo(mark);
    }
}

int main(void) {
    int nrels;
    if (scanf("%d %d", &nmax, &nrels) != 2) return 1;
    for (int g = 0; g < G; g++) nrot[g] = 0;
    for (int r = 0; r < nrels; r++) {
        int L, w[MAXL], u[MAXL];
        if (scanf("%d", &L) != 1) return 1;
        for (int i = 0; i < L; i++) scanf("%d", &w[i]);
        for (int pass = 0; pass < 2; pass++) {
            if (pass == 0) memcpy(u, w, sizeof(int) * L);
            else for (int i = 0; i < L; i++) u[i] = inv(w[L - 1 - i]);
            for (int s = 0; s < L; s++) {
                int g = u[s];
                int *dst = rot[g][nrot[g]];
                for (int i = 0; i < L; i++) dst[i] = u[(s + i) % L];
                /* dedupe */
                int dup = 0;
                for (int e = 0; e < nrot[g] && !dup; e++)
                    if (rotlen[g][e] == L && memcmp(rot[g][e], dst, sizeof(int) * L) == 0) dup = 1;
                if (!dup) { rotlen[g][nrot[g]] = L; nrot[g]++; }
            }
        }
    }
    for (int g = 0; g < G; g++) for (int i = 0; i < MAXN; i++) T[g][i] = -1;
    search(1);
    fprintf(stderr, "found %ld reps, %ld nodes\n", found, nodes);
    return 0;
}
