/* Simulated-annealing hunt for a k-seed witness (all seed types allowed).
 * Cost(T) = #classes(cl(T)) - #classes(cl(T) v ker m), the number of merges
 * still missing; cost 0 iff cl(T) contains ker(m).  With k = law - 1 a cost-0
 * set is an exact certified counterexample deep_j < law_j to (O); with
 * k = law the run calibrates the search (lawful witnesses exist).
 *
 * Usage: ./anneal inst.txt k restarts iters seed [T0]
 * Input: the format of ../fpbs-overfold-exact-c-2026-09-17/export.py.
 * Prints per restart the best cost, and the witness if cost 0 is reached,
 * with the number of overfold seeds in it.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define MAXV 1024
static int V, n, S;
static int nb[MAXV][4], mm[MAXV], firstm[MAXV];
static int su[8192], sv[8192], slaw[8192];
static int par[MAXV], sz[MAXV], adj[MAXV][4];
static int stk[1 << 18][2];
static int kp[MAXV][2], NK;

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int find(int x) {
    while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; }
    return x;
}
static void unite_fold(int top) {
    while (top > 0) {
        top--;
        int x = find(stk[top][0]), y = find(stk[top][1]);
        if (x == y) continue;
        if (sz[x] < sz[y]) { int t = x; x = y; y = t; }
        par[y] = x; sz[x] += sz[y];
        for (int d = 0; d < 4; d++) if (adj[y][d] >= 0) {
            if (adj[x][d] < 0) adj[x][d] = adj[y][d];
            else { stk[top][0] = adj[x][d]; stk[top][1] = adj[y][d]; top++; }
        }
    }
}
static int nclasses(void) {
    int c = 0;
    for (int v = 0; v < V; v++) if (find(v) == v) c++;
    return c;
}
/* cost of a seed set */
static int cost(const int *T, int k) {
    int top = 0;
    for (int v = 0; v < V; v++) { par[v] = v; sz[v] = 1; for (int d = 0; d < 4; d++) adj[v][d] = nb[v][d]; }
    for (int i = 0; i < k; i++) { stk[top][0] = su[T[i]]; stk[top][1] = sv[T[i]]; top++; }
    unite_fold(top);
    int c1 = nclasses();
    top = 0;
    for (int i = 0; i < NK; i++) { stk[top][0] = kp[i][0]; stk[top][1] = kp[i][1]; top++; }
    unite_fold(top);
    return c1 - nclasses();
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    int k = atoi(argv[2]), R = atoi(argv[3]);
    long iters = atol(argv[4]);
    rs = 88172645463325252ULL ^ (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
    double T0 = argc > 6 ? atof(argv[6]) : 1.0;
    if (!f || fscanf(f, "%d %d", &V, &n) != 2) return 1;
    for (int v = 0; v < V; v++) for (int d = 0; d < 4; d++) if (fscanf(f, "%d", &nb[v][d]) != 1) return 1;
    for (int v = 0; v < V; v++) if (fscanf(f, "%d", &mm[v]) != 1) return 1;
    int over; for (int v = 0; v < V; v++) if (fscanf(f, "%d", &over) != 1) return 1;
    if (fscanf(f, "%d", &S) != 1) return 1;
    for (int i = 0; i < S; i++) if (fscanf(f, "%d %d %d", &su[i], &sv[i], &slaw[i]) != 3) return 1;
    for (int i = 0; i < MAXV; i++) firstm[i] = -1;
    NK = 0;
    for (int v = 0; v < V; v++) {
        if (firstm[mm[v]] < 0) firstm[mm[v]] = v;
        else { kp[NK][0] = firstm[mm[v]]; kp[NK][1] = v; NK++; }
    }
    int base = cost(NULL, 0);
    printf("V %d n %d seeds %d k %d base-cost %d\n", V, n, S, k, base);
    int T[64], best[64];
    int hits = 0;
    for (int r = 0; r < R; r++) {
        for (int i = 0; i < k; i++) T[i] = rnd() % S;
        int c = cost(T, k), bc = c;
        memcpy(best, T, sizeof(int) * k);
        for (long it = 0; it < iters && bc > 0; it++) {
            double temp = T0 * (1.0 - (double)it / iters) + 1e-3;
            int i = rnd() % k, old = T[i];
            T[i] = rnd() % S;
            int c2 = cost(T, k);
            if (c2 <= c || urand() < exp((c - c2) / temp)) {
                c = c2;
                if (c < bc) { bc = c; memcpy(best, T, sizeof(int) * k); }
            } else T[i] = old;
        }
        if (bc == 0) {
            hits++;
            int ov = 0; for (int i = 0; i < k; i++) ov += !slaw[best[i]];
            printf("restart %d WITNESS k %d overfold %d:", r, k, ov);
            for (int i = 0; i < k; i++) printf(" %d(%d,%d,%d)", best[i], su[best[i]], sv[best[i]], slaw[best[i]]);
            printf("\n");
        } else printf("restart %d best cost %d\n", r, bc);
        fflush(stdout);
    }
    printf("hits %d / %d\n", hits, R);
    return 0;
}
