/* Overfold cascade versus lawful percolation on large random levels.
 *
 * Model: Gamma_{j+1}(Q) = Q x_R C_{j+1} (pullback form, proved in the node
 * fpbs-mal-overfold-merges-never-help), m = id x iota onto Gamma_j(Q).
 * A seed is (q, type): the root pair (c, d) of an off-diagonal pair-graph
 * component, placed over q.  Lawful iff iota c == iota d.
 *
 * D(E) = sum over nontrivial fibres of m of (#classes of E in the fibre - 1).
 * cl(P) contains ker(m) iff D(cl(P)) == 0.
 *
 * Usage: cascade MODEL n qseed mode cls [cand] [runs]
 *   mode rand  : add seeds of class cls in uniform random order; print the
 *                number of seeds at which D first hits 0 (exact, by
 *                bisection over the checkpoints) and the D trajectory.
 *   mode greedy: at each step sample cand seeds of class cls, keep the one
 *                with least D after closure; print the count at D == 0.
 *   cls: law | over | all | lev0 (level-0 overfold only)
 * Q: two uniform random permutations of {0..n-1} (qseed).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int Vc, Vb, T;
static int cnb[1024][4];
static int io[1024];
static int tc[8192], td[8192], tlaw[8192], tsz[8192], tlev[8192];

static int n, V;
static int *nb;           /* V x 4 */
static int *par, *adj;    /* union find, adjacency of roots (V x 4) */
static int *mfib;         /* m(v) */
static int *stk;
static long stkcap;

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int find(int x) { while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; } return x; }

static void push(long *sp, int a, int b) {
    if (*sp + 2 > stkcap) { stkcap *= 2; stk = realloc(stk, stkcap * sizeof(int)); }
    stk[(*sp)++] = a; stk[(*sp)++] = b;
}

static void merge(int x0, int y0) {
    long sp = 0;
    push(&sp, x0, y0);
    while (sp) {
        int y = stk[--sp], x = stk[--sp];
        x = find(x); y = find(y);
        if (x == y) continue;
        par[y] = x;
        for (int i = 0; i < 4; i++) {
            int ay = adj[4 * y + i];
            if (ay >= 0) {
                int ax = adj[4 * x + i];
                if (ax >= 0) push(&sp, ax, ay); else adj[4 * x + i] = ay;
            }
        }
    }
}

static void reset(void) {
    for (int v = 0; v < V; v++) { par[v] = v; memcpy(adj + 4 * v, nb + 4 * v, 4 * sizeof(int)); }
}

/* D: count distinct (fibre, root) pairs among vertices; D = V - #distinct
 * (every fibre of m is nontrivial or a singleton; singletons contribute 0). */
static int *mark; static int stamp = 0;
static long computeD(void) {
    /* classes within a fibre: a vertex v is a "first" of its class in its
     * fibre iff no earlier vertex of the fibre has the same root.  Fibre of
     * (q, iota c) = vertices q*Vc + c' with iota c' = iota c. */
    long D = 0;
    for (int q = 0; q < n; q++) {
        for (int b = 0; b < Vb; b++) {
            int cnt = 0, distinct = 0;
            stamp++;
            for (int c = 0; c < Vc; c++) if (io[c] == b) {
                int r = find(q * Vc + c);
                cnt++;
                if (mark[r] != stamp) { mark[r] = stamp; distinct++; }
            }
            if (cnt) D += distinct - 1;
        }
    }
    return D;
}

static int inclass(int t, const char *cls) {
    if (!strcmp(cls, "all")) return 1;
    if (!strcmp(cls, "law")) return tlaw[t];
    if (!strcmp(cls, "over")) return !tlaw[t];
    if (!strcmp(cls, "lev0")) return !tlaw[t] && tlev[t] == 0;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d %d %d", &Vc, &Vb, &T) != 3) return 1;
    for (int c = 0; c < Vc; c++) for (int i = 0; i < 4; i++) if (fscanf(f, "%d", &cnb[c][i]) != 1) return 1;
    for (int c = 0; c < Vc; c++) if (fscanf(f, "%d", &io[c]) != 1) return 1;
    for (int t = 0; t < T; t++) if (fscanf(f, "%d %d %d %d %d", &tc[t], &td[t], &tlaw[t], &tsz[t], &tlev[t]) != 5) return 1;
    fclose(f);
    n = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    const char *mode = argv[4], *cls = argv[5];
    int cand = argc > 6 ? atoi(argv[6]) : 200;
    int runs = argc > 7 ? atoi(argv[7]) : 1;
    V = n * Vc;
    int *PA = malloc(n * sizeof(int)), *PB = malloc(n * sizeof(int));
    int *IA = malloc(n * sizeof(int)), *IB = malloc(n * sizeof(int));
    for (int i = 0; i < n; i++) PA[i] = PB[i] = i;
    for (int i = n - 1; i > 0; i--) { int k = rnd() % (i + 1), x = PA[i]; PA[i] = PA[k]; PA[k] = x; }
    for (int i = n - 1; i > 0; i--) { int k = rnd() % (i + 1), x = PB[i]; PB[i] = PB[k]; PB[k] = x; }
    for (int i = 0; i < n; i++) { IA[PA[i]] = i; IB[PB[i]] = i; }
    int *act[4] = {PA, IA, PB, IB};
    nb = malloc(4L * V * sizeof(int)); par = malloc(V * sizeof(int)); adj = malloc(4L * V * sizeof(int));
    mark = calloc(V, sizeof(int));
    stkcap = 1 << 16; stk = malloc(stkcap * sizeof(int));
    for (int q = 0; q < n; q++) for (int c = 0; c < Vc; c++) for (int i = 0; i < 4; i++) {
        int d = cnb[c][i];
        nb[4 * (q * Vc + c) + i] = d >= 0 ? act[i][q] * Vc + d : -1;
    }
    /* candidate seeds */
    int ns = 0;
    int *sq = malloc((long)n * T * sizeof(int)), *st = malloc((long)n * T * sizeof(int));
    for (int q = 0; q < n; q++) for (int t = 0; t < T; t++) if (inclass(t, cls)) { sq[ns] = q; st[ns] = t; ns++; }
    reset();
    long D0 = computeD();
    printf("# n=%d Vc=%d Vb=%d V=%d classes=%s seeds_in_class=%d D0=%ld\n", n, Vc, Vb, V, cls, ns, D0);
    if (!strcmp(mode, "rand")) {
        int *perm = malloc(ns * sizeof(int));
        for (int r = 0; r < runs; r++) {
            for (int i = 0; i < ns; i++) perm[i] = i;
            for (int i = ns - 1; i > 0; i--) { int k = rnd() % (i + 1), x = perm[i]; perm[i] = perm[k]; perm[k] = x; }
            reset();
            int step = n / 100; if (step < 1) step = 1;
            int k = 0; long D = D0;
            printf("traj");
            while (D > 0 && k < ns) {
                int kk = k + step; if (kk > ns) kk = ns;
                for (; k < kk; k++) { int s = perm[k]; merge(sq[s] * Vc + tc[st[s]], sq[s] * Vc + td[st[s]]); }
                D = computeD();
                if ((k / step) % 5 == 0) printf(" %.3f:%.4f", (double)k / n, (double)D / D0);
            }
            /* bisect the last block for the exact hitting count */
            int lo = k - step < 0 ? 0 : k - step, hi = k;
            while (hi - lo > 1) {
                int mid = (lo + hi) / 2;
                reset();
                for (int i = 0; i < mid; i++) { int s = perm[i]; merge(sq[s] * Vc + tc[st[s]], sq[s] * Vc + td[st[s]]); }
                if (computeD() == 0) hi = mid; else lo = mid;
            }
            printf("\nrun %d hit %d density %.4f\n", r, hi, (double)hi / n);
        }
    } else {
        /* greedy */
        int *spar = malloc(V * sizeof(int)), *sadj = malloc(4L * V * sizeof(int));
        reset();
        long D = D0; int k = 0; int nover = 0;
        while (D > 0) {
            memcpy(spar, par, V * sizeof(int)); memcpy(sadj, adj, 4L * V * sizeof(int));
            long best = D + 1; int bs = -1;
            for (int c = 0; c < cand; c++) {
                int s = rnd() % ns;
                merge(sq[s] * Vc + tc[st[s]], sq[s] * Vc + td[st[s]]);
                long Dn = computeD();
                if (Dn < best) { best = Dn; bs = s; }
                memcpy(par, spar, V * sizeof(int)); memcpy(adj, sadj, 4L * V * sizeof(int));
            }
            merge(sq[bs] * Vc + tc[st[bs]], sq[bs] * Vc + td[st[bs]]);
            D = best; k++; if (!tlaw[st[bs]]) nover++;
        }
        printf("greedy seeds %d density %.4f overfold_used %d\n", k, (double)k / n, nover);
    }
    return 0;
}
