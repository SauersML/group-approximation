/* Exhaustive census of the two-generator Titz--Witzel gate (TW2G2) on n points.
 *
 * Up to simultaneous conjugation, e is the involution (0 1)(2 3)...(2k-2 2k-1) with k
 * transpositions; u runs over all of Sym(n) (Heap's algorithm).  For every pair with
 * mark M = |supp u^8| > 0 we record the relator defect D = sum_r |supp r(e,u)| over the
 * four approximate relators of relators.h (counts, not normalised), and report
 *   minD      = min D over pairs with M > 0,
 *   ratio     = min D/M over pairs with M > 0 (as a fraction),
 *   minD_q    = min D over pairs with 4M >= n (mark at least 1/4).
 * Words act on the right, as in gate_anneal.c.  Early abort: a pair is abandoned once its
 * partial defect already exceeds all three running minima.
 *
 * Usage: gate_exhaust n k      (k = number of transpositions of e)
 */
#include <stdio.h>
#include <stdlib.h>
#include "relators.h"

static int n, E[16], U[16], Ui[16];

static inline int ap(int x, int l) { return l == 1 ? E[x] : (l == 2 ? U[x] : Ui[x]); }

static int supp(const int *w, int len) {
    int c = 0;
    for (int x = 0; x < n; x++) {
        int y = x;
        for (int j = 0; j < len; j++) y = ap(y, w[j]);
        c += (y != x);
    }
    return c;
}

static long long cnt;
static int minD = 1 << 30, minDq = 1 << 30, rN = 1 << 30, rM = 1;  /* ratio rN/rM */
static int wE[16], wU[16], wEq[16], wUq[16], wEr[16], wUr[16];

static void visit(void) {
    for (int i = 0; i < n; i++) Ui[U[i]] = i;
    int M = 0;
    for (int x = 0; x < n; x++) {
        int y = x;
        for (int j = 0; j < 8; j++) y = U[y];
        M += (y != x);
    }
    if (M == 0) return;
    cnt++;
    /* abort threshold: largest D that could still improve something */
    int thr = minD;
    if (4 * M >= n && minDq > thr) thr = minDq;
    long long rthr = ((long long)rN * M + rM - 1) / rM;   /* D < rN/rM * M improves ratio */
    if (rthr > thr) thr = rthr > (1 << 30) ? (1 << 30) : (int)rthr;
    int D = 0;
    for (int r = 0; r < NREL; r++) {
        D += supp(REL[r], RLEN[r]);
        if (D > thr) return;
    }
    if (D < minD) { minD = D; for (int i = 0; i < n; i++) { wE[i] = E[i]; wU[i] = U[i]; } }
    if (4 * M >= n && D < minDq) { minDq = D; for (int i = 0; i < n; i++) { wEq[i] = E[i]; wUq[i] = U[i]; } }
    if ((long long)D * rM < (long long)rN * M) { rN = D; rM = M; for (int i = 0; i < n; i++) { wEr[i] = E[i]; wUr[i] = U[i]; } }
}

static void pr(const char *tag, const int *e, const int *u) {
    printf("%s e=", tag);
    for (int i = 0; i < n; i++) printf("%d%s", e[i], i + 1 < n ? "," : "");
    printf(" u=");
    for (int i = 0; i < n; i++) printf("%d%s", u[i], i + 1 < n ? "," : "");
    printf("\n");
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: gate_exhaust n k\n"); return 1; }
    n = atoi(argv[1]); int k = atoi(argv[2]);
    if (n > 16 || 2 * k > n) return 1;
    for (int i = 0; i < n; i++) E[i] = i;
    for (int t = 0; t < k; t++) { E[2 * t] = 2 * t + 1; E[2 * t + 1] = 2 * t; }
    int c[16] = {0};
    for (int i = 0; i < n; i++) U[i] = i;
    visit();
    int i = 1;
    while (i < n) {                      /* Heap's algorithm */
        if (c[i] < i) {
            int j = (i % 2 == 0) ? 0 : c[i];
            int t = U[j]; U[j] = U[i]; U[i] = t;
            visit();
            c[i]++; i = 1;
        } else { c[i] = 0; i++; }
    }
    printf("n=%d k=%d markedpairs=%lld minD=%d ratio=%d/%d minD_quarter=%d\n",
           n, k, cnt, minD == 1 << 30 ? -1 : minD, rN == 1 << 30 ? -1 : rN, rM,
           minDq == 1 << 30 ? -1 : minDq);
    if (minD < (1 << 30)) pr("argminD", wE, wU);
    if (rN < (1 << 30)) pr("argratio", wEr, wUr);
    if (minDq < (1 << 30)) pr("argquarter", wEq, wUq);
    return 0;
}
