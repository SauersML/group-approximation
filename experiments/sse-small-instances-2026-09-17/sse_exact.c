/* Exact max over |S| = s, 0 in S, of  P(S) = sum_{unordered u != v in S} w[u ^ v]
 * for a weighted Cayley graph on F_2^k (k <= 9, s <= 63).  Branch and bound, exact integer arithmetic.
 * stay(S) = 2 P(S) / (W s).
 * Input on stdin:  k s lower_bound  then 2^k weights w[0..N-1] (w[0] ignored).
 * Output: best P and witness vertices, then the node count.
 * Prunes only when bound < best+1 with best initialised to lower_bound-1, so the result is exact
 * provided lower_bound <= true optimum (pass 0 if unsure).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static int k, N, s;
static ll w[512], topw[512]; /* topw[r] = sum of r largest weights over nonzero a */
static int S[64], bestS[64];
static ll best;
static ll gain[64][512]; /* gain[t][v] = sum_{u in S[0..t-1]} w[u^v] */
static long long nodes = 0;

static int cmpd(const void *a, const void *b) { ll x = *(ll*)a, y = *(ll*)b; return (x < y) - (x > y); }

static void dfs(int t, int last, ll cur) {
    nodes++;
    if (t == s) {
        if (cur > best) { best = cur; memcpy(bestS, S, sizeof(int) * s); }
        return;
    }
    int r = s - t;
    int ncand = N - 1 - last;
    if (ncand < r) return;
    /* bound: top r gains among candidates + r*topw[r-1]/2 */
    static ll buf[8][512];
    ll *g = buf[t < 8 ? t : 7];
    int c = 0;
    for (int v = last + 1; v < N; v++) g[c++] = gain[t][v];
    ll bound = cur;
    if (r <= 3 || t >= 7) {
        /* partial selection of top r */
        for (int i = 0; i < r; i++) {
            int bi = i;
            for (int j = i + 1; j < c; j++) if (g[j] > g[bi]) bi = j;
            ll tmp = g[i]; g[i] = g[bi]; g[bi] = tmp;
            bound += g[i];
        }
    } else {
        qsort(g, c, sizeof(ll), cmpd);
        for (int i = 0; i < r; i++) bound += g[i];
    }
    bound += (r * topw[r - 1]) / 2;
    if (bound <= best) return;
    for (int v = last + 1; v < N; v++) {
        if (N - v < r) break;
        S[t] = v;
        ll nc = cur + gain[t][v];
        for (int x = 0; x < N; x++) gain[t + 1][x] = gain[t][x] + w[x ^ v];
        dfs(t + 1, v, nc);
    }
}

int main(void) {
    ll lb;
    if (scanf("%d %d %lld", &k, &s, &lb) != 3) return 1;
    N = 1 << k;
    for (int i = 0; i < N; i++) if (scanf("%lld", &w[i]) != 1) return 1;
    w[0] = 0;
    ll sorted[512];
    memcpy(sorted, w + 1, sizeof(ll) * (N - 1));
    qsort(sorted, N - 1, sizeof(ll), cmpd);
    topw[0] = 0;
    for (int r = 1; r < N; r++) topw[r] = topw[r - 1] + sorted[r - 1];
    for (int r = N; r < 512; r++) topw[r] = topw[N - 1];
    best = lb - 1;
    S[0] = 0;
    for (int x = 0; x < N; x++) gain[1][x] = w[x];
    if (s == 1) { printf("0\n0\n0\n"); return 0; }
    dfs(1, 0, 0);
    printf("%lld\n", best);
    for (int i = 0; i < s; i++) printf("%d ", bestS[i]);
    printf("\n%lld\n", nodes);
    return 0;
}
