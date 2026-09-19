/* Dinic max flow with int64 capacities on an undirected graph.
 * mincut(n, m, u, v, c, s, t, side): edge i joins u[i], v[i] with capacity c[i]
 * in both directions.  Returns the max flow value; side[x] = 1 iff x is reachable
 * from s in the final residual graph (the source side of a minimum cut).
 * Build: gcc -O2 -shared -fPIC -o hadk_flow.so hadk_flow.c
 */
#include <stdlib.h>
#include <string.h>
typedef long long ll;

static int *head, *nxt, *to, *level, *it, *q;
static ll *cap;

static int bfs(int n, int s, int t) {
    for (int i = 0; i < n; i++) level[i] = -1;
    int qh = 0, qt = 0;
    q[qt++] = s; level[s] = 0;
    while (qh < qt) {
        int x = q[qh++];
        for (int e = head[x]; e >= 0; e = nxt[e])
            if (cap[e] > 0 && level[to[e]] < 0) { level[to[e]] = level[x] + 1; q[qt++] = to[e]; }
    }
    return level[t] >= 0;
}

static ll dfs(int x, int t, ll f) {
    if (x == t) return f;
    for (int *pe = &it[x]; *pe >= 0; *pe = nxt[*pe]) {
        int e = *pe, y = to[e];
        if (cap[e] > 0 && level[y] == level[x] + 1) {
            ll d = dfs(y, t, f < cap[e] ? f : cap[e]);
            if (d > 0) { cap[e] -= d; cap[e ^ 1] += d; return d; }
        }
    }
    return 0;
}

ll mincut(int n, int m, const int *u, const int *v, const ll *c, int s, int t, unsigned char *side) {
    head = malloc(sizeof(int) * n); level = malloc(sizeof(int) * n);
    it = malloc(sizeof(int) * n); q = malloc(sizeof(int) * n);
    nxt = malloc(sizeof(int) * 2 * m); to = malloc(sizeof(int) * 2 * m);
    cap = malloc(sizeof(ll) * 2 * m);
    for (int i = 0; i < n; i++) head[i] = -1;
    for (int i = 0; i < m; i++) {
        int e = 2 * i;
        to[e] = v[i]; cap[e] = c[i]; nxt[e] = head[u[i]]; head[u[i]] = e;
        to[e + 1] = u[i]; cap[e + 1] = c[i]; nxt[e + 1] = head[v[i]]; head[v[i]] = e + 1;
    }
    ll flow = 0;
    const ll INF = (ll)1 << 62;
    while (bfs(n, s, t)) {
        memcpy(it, head, sizeof(int) * n);
        ll f;
        while ((f = dfs(s, t, INF)) > 0) flow += f;
    }
    bfs(n, s, t);
    for (int i = 0; i < n; i++) side[i] = level[i] >= 0;
    free(head); free(level); free(it); free(q); free(nxt); free(to); free(cap);
    return flow;
}
