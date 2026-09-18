// Exact isoperimetric profile of balls in Thompson's group F, generators {x0, x1}.
//
// For each radius r <= R this program computes
//     h_r = min { |dS| / |S| : S nonempty, S subset of B_r }
// where dS is the set of directed edges (g, g s), g in S, s in {x0^{+-1}, x1^{+-1}}, g s not in S
// (edges leaving the ball count as boundary). Density delta(S) = 4 - |dS|/|S| is the average
// induced degree. Every finite set of word-diameter <= r has a translate inside B_r, so
// 4 - h_r is the maximal density of ANY finite set of diameter <= r.
//
// Method: Dinkelbach iteration. For lambda = p/q, min over S of  q|dS| - p|S|  is a minimum
// s-t cut: source -> g capacity p, g -> sink capacity q * (#darts from g leaving the ball),
// g <-> g s capacity q in both directions. C(lambda) = p|B| + min_S (q|dS| - p|S|).
// If the min cut is < p|B| the source side S has ratio < lambda; iterate lambda <- |dS|/|S|.
// When the min cut equals p|B| no set beats lambda. Exact integer arithmetic throughout.
//
// Elements are PL homeomorphisms of [0,1], breakpoints scaled by 2^62, all divisions checked.
// Right multiplication g s = g o s (apply s first); the right Cayley graph {g, g s} is
// isomorphic to the left one via g -> g^-1.
//
// Usage: ball_density R [outprefix]
#include <bits/stdc++.h>
using namespace std;
typedef uint64_t u64; typedef __int128 i128;
static const int K = 62; static const u64 ONE = (u64)1 << K;
struct PL { vector<u64> xs, ys; };

static u64 ev(const vector<u64>& xs, const vector<u64>& ys, u64 x) {
    size_t i = upper_bound(xs.begin(), xs.end(), x) - xs.begin();
    if (i == 0) { fprintf(stderr, "ev below 0\n"); exit(2); }
    i--;
    if (i >= xs.size() - 1) { if (x != ONE) { fprintf(stderr, "ev above 1\n"); exit(2); } return ONE; }
    i128 num = (i128)(x - xs[i]) * (i128)(ys[i + 1] - ys[i]);
    i128 den = xs[i + 1] - xs[i];
    if (num % den) { fprintf(stderr, "dyadic depth exceeds K\n"); exit(2); }
    return ys[i] + (u64)(num / den);
}
static PL canon(const vector<u64>& X, const vector<u64>& Y) {
    PL o; o.xs.push_back(X[0]); o.ys.push_back(Y[0]);
    for (size_t i = 1; i + 1 < X.size(); i++) {
        i128 a = (i128)(Y[i] - o.ys.back()) * (i128)(X[i + 1] - X[i]);
        i128 b = (i128)(Y[i + 1] - Y[i]) * (i128)(X[i] - o.xs.back());
        if (a != b) { o.xs.push_back(X[i]); o.ys.push_back(Y[i]); }
    }
    o.xs.push_back(X.back()); o.ys.push_back(Y.back());
    return o;
}
// g s = g o s (apply s first), the convention of experiments/thompson-f/cogrowth_exact.py
static PL mul(const PL& g, const PL& s) {
    vector<u64> cand(s.xs);
    for (u64 x : g.xs) cand.push_back(ev(s.ys, s.xs, x));
    sort(cand.begin(), cand.end()); cand.erase(unique(cand.begin(), cand.end()), cand.end());
    vector<u64> Y(cand.size());
    for (size_t i = 0; i < cand.size(); i++) Y[i] = ev(g.xs, g.ys, ev(s.xs, s.ys, cand[i]));
    return canon(cand, Y);
}
static PL make(vector<pair<pair<u64,u64>, pair<u64,u64>>> pts) {
    vector<u64> X, Y;
    for (auto& p : pts) { X.push_back(ONE / p.first.second * p.first.first); Y.push_back(ONE / p.second.second * p.second.first); }
    return canon(X, Y);
}
static PL inv(const PL& f) { PL o; o.xs = f.ys; o.ys = f.xs; return o; }
static bool eq(const PL& a, const PL& b) { return a.xs == b.xs && a.ys == b.ys; }
struct KeyHash { size_t operator()(const vector<u64>& v) const { u64 h = 1469598103934665603ULL; for (u64 x : v) { h ^= x + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2); } return h; } };
static vector<u64> key(const PL& f) { vector<u64> k(f.xs); k.insert(k.end(), f.ys.begin(), f.ys.end()); return k; }

// ---------------- Dinic max flow ----------------
struct Flow {
    int N; vector<int> head, nxt, to; vector<long long> cap;
    Flow(int n) : N(n), head(n, -1) {}
    void reserve(size_t m) { nxt.reserve(m); to.reserve(m); cap.reserve(m); }
    void add(int u, int v, long long c, long long rc) {
        to.push_back(v); cap.push_back(c); nxt.push_back(head[u]); head[u] = (int)to.size() - 1;
        to.push_back(u); cap.push_back(rc); nxt.push_back(head[v]); head[v] = (int)to.size() - 1;
    }
    vector<int> level, it;
    bool bfs(int s, int t) {
        level.assign(N, -1); vector<int> q; q.reserve(N); q.push_back(s); level[s] = 0;
        for (size_t i = 0; i < q.size(); i++) { int u = q[i]; for (int e = head[u]; e != -1; e = nxt[e]) if (cap[e] > 0 && level[to[e]] < 0) { level[to[e]] = level[u] + 1; q.push_back(to[e]); } }
        return level[t] >= 0;
    }
    long long dfs(int s, int t) {  // blocking flow, augmenting paths found by iterative DFS
        long long total = 0; vector<int> path; path.reserve(N);
        while (true) {
            int u = s; path.clear();
            while (u != t) {
                int& e = it[u];
                while (e != -1 && !(cap[e] > 0 && level[to[e]] == level[u] + 1)) e = nxt[e];
                if (e == -1) { if (u == s) return total; level[u] = -1; u = to[path.back() ^ 1]; path.pop_back(); continue; }
                path.push_back(e); u = to[e];
            }
            long long f = LLONG_MAX; for (int e : path) f = min(f, cap[e]);
            for (int e : path) { cap[e] -= f; cap[e ^ 1] += f; }
            total += f;
        }
    }
    long long maxflow(int s, int t) { long long f = 0; while (bfs(s, t)) { it = head; f += dfs(s, t); } return f; }
    vector<char> sourceSide(int s) {
        vector<char> vis(N, 0); vector<int> q{ s }; vis[s] = 1;
        for (size_t i = 0; i < q.size(); i++) { int u = q[i]; for (int e = head[u]; e != -1; e = nxt[e]) if (cap[e] > 0 && !vis[to[e]]) { vis[to[e]] = 1; q.push_back(to[e]); } }
        return vis;
    }
};

int main(int argc, char** argv) {
    int R = argc > 1 ? atoi(argv[1]) : 8;
    string outp = argc > 2 ? argv[2] : "";
    PL X0 = make({ {{0,1},{0,1}}, {{1,2},{1,4}}, {{3,4},{1,2}}, {{1,1},{1,1}} });
    PL X1 = make({ {{0,1},{0,1}}, {{1,2},{1,2}}, {{3,4},{5,8}}, {{7,8},{3,4}}, {{1,1},{1,1}} });
    PL I = make({ {{0,1},{0,1}}, {{1,1},{1,1}} });
    vector<PL> G = { X0, inv(X0), X1, inv(X1) };
    int invl[4] = { 1, 0, 3, 2 };
    {  // relation checks: [x0 x1^-1, x0^-1 x1 x0] = [x0 x1^-1, x0^-2 x1 x0^2] = 1
        auto word = [&](vector<int> w) { PL g = I; for (int s : w) g = mul(g, G[s]); return g; };
        auto comm = [&](vector<int> u, vector<int> v) { vector<int> w; for (int i = (int)u.size() - 1; i >= 0; i--) w.push_back(invl[u[i]]); for (int i = (int)v.size() - 1; i >= 0; i--) w.push_back(invl[v[i]]); w.insert(w.end(), u.begin(), u.end()); w.insert(w.end(), v.begin(), v.end()); return w; };
        bool r1 = eq(word(comm({ 0,3 }, { 1,2,0 })), I), r2 = eq(word(comm({ 0,3 }, { 1,1,2,0,0 })), I), nc = !eq(mul(X0, X1), mul(X1, X0));
        printf("{\"relations\": {\"r1\": %d, \"r2\": %d, \"noncommuting\": %d}}\n", r1, r2, nc);
        if (!(r1 && r2 && nc)) return 3;
    }
    unordered_map<vector<u64>, int, KeyHash> idx;
    vector<int> radius{ 0 }, parent{ -1 }; vector<signed char> plet{ -1 };
    vector<PL> cur{ I }; vector<int> curId{ 0 }; idx[key(I)] = 0;
    vector<int> nb(4, -2); vector<long long> sphere{ 1 };
    for (int k = 0; k < R; k++) {
        vector<PL> nxt; vector<int> nxtId;
        for (size_t i = 0; i < cur.size(); i++) {
            int gid = curId[i];
            for (int s = 0; s < 4; s++) {
                PL h = mul(cur[i], G[s]); auto kk = key(h);
                auto f = idx.find(kk); int hid;
                if (f == idx.end()) { hid = (int)radius.size(); idx.emplace(move(kk), hid); radius.push_back(k + 1); parent.push_back(gid); plet.push_back((signed char)s); nxt.push_back(move(h)); nxtId.push_back(hid); nb.resize(4 * (size_t)(hid + 1), -2); }
                else hid = f->second;
                nb[4 * (size_t)gid + s] = hid;
            }
        }
        sphere.push_back((long long)nxt.size()); cur.swap(nxt); curId.swap(nxtId);
        fprintf(stderr, "sphere %d: %lld (ball %zu)\n", k + 1, sphere.back(), radius.size());
    }
    for (size_t i = 0; i < cur.size(); i++) for (int s = 0; s < 4; s++) { auto f = idx.find(key(mul(cur[i], G[s]))); nb[4 * (size_t)curId[i] + s] = (f == idx.end()) ? -1 : f->second; }
    cur.clear(); curId.clear(); { unordered_map<vector<u64>, int, KeyHash> tmp; idx.swap(tmp); }
    printf("{\"spheres\": ["); for (size_t k = 0; k < sphere.size(); k++) printf("%s%lld", k ? ", " : "", sphere[k]); printf("]}\n");
    int n = (int)radius.size();
    for (int v = 0; v < n; v++) for (int s = 0; s < 4; s++) { int w = nb[4 * (size_t)v + s]; if (w >= 0 && nb[4 * (size_t)w + invl[s]] != v) { fprintf(stderr, "asymmetric edge\n"); return 4; } }
    for (int r = 1; r <= R; r++) {
        int nr = 0; while (nr < n && radius[nr] <= r) nr++;
        auto inB = [&](int w) { return w >= 0 && w < nr; };
        long long bdB = 0; for (int v = 0; v < nr; v++) for (int s = 0; s < 4; s++) if (!inB(nb[4 * (size_t)v + s])) bdB++;
        long long P = bdB, Q = nr; { long long g = __gcd(P, Q); P /= g; Q /= g; }
        vector<char> best(nr, 1); int iters = 0;
        while (true) {
            iters++;
            Flow fl(nr + 2); int S = nr, T = nr + 1; fl.reserve(8 * (size_t)nr);
            for (int v = 0; v < nr; v++) {
                fl.add(S, v, P, 0); int out = 0;
                for (int s = 0; s < 4; s++) { int w = nb[4 * (size_t)v + s]; if (!inB(w)) out++; else if (v < w) fl.add(v, w, Q, Q); }
                if (out) fl.add(v, T, Q * out, 0);
            }
            long long cut = fl.maxflow(S, T);
            if (cut >= P * (long long)nr) break;  // no subset of B_r beats P/Q
            auto side = fl.sourceSide(S);
            long long sz = 0, bd = 0;
            for (int v = 0; v < nr; v++) if (side[v]) { sz++; for (int s = 0; s < 4; s++) { int w = nb[4 * (size_t)v + s]; if (!inB(w) || !side[w]) bd++; } }
            for (int v = 0; v < nr; v++) best[v] = side[v];
            long long g = __gcd(bd, sz); P = bd / g; Q = sz / g;
        }
        long long sz = 0, bd = 0; vector<long long> byRad(r + 1, 0);
        for (int v = 0; v < nr; v++) if (best[v]) { sz++; byRad[radius[v]]++; for (int s = 0; s < 4; s++) { int w = nb[4 * (size_t)v + s]; if (!inB(w) || !best[w]) bd++; } }
        printf("{\"r\": %d, \"ball\": %d, \"ball_boundary\": %lld, \"h_num\": %lld, \"h_den\": %lld, \"h\": %.6f, \"density\": %.6f, \"opt_size\": %lld, \"opt_boundary\": %lld, \"dinkelbach_iters\": %d, \"opt_by_radius\": [", r, nr, bdB, P, Q, (double)P / Q, 4.0 - (double)P / Q, sz, bd, iters);
        for (int k = 0; k <= r; k++) printf("%s%lld", k ? ", " : "", byRad[k]);
        printf("]}\n"); fflush(stdout);
        if (!outp.empty()) {  // optimal set as words: 0=x0, 1=x0^-1, 2=x1, 3=x1^-1 ("e" = identity)
            string fn = outp + "_r" + to_string(r) + ".words"; FILE* fo = fopen(fn.c_str(), "w");
            for (int v = 0; v < nr; v++) if (best[v]) { string w; int u = v; while (parent[u] >= 0) { w.push_back((char)('0' + plet[u])); u = parent[u]; } reverse(w.begin(), w.end()); fprintf(fo, "%s\n", w.empty() ? "e" : w.c_str()); }
            fclose(fo);
        }
    }
}
