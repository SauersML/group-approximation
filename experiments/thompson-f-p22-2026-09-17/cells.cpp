// Adaptive Boltzmann-cylinder bound for the doubling ratio of S(n->k) in Thompson's F.
// C++ port of adaptive_limit.py (same cells, same refinement rules), with the neighbour
// refinement loop.  Flows use doubles; the ratio of every chosen set is recomputed exactly
// (dyadic masses summed in __int128) by a second enumeration pass.
//
// build: g++ -O2 -std=c++17 -o cells cells.cpp
// usage: ./cells n k H rounds [mode]
//   start from the uniform depth-H partition; each round: build Q-cells, optimise, then refine
//   mode 0 (default): every excluded a-cell and every chosen a-cell sharing an image class with an excluded one;
//   mode 1: every chosen a-cell;  mode 2: every a-cell.
//   H < 0: start instead from the caterpillar partition of depth -H (every entry resolved along caterpillar spines).
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef __int128 i128;

enum { LEAF = 0, STAR = 1, GI = 2, CAR = 3 };
struct TN { int t, l, r, e; bool g; };
vector<TN> pool;
unordered_map<unsigned long long, int> internmap;

int mk(int t, int l, int r) {
    unsigned long long key = (unsigned long long)t | ((unsigned long long)(l + 1) << 2) | ((unsigned long long)(r + 1) << 33);
    auto it = internmap.find(key);
    if (it != internmap.end()) return it->second;
    TN x;
    x.t = t; x.l = l; x.r = r;
    if (t == LEAF) { x.e = 0; x.g = false; }
    else if (t == STAR) { x.e = 1; x.g = false; }
    else if (t == GI) { x.e = 0; x.g = true; }
    else { x.e = pool[l].e + pool[r].e - 2; x.g = pool[l].g || pool[r].g; }
    pool.push_back(x);
    int id = (int)pool.size() - 1;
    internmap[key] = id;
    return id;
}
int NLEAF, NSTAR, NGI;

typedef vector<uint8_t> Path;

int getn(int u, const Path &p, size_t upto) {
    for (size_t i = 0; i < upto; i++) u = p[i] ? pool[u].r : pool[u].l;
    return u;
}
int putn(int u, const Path &p, size_t i, int v) {
    if (i == p.size()) return v;
    if (p[i] == 0) return mk(CAR, putn(pool[u].l, p, i + 1, v), pool[u].r);
    return mk(CAR, pool[u].l, putn(pool[u].r, p, i + 1, v));
}
// children of refining node at path of entry j of cell
void refine_kids(const vector<int> &cell, int j, const Path &p, vector<int> &c0, vector<int> &c1, int &kind) {
    int v = getn(cell[j], p, p.size());
    kind = pool[v].t;
    int a, b;
    if (kind == STAR) { a = NLEAF; b = mk(CAR, NSTAR, NSTAR); }
    else if (kind == GI) { a = mk(CAR, NGI, NSTAR); b = mk(CAR, NSTAR, NGI); }
    else { fprintf(stderr, "refine on closed node\n"); exit(1); }
    c0 = cell; c1 = cell;
    c0[j] = putn(cell[j], p, 0, a);
    c1[j] = putn(cell[j], p, 0, b);
}
// shallowest open node of a tree (ties: lexicographic path)
bool shallow_open(int u, Path &best) {
    // BFS
    deque<pair<int, Path>> q;
    q.push_back({u, Path()});
    while (!q.empty()) {
        auto pr = q.front(); q.pop_front();
        int t = pool[pr.first].t;
        if (t == STAR || t == GI) { best = pr.second; return true; }
        if (t == CAR) {
            Path a = pr.second; a.push_back(0);
            Path b = pr.second; b.push_back(1);
            q.push_back({pool[pr.first].l, a});
            q.push_back({pool[pr.first].r, b});
        }
    }
    return false;
}

struct RN { vector<int> cell; int j = -1; Path path; int kind = -1; int kid[2] = {-1, -1}; int cid = -1; };
vector<RN> rt;
vector<int> roots;
int n, k, d;

bool cell_open(const vector<int> &cell, int &j, Path &p) {
    bool found = false;
    for (int i = 0; i < (int)cell.size(); i++) {
        Path q;
        if (shallow_open(cell[i], q) && (!found || q.size() < p.size())) { found = true; j = i; p = q; }
    }
    return found;
}
void refine_leaf(int idx) {
    int j; Path p;
    if (!cell_open(rt[idx].cell, j, p)) return;
    vector<int> c0, c1; int kind;
    refine_kids(rt[idx].cell, j, p, c0, c1, kind);
    rt[idx].j = j; rt[idx].path = p; rt[idx].kind = kind;
    RN a, b; a.cell = c0; b.cell = c1;
    rt.push_back(a); rt[idx].kid[0] = (int)rt.size() - 1;
    rt.push_back(b); rt[idx].kid[1] = (int)rt.size() - 1;
}
vector<int> leaves_list;  // cid -> rt index
void number_cells() {
    leaves_list.clear();
    for (int r : roots) {
        vector<int> st = {r};
        while (!st.empty()) {
            int x = st.back(); st.pop_back();
            if (rt[x].kid[0] < 0) { rt[x].cid = (int)leaves_list.size(); leaves_list.push_back(x); }
            else { rt[x].cid = -1; st.push_back(rt[x].kid[1]); st.push_back(rt[x].kid[0]); }
        }
    }
}

// lookup: returns cid >= 0, or -1 with refinement (j, prefix length) stored
int lk_j; size_t lk_len; const Path *lk_path;
int lookup(const vector<int> &piece) {
    int pos = -1;
    for (int j = 0; j < n; j++) if (pool[piece[j]].g) { pos = j; break; }
    int x = roots[pos];
    while (rt[x].cid < 0) {
        int j = rt[x].j; const Path &p = rt[x].path;
        int u = piece[j];
        for (size_t i = 0; i < p.size(); i++) {
            int t = pool[u].t;
            if (t == STAR || t == GI) { lk_j = j; lk_len = i; lk_path = &rt[x].path; return -1; }
            if (t == LEAF) { fprintf(stderr, "incompatible piece\n"); exit(1); }
            u = p[i] ? pool[u].r : pool[u].l;
        }
        int t = pool[u].t;
        if (rt[x].kind == STAR) {
            if (t == STAR) { lk_j = j; lk_len = p.size(); lk_path = &rt[x].path; return -1; }
            x = (t == LEAF) ? rt[x].kid[0] : rt[x].kid[1];
        } else {
            if (t == GI) { lk_j = j; lk_len = p.size(); lk_path = &rt[x].path; return -1; }
            x = pool[pool[u].l].g ? rt[x].kid[0] : rt[x].kid[1];
        }
    }
    return rt[x].cid;
}

// shapes
struct SN { int var, l, r; };  // var >= 0 : variable
vector<SN> snodes;
vector<vector<int>> shapes;  // each: k root snode ids
void gen_shapes() {
    set<string> seen;
    function<string(int)> str = [&](int s) -> string {
        if (snodes[s].var >= 0) return "v" + to_string(snodes[s].var);
        return "(" + str(snodes[s].l) + "," + str(snodes[s].r) + ")";
    };
    function<void(vector<int>)> rec = [&](vector<int> f) {
        if ((int)f.size() == k) {
            string key;
            for (int s : f) key += str(s) + ";";
            if (!seen.count(key)) { seen.insert(key); shapes.push_back(f); }
            return;
        }
        for (int i = 0; i + 1 < (int)f.size(); i++) {
            snodes.push_back({-1, f[i], f[i + 1]});
            vector<int> g(f.begin(), f.begin() + i);
            g.push_back((int)snodes.size() - 1);
            g.insert(g.end(), f.begin() + i + 2, f.end());
            rec(g);
        }
    };
    vector<int> f;
    for (int j = 0; j < n; j++) { snodes.push_back({j, -1, -1}); f.push_back((int)snodes.size() - 1); }
    rec(f);
}

// match: 0 fail, 1 ok, 2 refine at (entry, path)
int env_node[64], env_entry[64];
Path env_path[64];
int rf_entry; Path rf_path;
int match(int s, int u, int entry, Path &cur) {
    if (snodes[s].var >= 0) { env_node[snodes[s].var] = u; env_entry[snodes[s].var] = entry; env_path[snodes[s].var] = cur; return 1; }
    int t = pool[u].t;
    if (t == LEAF) return 0;
    if (t == STAR || t == GI) { rf_entry = entry; rf_path = cur; return 2; }
    cur.push_back(0);
    int r = match(snodes[s].l, pool[u].l, entry, cur);
    cur.pop_back();
    if (r != 1) return r;
    cur.push_back(1);
    r = match(snodes[s].r, pool[u].r, entry, cur);
    cur.pop_back();
    return r;
}

struct VecHash {
    size_t operator()(const vector<int> &v) const {
        size_t h = v.size() * 0x9e3779b97f4a7c15ULL;
        for (int x : v) h ^= (size_t)x + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
        return h;
    }
};

// enumerate Q-cells; callback(sig, exponent)
template <class F> ll enum_q(F cb) {
    ll nq = 0;
    for (int pos = 0; pos < k; pos++) {
        vector<vector<int>> st;
        vector<int> q(k, NSTAR); q[pos] = NGI;
        st.push_back(q);
        vector<int> sig; vector<int> piece(n);
        while (!st.empty()) {
            vector<int> c = st.back(); st.pop_back();
            sig.clear();
            bool refined = false;
            int rentry = -1; Path rpath;
            for (auto &sh : shapes) {
                int res = 1;
                for (int i = 0; i < k && res == 1; i++) { Path cur; res = match(sh[i], c[i], i, cur); }
                if (res == 0) continue;
                if (res == 2) { refined = true; rentry = rf_entry; rpath = rf_path; break; }
                for (int j = 0; j < n; j++) piece[j] = env_node[j];
                int cid = lookup(piece);
                if (cid >= 0) sig.push_back(cid);
                else {
                    refined = true; rentry = env_entry[lk_j]; rpath = env_path[lk_j];
                    rpath.insert(rpath.end(), lk_path->begin(), lk_path->begin() + lk_len);
                    break;
                }
            }
            if (refined) {
                vector<int> c0, c1; int kind;
                refine_kids(c, rentry, rpath, c0, c1, kind);
                st.push_back(c1); st.push_back(c0);
                continue;
            }
            nq++;
            if (!sig.empty()) {
                sort(sig.begin(), sig.end());
                sig.erase(unique(sig.begin(), sig.end()), sig.end());
                int e = 2 * d;
                for (int i = 0; i < k; i++) e += pool[c[i]].e;
                cb(sig, e);
            }
        }
    }
    return nq;
}

// ---------------------------------------------------------------- flow + Dinkelbach
struct Dinic {
    struct E { int to; double cap; };
    vector<E> e; vector<vector<int>> g; vector<int> level, it;
    Dinic(int N) : g(N), level(N), it(N) {}
    void add(int a, int b, double c) { g[a].push_back((int)e.size()); e.push_back({b, c}); g[b].push_back((int)e.size()); e.push_back({a, 0}); }
    double eps = 1e-14;
    bool bfs(int s, int t) {
        fill(level.begin(), level.end(), -1); level[s] = 0;
        vector<int> q = {s}; size_t h = 0;
        while (h < q.size()) { int v = q[h++]; for (int id : g[v]) if (e[id].cap > eps && level[e[id].to] < 0) { level[e[id].to] = level[v] + 1; q.push_back(e[id].to); } }
        return level[t] >= 0;
    }
    double dfs(int v, int t, double f) {
        if (v == t) return f;
        for (int &i = it[v]; i < (int)g[v].size(); i++) {
            int id = g[v][i]; int w = e[id].to;
            if (e[id].cap > eps && level[w] == level[v] + 1) {
                double r = dfs(w, t, min(f, e[id].cap));
                if (r > eps) { e[id].cap -= r; e[id ^ 1].cap += r; return r; }
            }
        }
        return 0;
    }
    double maxflow(int s, int t) {
        double fl = 0;
        while (bfs(s, t)) { fill(it.begin(), it.end(), 0); double f; while ((f = dfs(s, t, 1e300)) > eps) fl += f; }
        return fl;
    }
};

i128 gcd128(i128 a, i128 b) { if (a < 0) a = -a; if (b < 0) b = -b; while (b) { i128 r = a % b; a = b; b = r; } return a; }
string s128(i128 x) { if (x == 0) return "0"; bool neg = x < 0; if (neg) x = -x; string s; while (x) { s += char('0' + (int)(x % 10)); x /= 10; } if (neg) s += '-'; reverse(s.begin(), s.end()); return s; }
const int SH = 84;
i128 dy(int e) {
    if (e + SH < 0 || e > 30) { fprintf(stderr, "exponent out of range %d\n", e); exit(1); }
    return (i128)1 << (e + SH);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: cells n k H rounds\n"); return 1; }
    n = atoi(argv[1]); k = atoi(argv[2]); int H = atoi(argv[3]); int rounds = atoi(argv[4]);
    int mode = argc > 5 ? atoi(argv[5]) : 0;
    d = n - k;
    NLEAF = mk(LEAF, -1, -1); NSTAR = mk(STAR, -1, -1); NGI = mk(GI, -1, -1);
    gen_shapes();
    for (int pos = 0; pos < n; pos++) {
        RN r; r.cell.assign(n, NSTAR); r.cell[pos] = NGI;
        rt.push_back(r); roots.push_back((int)rt.size() - 1);
    }
    if (H < 0) {
        // caterpillar partition: refine every entry along caterpillar spines (one child of each spine caret is a leaf)
        int D = -H;
        auto cat_open = [&](int u, Path &p) -> bool {
            p.clear(); int depth = 0;
            while (true) {
                int t = pool[u].t;
                if (t == STAR || t == GI) return depth < D;
                if (t == LEAF || depth >= D) return false;
                int tl = pool[pool[u].l].t, tr = pool[pool[u].r].t;
                if (tl == STAR) { p.push_back(0); return true; }
                if (tr == STAR) { p.push_back(1); return true; }
                if (tl == LEAF) { p.push_back(1); u = pool[u].r; depth++; continue; }
                if (tr == LEAF) { p.push_back(0); u = pool[u].l; depth++; continue; }
                return false;
            }
        };
        vector<int> st(roots.begin(), roots.end());
        while (!st.empty()) {
            int x = st.back(); st.pop_back();
            bool done = false;
            for (int j = 0; j < n && !done; j++) {
                Path p;
                if (cat_open(rt[x].cell[j], p)) {
                    vector<int> c0, c1; int kind;
                    refine_kids(rt[x].cell, j, p, c0, c1, kind);
                    rt[x].j = j; rt[x].path = p; rt[x].kind = kind;
                    RN a, b; a.cell = c0; b.cell = c1;
                    rt.push_back(a); rt[x].kid[0] = (int)rt.size() - 1;
                    rt.push_back(b); rt[x].kid[1] = (int)rt.size() - 1;
                    st.push_back(rt[x].kid[0]); st.push_back(rt[x].kid[1]);
                    done = true;
                }
            }
        }
    } else
    // uniform depth H
    {
        vector<int> st(roots.begin(), roots.end());
        while (!st.empty()) {
            int x = st.back(); st.pop_back();
            int j; Path p;
            if (cell_open(rt[x].cell, j, p) && (int)p.size() < H) { refine_leaf(x); st.push_back(rt[x].kid[0]); st.push_back(rt[x].kid[1]); }
        }
    }
    for (int rd = 0; rd < rounds; rd++) {
        auto t0 = chrono::steady_clock::now();
        number_cells();
        int nc = (int)leaves_list.size();
        vector<i128> amass(nc); i128 atot = 0;
        for (int c = 0; c < nc; c++) { int e = 0; for (int x : rt[leaves_list[c]].cell) e += pool[x].e; amass[c] = dy(e); atot += amass[c]; }
        if (atot != (i128)n * dy(n - 1)) { fprintf(stderr, "a-mass total mismatch\n"); return 1; }
        unordered_map<vector<int>, int, VecHash> cmap;
        vector<i128> cmass; vector<ll> estart = {0}; vector<int> eflat;
        ll nq = enum_q([&](const vector<int> &sig, int e) {
            auto itc = cmap.find(sig);
            int id;
            if (itc == cmap.end()) {
                id = (int)cmass.size(); cmap.emplace(sig, id); cmass.push_back(0);
                eflat.insert(eflat.end(), sig.begin(), sig.end()); estart.push_back((ll)eflat.size());
            } else id = itc->second;
            cmass[id] += dy(e);
        });
        int ncl = (int)cmass.size();
        cmap.clear(); cmap.rehash(0);
        i128 ctot = 0; for (auto x : cmass) ctot += x;
        vector<double> am(nc), cm(ncl);
        double sc = ldexp(1.0, -SH);
        for (int c = 0; c < nc; c++) am[c] = (double)amass[c] * sc;
        for (int c = 0; c < ncl; c++) cm[c] = (double)cmass[c] * sc;
        // Dinkelbach
        vector<char> inA(nc, 1);
        i128 bnum = ctot, bden = atot;
        long double ratio = (long double)ctot / (long double)atot;
        for (int iter = 0; iter < 60; iter++) {
            Dinic D(nc + ncl + 2);
            int s = nc + ncl, t = s + 1;
            double rr = (double)ratio;
            double INF = 1e30;
            for (int c = 0; c < nc; c++) D.add(s, c, rr * am[c]);
            for (int c = 0; c < ncl; c++) { for (ll i = estart[c]; i < estart[c + 1]; i++) D.add(eflat[i], nc + c, INF); D.add(nc + c, t, cm[c]); }
            double fl = D.maxflow(s, t);
            double tota = 0; for (double x : am) tota += x;
            if (rr * tota - fl <= 1e-12 * tota) break;
            D.bfs(s, t);
            vector<char> A(nc, 0); int cntA = 0;
            for (int c = 0; c < nc; c++) if (D.level[c] >= 0) { A[c] = 1; cntA++; }
            if (!cntA) break;
            i128 num = 0, den = 0;
            for (int c = 0; c < nc; c++) if (A[c]) den += amass[c];
            for (int c = 0; c < ncl; c++) { bool hit = false; for (ll i = estart[c]; i < estart[c + 1] && !hit; i++) hit = A[eflat[i]]; if (hit) num += cmass[c]; }
            long double nr = (long double)num / (long double)den;
            if (nr >= ratio * (1 - 1e-15L)) break;
            ratio = nr; bnum = num; bden = den; inA = A;
        }
        i128 g = gcd128(bnum, bden);
        int chosen = 0; for (char x : inA) chosen += x;
        // neighbour refinement set
        vector<char> ref(nc, 0);
        if (mode == 1) { for (int c = 0; c < nc; c++) ref[c] = inA[c]; }
        else if (mode == 2) { for (int c = 0; c < nc; c++) ref[c] = 1; }
        else for (int c = 0; c < nc; c++) if (!inA[c]) ref[c] = 1;
        if (mode == 0) for (int c = 0; c < ncl; c++) {
            bool ex = false; for (ll i = estart[c]; i < estart[c + 1] && !ex; i++) ex = !inA[eflat[i]];
            if (ex) for (ll i = estart[c]; i < estart[c + 1]; i++) ref[eflat[i]] = 1;
        }
        int nref = 0; for (char x : ref) nref += x;
        double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
        printf("round %d: S(%d->%d) a-cells=%d Q-cells=%lld classes=%d ratio(all)=%.6f R=%s/%s ~ %.6f chosen=%d elapsed %.1fs refine %d\n",
               rd, n, k, nc, nq, ncl, (double)((long double)ctot / (long double)atot), s128(bnum / g).c_str(), s128(bden / g).c_str(),
               (double)ratio, chosen, el, nref);
        fflush(stdout);
        if (rd + 1 < rounds) for (int c = 0; c < nc; c++) if (ref[c]) refine_leaf(leaves_list[c]);
    }
    return 0;
}
