// Cone-propagation tree finder on the radius-R ball of a BMW parity kernel, with the optional
// short-k restriction of the census (products only when one factor has length <= k).
// A C++ port of dtree2.py (w10-107), same search and same certificate format, read by verify_cone.py.
// input (stdin, written by ctree.py): m n / iA / iB / m*n lines "h v v' h'" (h v = v' h')
// usage: ctree R SHORT(-1 = none) MAXLEAVES TIMEOUT_S CLASSID < class.txt
#include <bits/stdc++.h>
using namespace std;
int m, n; vector<int> iA, iB; vector<array<int,2>> SQ;   // SQ[h*n+v] = (v', h')
struct El { vector<int> v, h; };
static El mul(const El& a, const El& b) {
    El r; r.v = a.v; vector<int> h = a.h;
    for (int v0 : b.v) {
        int v = v0;
        for (int i = (int)h.size() - 1; i >= 0; --i) { auto q = SQ[h[i] * n + v]; v = q[0]; h[i] = q[1]; }
        if (!r.v.empty() && r.v.back() == iB[v]) r.v.pop_back(); else r.v.push_back(v);
    }
    for (int c : b.h) { if (!h.empty() && h.back() == iA[c]) h.pop_back(); else h.push_back(c); }
    r.h = h; return r;
}
static string key(const El& e) { string s; for (int x : e.v) s += char('a' + x); s += '|'; for (int x : e.h) s += char('a' + x); return s; }
vector<El> els; unordered_map<string,int> idx;
vector<int> INV, isK; vector<vector<pair<int,int>>> Lp, Rp;   // Lp[a]: (b, a*b), Rp[a]: (b, b*a)
vector<char> inP; vector<pair<int,int>> par; vector<int> trail;
static string word(int i) { string s; for (int x : els[i].v) s += "v" + to_string(x); for (int x : els[i].h) s += "h" + to_string(x); return s; }
static void undo(size_t mk) { while (trail.size() > mk) { inP[trail.back()] = 0; trail.pop_back(); } }
// add g (with parent p) and close; returns conflict pair (x,y) with x y = 1, or (-1,-1)
static pair<int,int> close1(int g) {
    vector<int> todo;
    if (inP[g]) return {-1, -1};
    inP[g] = 1; par[g] = {-1, -1}; trail.push_back(g); todo.push_back(g);
    while (!todo.empty()) {
        int x = todo.back(); todo.pop_back();
        if (inP[INV[x]]) return {x, INV[x]};
        for (int s = 0; s < 2; ++s) for (auto& bk : (s ? Rp[x] : Lp[x])) {
            int b = bk.first, k = bk.second;
            if (!inP[b]) continue;
            pair<int,int> pr = s ? make_pair(b, x) : make_pair(x, b);
            if (k == 0) return pr;
            if (!inP[k]) { inP[k] = 1; par[k] = pr; trail.push_back(k); todo.push_back(k); }
        }
    }
    return {-1, -1};
}
long nleaves = 0, MAXL; double TMAX; chrono::steady_clock::time_point T0;
struct Budget {};
static string leaf(pair<int,int> w) {
    string st; unordered_set<int> seen; bool first = true;
    function<void(int)> need = [&](int x) {
        if (seen.count(x) || par[x].first < 0) return;
        seen.insert(x); need(par[x].first); need(par[x].second);
        st += string(first ? "" : ",") + "[\"" + word(x) + "\",\"" + word(par[x].first) + "\",\"" + word(par[x].second) + "\"]";
        first = false;
    };
    need(w.first); need(w.second); ++nleaves;
    return "[\"leaf\",[\"" + word(w.first) + "\",\"" + word(w.second) + "\"],[" + st + "]]";
}
vector<int> cands;
static string split(int g, const string& a, const string& b) { return "[\"split\",\"" + word(g) + "\"," + a + "," + b + "]"; }
// state: closed, no conflict. returns "" when no tree within depth.
static string node(int depth) {
    double el = chrono::duration<double>(chrono::steady_clock::now() - T0).count();
    if (el > TMAX || nleaves > MAXL) throw Budget();
    if (depth == 0) return "";
    int best = -1; long bsc = -1;
    for (int g : cands) {
        if (inP[g] || inP[INV[g]]) continue;
        size_t mk = trail.size();
        auto w1 = close1(g); size_t s1 = trail.size() - mk; string l1; if (w1.first >= 0) l1 = leaf(w1); undo(mk);
        auto w2 = close1(INV[g]); size_t s2 = trail.size() - mk; string l2; if (w2.first >= 0) l2 = leaf(w2); undo(mk);
        if (w1.first >= 0 && w2.first >= 0) return split(g, l1, l2);
        if (w1.first >= 0) { close1(INV[g]); string t = node(depth); undo(mk); return t.empty() ? "" : split(g, l1, t); }
        if (w2.first >= 0) { close1(g); string t = node(depth); undo(mk); return t.empty() ? "" : split(g, t, l2); }
        long sc = (long)min(s1, s2);
        if (sc > bsc) { bsc = sc; best = g; }
    }
    if (best < 0) return "";
    size_t mk = trail.size();
    close1(best); string t1 = node(depth - 1); undo(mk);
    if (t1.empty()) return "";
    close1(INV[best]); string t2 = node(depth - 1); undo(mk);
    if (t2.empty()) return "";
    return split(best, t1, t2);
}
int main(int argc, char** argv) {
    int R = atoi(argv[1]), SHORT = atoi(argv[2]); MAXL = atol(argv[3]); TMAX = atof(argv[4]); int cls = atoi(argv[5]);
    T0 = chrono::steady_clock::now();
    cin >> m >> n; iA.resize(m); iB.resize(n); SQ.resize(m * n);
    for (auto& x : iA) cin >> x; for (auto& x : iB) cin >> x;
    for (int i = 0; i < m * n; ++i) { int h, v, v2, h2; cin >> h >> v >> v2 >> h2; SQ[h * n + v] = {v2, h2}; }
    vector<El> gens; for (int v = 0; v < n; ++v) gens.push_back({{v}, {}}); for (int h = 0; h < m; ++h) gens.push_back({{}, {h}});
    els.push_back({}); idx[key(els[0])] = 0; vector<int> layer{0};
    for (int d = 0; d < R; ++d) { vector<int> nl;
        for (int g : layer) for (auto& t : gens) { El x = mul(els[g], t); string k = key(x);
            if (!idx.count(k)) { idx[k] = els.size(); nl.push_back(els.size()); els.push_back(x); } }
        layer = nl; }
    int N = els.size(); isK.assign(N, 0); INV.assign(N, -1); vector<int> K;
    for (int i = 1; i < N; ++i) if (els[i].v.size() % 2 == 0 && els[i].h.size() % 2 == 0) { isK[i] = 1; K.push_back(i); }
    for (int i : K) { El a; for (int j = els[i].h.size() - 1; j >= 0; --j) a.h.push_back(iA[els[i].h[j]]);
        El b; for (int j = els[i].v.size() - 1; j >= 0; --j) b.v.push_back(iB[els[i].v[j]]);
        INV[i] = idx.at(key(mul(a, b))); }
    Lp.assign(N, {}); Rp.assign(N, {});
    auto len = [&](int i) { return (int)(els[i].v.size() + els[i].h.size()); };
    vector<char> isLeft(N, 0); for (int i : K) if (SHORT < 0 || len(i) <= SHORT) isLeft[i] = 1;
    long npairs = 0;
    for (int i : K) if (isLeft[i]) for (int j : K) {
        if (isLeft[j] && j < i) continue;
        for (int s = 0; s < 2; ++s) { if (s && i == j) break;
            int a = s ? j : i, b = s ? i : j;
            auto it = idx.find(key(mul(els[a], els[b]))); if (it == idx.end()) continue;
            int k = it->second; if (k != 0 && !isK[k]) continue;
            Lp[a].push_back({b, k}); Rp[b].push_back({a, k}); ++npairs; }
    }
    fprintf(stderr, "ball %d kernel %zu pairs %ld build %.1fs\n", N, K.size(), npairs,
            chrono::duration<double>(chrono::steady_clock::now() - T0).count());
    if (getenv("CNF")) {   // dump the census CNF (variable = position in K, plus 1) and the variable map
        vector<int> var(N, 0); for (size_t t = 0; t < K.size(); ++t) var[K[t]] = t + 1;
        string fn = getenv("CNF"); FILE* f = fopen(fn.c_str(), "w"); FILE* g = fopen((fn + ".map").c_str(), "w");
        fprintf(f, "p cnf %zu %ld\n", K.size(), npairs + (long)K.size());
        for (int i : K) if (i < INV[i]) { fprintf(f, "%d %d 0\n%d %d 0\n", var[i], var[INV[i]], -var[i], -var[INV[i]]); }
        for (int a : K) for (auto& bk : Lp[a]) {
            if (bk.second == 0) fprintf(f, "%d %d 0\n", -var[a], -var[bk.first]);
            else fprintf(f, "%d %d %d 0\n", -var[a], -var[bk.first], var[bk.second]); }
        for (int i : K) fprintf(g, "%d %s %d\n", var[i], word(i).c_str(), var[INV[i]]);
        fclose(f); fclose(g); return 0;
    }
    inP.assign(N, 0); par.assign(N, {-1, -1});
    for (int i : K) if (i < INV[i]) cands.push_back(i);
    stable_sort(cands.begin(), cands.end(), [&](int a, int b) { return len(a) < len(b); });
    try {
        for (int d = 1; d < 12; ++d) { nleaves = 0; string t = node(d);
            if (!t.empty()) { printf("{\"cls\": %d, \"R\": %d, \"short\": %d, \"depth\": %d, \"leaves\": %ld, \"tree\": %s}\n", cls, R, SHORT, d, nleaves, t.c_str()); return 0; }
            fprintf(stderr, "no tree of lookahead depth %d\n", d); }
    } catch (Budget&) { printf("budget exhausted: leaves %ld time %.0f\n", nleaves, chrono::duration<double>(chrono::steady_clock::now() - T0).count()); }
    return 1;
}
