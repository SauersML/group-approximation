// Non-doubling witnesses for a finite set S of positive monomials of Thompson's group F.
//
// M = < x_0, x_1, ... | x_j x_i = x_i x_{j+1} (i < j) >, normal forms x_{i_1}...x_{i_D},
// i_1 <= ... <= i_D.  U = M_{D,L}: normal forms of degree D with all letters <= L.
//
// Network: source -2-> y (y in U) -INF-> s y (s in S) -1-> sink.  A cut with source side
// {source} u Y u N, N containing S Y, costs 2(|U| - |Y|) + |N|, so
//     min cut = min_{Y subset U} ( 2(|U| - |Y|) + |S Y| ).
// Hence some Y subset U has |S Y| < 2|Y|  iff  maxflow < 2|U|.  The words y reachable from
// the source in the residual network of a maximum flow form the smallest minimizer Y* of
// |S Y| - 2|Y|; it does not depend on which maximum flow was found.
//
// Usage: witness_flow D L "0,0;0,1;..."     (monomials ';'-separated, letters ','-separated)
// Output: one JSON line.  With env CERT=path and a witness found, Y* is written there, one
// word per line in lexicographic order.  The count |S Y*| is recomputed without the network.
// Written for this experiment; the monoid arithmetic follows experiments/thompson-f/doubling_flow.cpp.
#include <bits/stdc++.h>
using namespace std;
typedef vector<uint8_t> Word;
typedef unsigned __int128 Key;

static Word left_mul_letter(int j, const Word& w) {
  Word out; out.reserve(w.size() + 1);
  size_t k = 0, n = w.size();
  while (k < n && w[k] < j) { out.push_back(w[k]); j++; k++; }
  if (j > 63) { fprintf(stderr, "letter overflow\n"); exit(2); }
  out.push_back((uint8_t)j);
  for (; k < n; k++) out.push_back(w[k]);
  return out;
}
static Word mul(const Word& a, const Word& b) {
  Word r = b;
  for (int i = (int)a.size() - 1; i >= 0; i--) r = left_mul_letter(a[i], r);
  return r;
}
static Key key_of(const Word& w) {
  if (w.size() > 20) { fprintf(stderr, "word too long\n"); exit(2); }
  Key k = (Key)w.size();
  for (size_t i = 0; i < w.size(); i++) k |= (Key)w[i] << (8 + 6 * i);
  return k;
}
struct KeyHash { size_t operator()(const Key& k) const {
  uint64_t lo = (uint64_t)k, hi = (uint64_t)(k >> 64);
  return std::hash<uint64_t>()(lo * 0x9E3779B97F4A7C15ULL ^ hi); } };

struct Dinic {
  struct E { int to; int cap; };
  vector<E> e; vector<vector<int>> g; vector<int> level, it;
  Dinic(int n) : g(n), level(n), it(n) {}
  void add(int a, int b, int c) { g[a].push_back(e.size()); e.push_back({b, c}); g[b].push_back(e.size()); e.push_back({a, 0}); }
  bool bfs(int s, int t) {
    fill(level.begin(), level.end(), -1); level[s] = 0; deque<int> q{s};
    while (!q.empty()) { int v = q.front(); q.pop_front();
      for (int id : g[v]) if (e[id].cap > 0 && level[e[id].to] < 0) { level[e[id].to] = level[v] + 1; q.push_back(e[id].to); } }
    return level[t] >= 0;
  }
  int dfs(int v, int t, int f) {
    if (v == t) return f;
    for (int& i = it[v]; i < (int)g[v].size(); i++) {
      int id = g[v][i]; int w = e[id].to;
      if (e[id].cap > 0 && level[w] == level[v] + 1) {
        int d = dfs(w, t, min(f, e[id].cap));
        if (d > 0) { e[id].cap -= d; e[id ^ 1].cap += d; return d; }
      }
    }
    return 0;
  }
  long long maxflow(int s, int t) {
    long long flow = 0;
    while (bfs(s, t)) { fill(it.begin(), it.end(), 0); int f; while ((f = dfs(s, t, INT_MAX)) > 0) flow += f; }
    return flow;
  }
};

int main(int argc, char** argv) {
  if (argc < 4) { fprintf(stderr, "usage: D L monomials\n"); return 1; }
  if (mul(Word{3}, Word{1}) != Word({1, 4})) { fprintf(stderr, "relation fail\n"); return 3; }
  int D = atoi(argv[1]), L = atoi(argv[2]);
  vector<Word> S; { string spec = argv[3]; stringstream ss(spec); string mono;
    while (getline(ss, mono, ';')) { Word w; stringstream ms(mono); string lt; while (getline(ms, lt, ',')) w.push_back((uint8_t)stoi(lt));
      if (!is_sorted(w.begin(), w.end())) { fprintf(stderr, "monomial not in normal form\n"); return 1; } S.push_back(w); } }
  auto t0 = chrono::steady_clock::now();
  vector<Word> U; Word cur(D, 0);
  function<void(int, int)> rec = [&](int pos, int lo) {
    if (pos == D) { U.push_back(cur); return; }
    for (int v = lo; v <= L; v++) { cur[pos] = (uint8_t)v; rec(pos + 1, v); }
  };
  rec(0, 0);
  int nU = U.size(); size_t nS = S.size();
  unordered_map<Key, int, KeyHash> tidx; tidx.reserve((size_t)nU * nS);
  vector<int> adj((size_t)nU * nS);
  for (int y = 0; y < nU; y++) for (size_t s = 0; s < nS; s++) {
    Key k = key_of(mul(S[s], U[y]));
    auto itr = tidx.find(k); int id;
    if (itr == tidx.end()) { id = tidx.size(); tidx.emplace(k, id); } else id = itr->second;
    adj[(size_t)y * nS + s] = id;
  }
  int nT = tidx.size();
  Dinic dn(2 + nU + nT); int src = 0, snk = 1;
  for (int y = 0; y < nU; y++) dn.add(src, 2 + y, 2);
  for (int y = 0; y < nU; y++) for (size_t s = 0; s < nS; s++) dn.add(2 + y, 2 + nU + adj[(size_t)y * nS + s], 1 << 29);
  for (int t = 0; t < nT; t++) dn.add(2 + nU + t, snk, 1);
  long long flow = dn.maxflow(src, snk);
  bool found = flow < 2LL * nU;
  long long ny = 0, nt = 0;
  vector<char> inY(nU, 0);
  if (found) {
    vector<char> seen(2 + nU + nT, 0); deque<int> dq{src}; seen[src] = 1;
    while (!dq.empty()) { int v = dq.front(); dq.pop_front();
      for (int id : dn.g[v]) if (dn.e[id].cap > 0 && !seen[dn.e[id].to]) { seen[dn.e[id].to] = 1; dq.push_back(dn.e[id].to); } }
    for (int y = 0; y < nU; y++) { inY[y] = seen[2 + y]; ny += inY[y]; }
    vector<char> hit(nT, 0);
    for (int y = 0; y < nU; y++) if (inY[y]) for (size_t s = 0; s < nS; s++) { int t = adj[(size_t)y * nS + s]; if (!hit[t]) { hit[t] = 1; nt++; } }
    if (ny == 0 || !(nt < 2 * ny)) { fprintf(stderr, "inconsistent cut: ny=%lld nt=%lld\n", ny, nt); return 4; }
    const char* cert = getenv("CERT");
    if (cert) { FILE* f = fopen(cert, "w");
      for (int y = 0; y < nU; y++) if (inY[y]) { for (int z = 0; z < D; z++) fprintf(f, "%s%d", z ? "," : "", U[y][z]); fprintf(f, "\n"); }
      fclose(f); }
  }
  double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
  printf("{\"D\":%d,\"L\":%d,\"nS\":%zu,\"U\":%d,\"SU\":%d,\"maxflow\":%lld,\"found\":%s,\"Y\":%lld,\"SY\":%lld,\"seconds\":%.2f}\n",
         D, L, nS, nU, nT, flow, found ? "true" : "false", ny, nt, secs);
  return 0;
}
