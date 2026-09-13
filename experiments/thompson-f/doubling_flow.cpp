// Exact minimum of |S Y| / |Y| over nonempty Y inside a finite universe U of the positive
// monoid M = < x_0, x_1, ... | x_j x_i = x_i x_{j+1} (i < j) > of Thompson's group F.
//
// U = M_{D,L}: normal forms x_{i_1} ... x_{i_D}, i_1 <= ... <= i_D <= L.
// S = a finite set of normal forms (given on the command line).
//
// For integers K, J the network  source -K-> y -INF-> s y -J-> sink  has
//   min cut = min_{Y subset U} ( K (|U| - |Y|) + J |S Y| ),
// so  max_{Y} ( K |Y| - J |S Y| ) = K |U| - maxflow,  and the source side of a minimum
// cut attains it.  Dinkelbach iteration with K/J = current ratio gives the exact minimum.
//
// Usage: doubling_flow D L "0,0;0,1;..."   (monomials separated by ';', letters by ',')
// Output: one JSON line; with env CERT=path the optimal Y is written there (one word per line).
#include <bits/stdc++.h>
using namespace std;
typedef vector<uint8_t> Word;
typedef unsigned __int128 Key;

static Word left_mul_letter(int j, const Word& w) {
  Word out; out.reserve(w.size() + 1);
  size_t k = 0, n = w.size();
  while (k < n && w[k] < j) { out.push_back(w[k]); j++; k++; }
  if (j > 255) { fprintf(stderr, "letter overflow\n"); exit(2); }
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
  for (size_t i = 0; i < w.size(); i++) {
    if (w[i] > 63) { fprintf(stderr, "letter too large for key\n"); exit(2); }
    k |= (Key)w[i] << (8 + 6 * i);
  }
  return k;
}
struct KeyHash { size_t operator()(const Key& k) const {
  uint64_t lo = (uint64_t)k, hi = (uint64_t)(k >> 64);
  return std::hash<uint64_t>()(lo * 0x9E3779B97F4A7C15ULL ^ hi); } };

static void selftest() {
  for (int i = 0; i < 5; i++) for (int j = i + 1; j < 7; j++) {
    Word a = mul(Word{(uint8_t)j}, Word{(uint8_t)i});
    if (!(a.size() == 2 && a[0] == i && a[1] == j + 1)) { fprintf(stderr, "relation fail\n"); exit(3); }
  }
  mt19937 rng(7);
  for (int t = 0; t < 20000; t++) {
    Word w[3];
    for (int q = 0; q < 3; q++) { int len = rng() % 5; for (int z = 0; z < len; z++) w[q].push_back(rng() % 6); sort(w[q].begin(), w[q].end()); }
    if (mul(mul(w[0], w[1]), w[2]) != mul(w[0], mul(w[1], w[2]))) { fprintf(stderr, "assoc fail\n"); exit(3); }
  }
}

struct Dinic {
  struct E { int to; long long cap; };
  vector<E> e; vector<vector<int>> g; vector<int> level, it;
  Dinic(int n) : g(n), level(n), it(n) {}
  void add(int a, int b, long long c) { g[a].push_back(e.size()); e.push_back({b, c}); g[b].push_back(e.size()); e.push_back({a, 0}); }
  bool bfs(int s, int t) {
    fill(level.begin(), level.end(), -1); level[s] = 0; deque<int> q{s};
    while (!q.empty()) { int v = q.front(); q.pop_front();
      for (int id : g[v]) if (e[id].cap > 0 && level[e[id].to] < 0) { level[e[id].to] = level[v] + 1; q.push_back(e[id].to); } }
    return level[t] >= 0;
  }
  long long dfs(int v, int t, long long f) {
    if (v == t) return f;
    for (int& i = it[v]; i < (int)g[v].size(); i++) {
      int id = g[v][i]; int w = e[id].to;
      if (e[id].cap > 0 && level[w] == level[v] + 1) {
        long long d = dfs(w, t, min(f, e[id].cap));
        if (d > 0) { e[id].cap -= d; e[id ^ 1].cap += d; return d; }
      }
    }
    return 0;
  }
  long long maxflow(int s, int t) {
    long long flow = 0;
    while (bfs(s, t)) { fill(it.begin(), it.end(), 0); long long f; while ((f = dfs(s, t, LLONG_MAX)) > 0) flow += f; }
    return flow;
  }
};

int main(int argc, char** argv) {
  if (argc < 4) { fprintf(stderr, "usage: D L monomials\n"); return 1; }
  selftest();
  int D = atoi(argv[1]), L = atoi(argv[2]);
  vector<Word> S; { string spec = argv[3]; stringstream ss(spec); string mono;
    while (getline(ss, mono, ';')) { Word w; stringstream ms(mono); string lt; while (getline(ms, lt, ',')) w.push_back((uint8_t)stoi(lt));
      if (!is_sorted(w.begin(), w.end())) { fprintf(stderr, "monomial not in normal form\n"); return 1; } S.push_back(w); } }
  auto t0 = chrono::steady_clock::now();
  // enumerate U
  vector<Word> U; Word cur(D, 0);
  function<void(int, int)> rec = [&](int pos, int lo) {
    if (pos == D) { U.push_back(cur); return; }
    for (int v = lo; v <= L; v++) { cur[pos] = (uint8_t)v; rec(pos + 1, v); }
  };
  rec(0, 0);
  int nU = U.size();
  unordered_map<Key, int, KeyHash> tidx; tidx.reserve((size_t)nU * S.size());
  vector<int> adj(nU * S.size());
  for (int y = 0; y < nU; y++) for (size_t s = 0; s < S.size(); s++) {
    Word p = mul(S[s], U[y]); Key k = key_of(p);
    auto itr = tidx.find(k); int id;
    if (itr == tidx.end()) { id = tidx.size(); tidx.emplace(k, id); } else id = itr->second;
    adj[y * S.size() + s] = id;
  }
  int nT = tidx.size();
  // Dinkelbach
  long long p = nT, q = nU; int iters = 0; vector<char> inY(nU, 1);
  while (true) {
    iters++;
    long long gg = __gcd(p, q); long long K = p / gg, J = q / gg;
    Dinic dn(2 + nU + nT); int src = 0, snk = 1;
    for (int y = 0; y < nU; y++) dn.add(src, 2 + y, K);
    const long long INF = LLONG_MAX / 4;
    for (int y = 0; y < nU; y++) for (size_t s = 0; s < S.size(); s++) dn.add(2 + y, 2 + nU + adj[y * S.size() + s], INF);
    for (int t = 0; t < nT; t++) dn.add(2 + nU + t, snk, J);
    long long flow = dn.maxflow(src, snk);
    long long val = K * (long long)nU - flow;
    if (val <= 0) break;
    // source side of the min cut
    vector<char> seen(2 + nU + nT, 0); deque<int> dq{src}; seen[src] = 1;
    while (!dq.empty()) { int v = dq.front(); dq.pop_front();
      for (int id : dn.g[v]) if (dn.e[id].cap > 0 && !seen[dn.e[id].to]) { seen[dn.e[id].to] = 1; dq.push_back(dn.e[id].to); } }
    long long ny = 0, nt = 0;
    for (int y = 0; y < nU; y++) { inY[y] = seen[2 + y]; ny += inY[y]; }
    // recount |S Y| directly, independently of the network
    vector<char> hit(nT, 0);
    for (int y = 0; y < nU; y++) if (inY[y]) for (size_t s = 0; s < S.size(); s++) { int t = adj[y * S.size() + s]; if (!hit[t]) { hit[t] = 1; nt++; } }
    if (ny == 0 || !(nt * q < p * ny)) { fprintf(stderr, "Dinkelbach step did not improve: ny=%lld nt=%lld\n", ny, nt); return 4; }
    p = nt; q = ny;
  }
  double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
  const char* cert = getenv("CERT");
  // write the optimal Y when asked for all runs, or when it beats ratio 2
  if (cert && (getenv("CERT_ALL") || p < 2 * q)) { FILE* f = fopen(cert, "w");
    for (int y = 0; y < nU; y++) if (inY[y]) { for (int z = 0; z < D; z++) fprintf(f, "%s%d", z ? "," : "", U[y][z]); fprintf(f, "\n"); }
    fclose(f); }
  printf("{\"D\":%d,\"L\":%d,\"nS\":%zu,\"U\":%d,\"SU\":%d,\"min_ratio_num\":%lld,\"min_ratio_den\":%lld,\"min_ratio\":%.6f,\"iters\":%d,\"seconds\":%.1f}\n",
         D, L, S.size(), nU, nT, p, q, (double)p / q, iters, secs);
  return 0;
}
