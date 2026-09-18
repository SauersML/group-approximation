// Interleaved, lifted uniform certificate for the peeling links of VR(Z^n, d_1; r)  (version 2).
// Lmax = { x : |x|_1 <= r, x > 0 }.  Boxes with b_n >= 1: every dominator lies in hull(0, x, e_n).
// Phase A : balanced sphere points, Lemma 4 dominator (valid against any current set).  Q = unbalanced sphere points.
// Phase A': rounds over Q: x in Q deleted by a slack-one y in hull(0,x) (Lemma B: bad z are sphere points) if no alive
//           z in Q has |z-x| <= r < |z-y|.  Sequential, so each move is checked against the exact current sphere set.
// Phase B : rho = r-1 .. 2; x with |x| = rho, candidates w in hull(0,x,e_n), w > 0, w != x, alive.
//           Current set = (alive points of norm > rho: the list HI) + (points of norm <= rho, treated as all present).
//           Bulk test (sound): no z in Z^n with |z-w|-|z| >= r+1-rho and |z-w|-|z-x| >= 1 (separable DP).
//           List test: no z in HI with |z-x| <= r < |z-w|.   Kept points form H.
// Phase C : bitset greedy D-moves on C = alive Q + H + {e_i}, dominators in hull(0,x,e_n), decreasing-norm passes.
// Usage: ./ilv2 n r [certfile|-] [maxC=60000]
#include <bits/stdc++.h>
using namespace std;
typedef array<int8_t, 12> Pt;
int n, R;
static inline int d1(const Pt& a, const Pt& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
static inline int nr(const Pt& a) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); return s; }
static inline bool inhull3(const Pt& w, const Pt& x, const Pt& y) { for (int i = 0; i < n; i++) { int lo = min({0, (int)x[i], (int)y[i]}), hi = max({0, (int)x[i], (int)y[i]}); if (w[i] < lo || w[i] > hi) return false; } return true; }
bool balS(const vector<int>& x, const vector<int>& y) { int s = x.size();
  for (int m = 0; m < (1 << s); m++) { long long a = 0, b = 0; for (int i = 0; i < s; i++) { int g = (m >> i & 1) ? 1 : -1; a += g * x[i]; b += g * y[i]; } if (!((0 <= b && b <= a) || (a <= b && b <= 0))) return false; } return true; }
vector<int> balY(const vector<int>& x) { int s = x.size(), N = 0; for (int v : x) N += v; vector<int> y(s), res; bool f = false;
  function<void(int, int)> rec = [&](int i, int used) { if (f) return; if (i == s) { if (used > 0 && balS(x, y)) { f = true; res = y; } return; }
    for (int v = 0; v <= x[i] && used + v <= N / 2; v++) { y[i] = v; rec(i + 1, used + v); if (f) return; } };
  rec(0, 0); return res; }
map<vector<int>, pair<bool, vector<int>>> cacheB;
bool slack1(const Pt& x, const Pt& y) { // <sg,|y|> <= max(1,<sg,|x|>) for all sg over supp x
  int idx[12], s = 0; for (int i = 0; i < n; i++) if (x[i]) idx[s++] = i;
  for (int m = 0; m < (1 << s); m++) { int a = 0, b = 0; for (int t = 0; t < s; t++) { int g = (m >> t & 1) ? 1 : -1; a += g * abs(x[idx[t]]); b += g * abs(y[idx[t]]); } if (b > max(1, a)) return false; } return true; }
// Pareto pairs per coordinate: (x_i, w_i) -> list of (a,b) = (|z-w|-|z|, |z-w|-|z-x|), z in Z
vector<pair<int,int>> par[64][64];
void buildPar() { for (int xi = -R; xi <= R; xi++) for (int wi = -R; wi <= R; wi++) { vector<pair<int,int>> all;
    for (int z = -R - 3; z <= R + 3; z++) all.push_back({abs(z - wi) - abs(z), abs(z - wi) - abs(z - xi)});
    sort(all.begin(), all.end()); all.erase(unique(all.begin(), all.end()), all.end());
    vector<pair<int,int>> pf; for (auto& p : all) { bool dom = false; for (auto& q : all) if (q != p && q.first >= p.first && q.second >= p.second) { dom = true; break; } if (!dom) pf.push_back(p); }
    par[xi + R][wi + R] = pf; } }
// exists z with sum a >= T and sum b >= 1 ?
bool bulkBad(const Pt& x, const Pt& w, int T) { // DP over sum a in [-(n*R).. n*R] offset
  const int OFF = 12 * 40 + 5, SZ = 2 * OFF + 1; static int best[2][2 * (12 * 40 + 5) + 1]; int cur = 0;
  for (int s = 0; s < SZ; s++) best[cur][s] = INT_MIN; best[cur][OFF] = 0;
  int lo = OFF, hi = OFF;
  for (int i = 0; i < n; i++) { auto& pf = par[x[i] + R][w[i] + R]; int nx = cur ^ 1; int nlo = INT_MAX, nhi = INT_MIN;
    for (int s = lo - R - 1; s <= hi + R + 1; s++) if (s >= 0 && s < SZ) best[nx][s] = INT_MIN;
    for (int s = lo; s <= hi; s++) if (best[cur][s] != INT_MIN) for (auto& p : pf) { int t = s + p.first; int v = best[cur][s] + p.second; if (v > best[nx][t]) best[nx][t] = v; nlo = min(nlo, t); nhi = max(nhi, t); }
    cur = nx; lo = nlo; hi = nhi; }
  for (int s = max(lo, OFF + T); s <= hi; s++) if (best[cur][s] >= 1) return true; return false; }
FILE* cert = nullptr;
static void pr(FILE* f, const Pt& a) { for (int i = 0; i < n; i++) fprintf(f, "%d ", a[i]); }
long long enc(const Pt& v) { long long e = 0; for (int i = 0; i < n; i++) e = e * (2 * R + 1) + (v[i] + R); return e; }
int main(int argc, char** argv) {
  n = atoi(argv[1]); R = atoi(argv[2]); if (argc > 3 && string(argv[3]) != "-") cert = fopen(argv[3], "w");
  long long maxC = argc > 4 ? atoll(argv[4]) : 60000; buildPar();
  vector<Pt> P; { Pt x{}; function<void(int, int, bool)> gen = [&](int i, int rem, bool started) {
      if (i < 0) { if (started) P.push_back(x); return; }
      int lo = started ? -rem : 0; for (int v = lo; v <= rem; v++) { x[i] = v; gen(i - 1, rem - abs(v), started || v != 0); } x[i] = 0; };
    gen(n - 1, R, false); }
  int N = P.size(); vector<int> nrm(N); for (int i = 0; i < N; i++) nrm[i] = nr(P[i]);
  unordered_map<long long, int> id; id.reserve(N * 2); for (int i = 0; i < N; i++) id[enc(P[i])] = i;
  vector<char> alive(N, 1);
  auto isAlive = [&](const Pt& w) { auto it = id.find(enc(w)); return it != id.end() && alive[it->second]; };
  // Phase A
  vector<int> Q; long long nA = 0;
  for (int t = 0; t < N; t++) { if (nrm[t] != R) continue; auto& x = P[t];
    vector<pair<int, int>> mag; for (int i = 0; i < n; i++) if (x[i]) mag.push_back({abs(x[i]), i});
    sort(mag.begin(), mag.end(), [](auto& a, auto& b) { return a.first > b.first; }); vector<int> p; for (auto& q : mag) p.push_back(q.first);
    auto it = cacheB.find(p); if (it == cacheB.end()) { auto y = balY(p); it = cacheB.emplace(p, make_pair(!y.empty(), y)).first; }
    if (!it->second.first) { Q.push_back(t); continue; }
    auto& y = it->second.second; Pt u{}; int k = -1; for (int i = 0; i < n; i++) if (x[i]) k = i;
    for (size_t s = 0; s < mag.size(); s++) { int i = mag[s].second; u[i] = (x[i] > 0 ? 1 : -1) * y[s]; }
    if (u[k] < 1) for (int i = 0; i < n; i++) u[i] = x[i] - u[i];
    alive[t] = 0; nA++; if (cert) { fprintf(cert, "A "); pr(cert, x); fprintf(cert, "| "); pr(cert, u); fprintf(cert, "\n"); } }
  fprintf(stderr, "n=%d r=%d |Lmax|=%d balanced=%lld |Q|=%zu\n", n, R, N, nA, Q.size());
  // Phase A'
  long long nA2 = 0; { bool ch = true; int rd = 0;
    while (ch) { ch = false; rd++; long long del = 0;
      for (int t : Q) { if (!alive[t]) continue; auto& x = P[t]; Pt y{}; bool done = false;
        function<void(int)> rec = [&](int i) { if (done) return; if (i < 0) { int s = 0, last = 0; for (int j = 0; j < n; j++) { s += abs(y[j]); if (y[j]) last = y[j]; }
            if (last <= 0 || s == 0 || s == R || !slack1(x, y)) return;
            for (int z : Q) if (alive[z] && z != t && d1(P[z], x) <= R && d1(P[z], y) > R) return;
            done = true; alive[t] = 0; nA2++; del++; ch = true; if (cert) { fprintf(cert, "S "); pr(cert, x); fprintf(cert, "| "); pr(cert, y); fprintf(cert, "\n"); } return; }
          int lo = min(0, (int)x[i]), hi = max(0, (int)x[i]); for (int v = lo; v <= hi && !done; v++) { y[i] = v; rec(i - 1); } y[i] = 0; };
        rec(n - 1); }
      fprintf(stderr, "phase A' round %d: deleted %lld\n", rd, del); } }
  vector<int> Qa; for (int t : Q) if (alive[t]) Qa.push_back(t);
  fprintf(stderr, "after A': sphere alive %zu\n", Qa.size());
  // Phase B
  vector<int> H; long long nB = 0; Pt EN{}; EN[n - 1] = 1;
  vector<vector<int>> byN(R + 1); for (int i = 0; i < N; i++) byN[nrm[i]].push_back(i);
  for (int rho = R - 1; rho >= 2; rho--) {
    vector<int> HI; for (int i = 0; i < N; i++) if (alive[i] && nrm[i] > rho) HI.push_back(i);
    long long del = 0, kept = 0;
    for (int t : byN[rho]) { auto& x = P[t];
      vector<int> near; for (int z : HI) if (d1(P[z], x) <= R) near.push_back(z);
      // candidates
      vector<Pt> C; Pt w{}; function<void(int)> rec = [&](int i) { if (i < 0) { int last = 0; for (int j = 0; j < n; j++) if (w[j]) last = w[j]; if (last <= 0 || w == x) return; if (nrm[id[enc(w)]] >= rho && !isAlive(w)) return; C.push_back(w); return; }
        int lo = min(0, (int)x[i]), hi = max(0, (int)x[i]); if (i == n - 1) hi = max(hi, 1); for (int v = lo; v <= hi; v++) { w[i] = v; rec(i - 1); } w[i] = 0; };
      rec(n - 1);
      sort(C.begin(), C.end(), [&](const Pt& a, const Pt& b) { int da = d1(a, x), db = d1(b, x); if (da != db) return da < db; return nr(a) < nr(b); });
      int found = -1;
      for (size_t c = 0; c < C.size(); c++) { if (d1(C[c], x) > R) continue; if (bulkBad(x, C[c], R + 1 - rho)) continue;
        bool ok = true; for (int z : near) if (d1(P[z], C[c]) > R) { ok = false; break; } if (ok) { found = c; break; } }
      if (found < 0) { H.push_back(t); kept++; continue; }
      alive[t] = 0; nB++; del++; if (cert) { fprintf(cert, "B "); pr(cert, x); fprintf(cert, "| "); pr(cert, C[found]); fprintf(cert, "\n"); } }
    fprintf(stderr, "phase B rho=%d: |HI|=%zu deleted %lld kept %lld\n", rho, HI.size(), del, kept); }
  // Phase C
  vector<int> Cset; for (int i = 0; i < N; i++) if (alive[i]) Cset.push_back(i);
  int M = Cset.size(); if (M > maxC) { printf("n=%d r=%d |C|=%d too large for phase C\n", n, R, M); return 2; }
  vector<Pt> Pc(M); for (int i = 0; i < M; i++) Pc[i] = P[Cset[i]];
  int W = (M + 63) / 64; vector<uint64_t> B((size_t)M * W, 0); auto row = [&](int i) { return &B[(size_t)i * W]; };
  for (int i = 0; i < M; i++) { row(i)[i / 64] |= 1ULL << (i % 64); for (int j = i + 1; j < M; j++) if (d1(Pc[i], Pc[j]) <= R) { row(i)[j / 64] |= 1ULL << (j % 64); row(j)[i / 64] |= 1ULL << (i % 64); } }
  vector<uint64_t> mask(W, 0); for (int j = 0; j < M; j++) mask[j / 64] |= 1ULL << (j % 64);
  vector<char> al(M, 1); int left = M; vector<int> nm(M); for (int i = 0; i < M; i++) nm[i] = nr(Pc[i]);
  vector<int> ord(M); iota(ord.begin(), ord.end(), 0); stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return nm[a] > nm[b]; });
  auto get = [&](int i, int j) { return (row(i)[j / 64] >> (j % 64)) & 1; };
  int en = -1; for (int i = 0; i < M; i++) if (Pc[i] == EN) en = i;
  int pass = 0; bool changed = true; long long nC = 0;
  vector<int> byNorm(M); iota(byNorm.begin(), byNorm.end(), 0); stable_sort(byNorm.begin(), byNorm.end(), [&](int a, int b) { return nm[a] < nm[b]; });
  while (changed && left > 1) { changed = false; pass++;
    for (int u : ord) { if (!al[u] || left <= 1) continue; uint64_t* ru = row(u); int wf = -1;
      for (int w : byNorm) { if (w == u || !al[w] || !get(u, w) || !inhull3(Pc[w], Pc[u], EN)) continue;
        uint64_t* rw = row(w); bool ok = true; for (int k = 0; k < W; k++) if (ru[k] & mask[k] & ~rw[k]) { ok = false; break; }
        if (ok) { wf = w; break; } }
      if (wf < 0) continue;
      if (cert) { fprintf(cert, "D "); pr(cert, Pc[u]); fprintf(cert, "| "); pr(cert, Pc[wf]); fprintf(cert, "\n"); }
      al[u] = 0; mask[u / 64] &= ~(1ULL << (u % 64)); left--; changed = true; nC++; }
    vector<int> h(R + 1, 0); for (int i = 0; i < M; i++) if (al[i]) h[nm[i]]++;
    fprintf(stderr, "phase C pass %d: left %d by norm:", pass, left); for (int k = 1; k <= R; k++) fprintf(stderr, " %d", h[k]); fprintf(stderr, "\n"); }
  bool okEnd = left == 1 && en >= 0 && al[en];
  printf("n=%d r=%d |Lmax|=%d A=%lld S=%lld B=%lld |C|=%d D=%lld left=%d %s\n", n, R, N, nA, nA2, nB, M, nC, left, okEnd ? "REACHES {e_n}" : "STUCK");
  if (argc > 5) { FILE* f = fopen(argv[5], "w"); for (int i = 0; i < M; i++) if (al[i]) { for (int k = 0; k < n; k++) fprintf(f, "%d ", Pc[i][k]); fprintf(f, "\n"); } fclose(f); }
  if (!okEnd) { int sh = 0; for (int i = 0; i < M && sh < 10; i++) if (al[i]) { sh++; printf("  stuck "); for (int k = 0; k < n; k++) printf("%d ", Pc[i][k]); printf("\n"); } }
  if (cert) fclose(cert);
  return okEnd ? 0 : 1;
}
