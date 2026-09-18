// Lifted greedy D-move generator for Lmax_k = { x in Z^k : |x|_1 <= r, x > 0 }, exact tests by pruned DFS.
// Moves: D x | w with w alive, w != x, w in hull(0, x, e_k), d(x,w) <= r, and no alive z with d(z,x) <= r < d(z,w).
// Phase A: balanced sphere points deleted by their Lemma-4 dominator (valid against any current set; the verifier
//          re-checks).  Then greedy passes in decreasing norm over the alive points, each x tried against its
//          candidates (sphere: |2|w| - r| ascending; lower norms: d(w,x) ascending, then |w|), exact DFS test.
// State: presence bitmap indexed by a dense rank of the l^1 ball B_k(r).
// Usage: ./ilv4 k r certfile initfile|- outfile [budgetSec=1100] [maxCand=400]
//   initfile: start from this alive set (a previous outfile) instead of Lmax.  outfile: alive set at exit.
#include <bits/stdc++.h>
using namespace std;
typedef array<int8_t, 12> Pt;
int n, R; vector<long long> cnt[13]; vector<long long> off; // off[(i*(R+1)+b)*(2R+1)+v+R]
vector<uint64_t> pres;
static inline long long& OFF(int i, int b, int v) { return off[((size_t)i * (R + 1) + b) * (2 * R + 1) + v + R]; }
static inline bool getb(long long e) { return (pres[e >> 6] >> (e & 63)) & 1; }
static inline void setb(long long e, bool on) { if (on) pres[e >> 6] |= 1ULL << (e & 63); else pres[e >> 6] &= ~(1ULL << (e & 63)); }
static long long rk(const Pt& x) { long long e = 0; int b = R; for (int i = n - 1; i >= 0; i--) { e += OFF(i, b, x[i]); b -= abs(x[i]); } return e; }
static inline int d1(const Pt& a, const Pt& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
static inline int nr(const Pt& a) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); return s; }
static bool isPos(const Pt& a) { for (int i = n - 1; i >= 0; i--) if (a[i]) return a[i] > 0; return false; }
Pt X, W; int sufW[13], sufXW[13]; bool hit; long long nodes = 0, nodeCap = 0;
static void rec(int i, int pz, int px, int pw, long long e, bool started) {
  if (hit) return; nodes++; if (nodeCap && nodes > nodeCap) { hit = true; return; }
  if (i < 0) { if (started && pw >= R + 1 && getb(e)) hit = true; return; }
  int b = R - pz;
  for (int v = started ? -b : 0; v <= b; v++) {
    int npx = px + abs(v - X[i]); if (npx > R) continue; int npz = pz + abs(v), npw = pw + abs(v - W[i]);
    if (npw + min(R - npz + sufW[i], R - npx + sufXW[i]) < R + 1) continue;
    rec(i - 1, npz, npx, npw, e + OFF(i, b, v), started || v != 0); if (hit) return; } }
static bool dominated(const Pt& x, const Pt& w) { X = x; W = w; sufW[0] = sufXW[0] = 0;
  for (int i = 0; i < n; i++) { sufW[i + 1] = sufW[i] + abs(w[i]); sufXW[i + 1] = sufXW[i] + abs(x[i] - w[i]); }
  hit = false; rec(n - 1, 0, 0, 0, 0, false); return !hit; }
bool balS(const vector<int>& x, const vector<int>& y) { int s = x.size();
  for (int m = 0; m < (1 << s); m++) { long long a = 0, b = 0; for (int i = 0; i < s; i++) { int g = (m >> i & 1) ? 1 : -1; a += g * x[i]; b += g * y[i]; } if (!((0 <= b && b <= a) || (a <= b && b <= 0))) return false; } return true; }
vector<int> balY(const vector<int>& x) { int s = x.size(), N = 0; for (int v : x) N += v; vector<int> y(s), res; bool f = false;
  function<void(int, int)> go = [&](int i, int used) { if (f) return; if (i == s) { if (used > 0 && balS(x, y)) { f = true; res = y; } return; }
    for (int v = 0; v <= x[i] && used + v <= N / 2; v++) { y[i] = v; go(i + 1, used + v); if (f) return; } };
  go(0, 0); return res; }
static void pr(FILE* f, const Pt& a) { for (int i = 0; i < n; i++) fprintf(f, "%d ", a[i]); }
int main(int argc, char** argv) {
  n = atoi(argv[1]); R = atoi(argv[2]); FILE* cert = fopen(argv[3], "w"); string init = argv[4], outf = argv[5];
  double budget = argc > 6 ? atof(argv[6]) : 1100; int maxCand = argc > 7 ? atoi(argv[7]) : 400;
  auto t0 = chrono::steady_clock::now(); auto el = [&]() { return chrono::duration<double>(chrono::steady_clock::now() - t0).count(); };
  for (int i = 0; i <= n; i++) cnt[i].assign(R + 1, 0);
  for (int b = 0; b <= R; b++) cnt[0][b] = 1;
  for (int i = 1; i <= n; i++) for (int b = 0; b <= R; b++) { long long s = 0; for (int v = -b; v <= b; v++) s += cnt[i - 1][b - abs(v)]; cnt[i][b] = s; }
  off.assign((size_t)n * (R + 1) * (2 * R + 1), 0);
  for (int i = 0; i < n; i++) for (int b = 0; b <= R; b++) { long long s = 0; for (int v = -b; v <= b; v++) { OFF(i, b, v) = s; s += cnt[i][b - abs(v)]; } }
  long long tot = cnt[n][R]; pres.assign(tot / 64 + 1, 0);
  vector<Pt> P; { Pt x{}; function<void(int, int, bool)> gen = [&](int i, int rem, bool st) { if (i < 0) { if (st) P.push_back(x); return; }
      for (int v = st ? -rem : 0; v <= rem; v++) { x[i] = v; gen(i - 1, rem - abs(v), st || v != 0); } x[i] = 0; }; gen(n - 1, R, false); }
  int N = P.size(); vector<long long> rP(N); for (int i = 0; i < N; i++) rP[i] = rk(P[i]);
  { vector<long long> s(rP); sort(s.begin(), s.end()); if (adjacent_find(s.begin(), s.end()) != s.end()) { puts("rank collision"); return 3; } }
  vector<char> alive(N, 0); long long left = 0;
  if (init == "-") { for (int i = 0; i < N; i++) { alive[i] = 1; setb(rP[i], 1); } left = N; }
  else { unordered_map<long long, int> id; for (int i = 0; i < N; i++) id[rP[i]] = i; FILE* f = fopen(init.c_str(), "r"); Pt x{}; int v, k = 0;
    while (fscanf(f, "%d", &v) == 1) { x[k++] = v; if (k == n) { int t = id.at(rk(x)); alive[t] = 1; setb(rP[t], 1); left++; x = Pt{}; k = 0; } } fclose(f); }
  auto kill = [&](int t) { alive[t] = 0; setb(rP[t], 0); left--; };
  auto isAlive = [&](const Pt& w) { return nr(w) <= R && isPos(w) && getb(rk(w)); };
  fprintf(stderr, "k=%d r=%d |Lmax|=%d alive=%lld\n", n, R, N, left);
  // Phase A
  long long nA = 0; map<vector<int>, vector<int>> cacheB;
  for (int t = 0; t < N; t++) { if (!alive[t] || nr(P[t]) != R) continue; auto& x = P[t];
    vector<pair<int, int>> mag; for (int i = 0; i < n; i++) if (x[i]) mag.push_back({abs(x[i]), i});
    sort(mag.begin(), mag.end(), [](auto& a, auto& b) { return a.first > b.first; }); vector<int> p; for (auto& q : mag) p.push_back(q.first);
    auto it = cacheB.find(p); if (it == cacheB.end()) it = cacheB.emplace(p, balY(p)).first; if (it->second.empty()) continue;
    auto& y = it->second; Pt u{}; int k = -1; for (int i = 0; i < n; i++) if (x[i]) k = i;
    for (size_t s = 0; s < mag.size(); s++) { int i = mag[s].second; u[i] = (x[i] > 0 ? 1 : -1) * y[s]; }
    if (u[k] < 1) for (int i = 0; i < n; i++) u[i] = x[i] - u[i];
    if (!isAlive(u)) continue;
    fprintf(cert, "A "); pr(cert, x); fprintf(cert, "| "); pr(cert, u); fprintf(cert, "\n"); kill(t); nA++; }
  fprintf(stderr, "phase A: %lld, alive %lld, t=%.0fs\n", nA, left, el());
  vector<int> ord(N); iota(ord.begin(), ord.end(), 0); stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return nr(P[a]) > nr(P[b]); });
  long long nD = 0; bool changed = true, oot = false; int pass = 0;
  while (changed && left > 1 && !oot) { changed = false; pass++; long long del = 0;
    for (int t : ord) { if (!alive[t]) continue; if (el() > budget) { oot = true; break; } auto& x = P[t]; int nx = nr(x);
      vector<Pt> C; Pt w{}; function<void(int)> g = [&](int i) { if (i < 0) { if (w == x || !isPos(w) || d1(w, x) > R || !getb(rk(w))) return; C.push_back(w); return; }
        int lo = min(0, (int)x[i]), hi = max(0, (int)x[i]); if (i == n - 1) hi = max(hi, 1); for (int v = lo; v <= hi; v++) { w[i] = v; g(i - 1); } w[i] = 0; };
      g(n - 1);
      if (nx == R) sort(C.begin(), C.end(), [&](const Pt& a, const Pt& b) { int ka = abs(2 * nr(a) - R), kb = abs(2 * nr(b) - R); if (ka != kb) return ka < kb; return d1(a, x) < d1(b, x); });
      else sort(C.begin(), C.end(), [&](const Pt& a, const Pt& b) { int da = d1(a, x), db = d1(b, x); if (da != db) return da < db; return nr(a) < nr(b); });
      int tried = 0;
      for (auto& c : C) { if (++tried > maxCand) break; if (dominated(x, c)) { fprintf(cert, "D "); pr(cert, x); fprintf(cert, "| "); pr(cert, c); fprintf(cert, "\n"); kill(t); nD++; del++; changed = true; break; } } }
    vector<long long> h(R + 1, 0); for (int i = 0; i < N; i++) if (alive[i]) h[nr(P[i])]++;
    fprintf(stderr, "pass %d: deleted %lld, alive %lld, t=%.0fs, dfs %lld; by norm:", pass, del, left, el(), nodes); for (int k = 1; k <= R; k++) fprintf(stderr, " %lld", h[k]); fprintf(stderr, "\n"); }
  Pt EN{}; EN[n - 1] = 1; bool ok = left == 1 && isAlive(EN);
  printf("k=%d r=%d |Lmax|=%d A=%lld D=%lld alive=%lld %s%s\n", n, R, N, nA, nD, left, ok ? "REACHES {e_k}" : "STUCK", oot ? " (time budget)" : "");
  FILE* f = fopen(outf.c_str(), "w"); for (int i = 0; i < N; i++) if (alive[i]) { pr(f, P[i]); fprintf(f, "\n"); } fclose(f); fclose(cert);
  return ok ? 0 : 1; }
