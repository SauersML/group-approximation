// Level-by-level orbit certificate for Lmax_k = { x in Z^k : |x|_1 <= r, x > 0 }, with no enumeration of points.
// Layer of x: index j of its last nonzero coordinate; T_j = layer-j points of Lmax; H_j = signed permutations of
// coordinates 0..j-1.  Orbits of H_j on T_j are listed by canonical reps x[0] >= ... >= x[j-1] >= 0, x[j] >= 1.
// Levels m = r, r-1, ..., 2; at level m every point of norm > m is already deleted and every point of norm < m is present.
// A move "D x | w" (x of norm m, layer j) deletes the orbit H_j x; its dominator w must satisfy
//   w in hull(0, x, e_k) (coordinatewise box, last coordinate up to max(x_{k-1}, 1)), layer(w) >= j, |w| <= m-1, d(x,w) <= r,
// and d(z,w) <= r for every z in the superset S = H_j C with d(z,x) <= r.  S is covered by
//   (a) all z with |z| <= m-1 and (z > 0 or layer(z) < j)        -- exact DP over coordinates;
//   (b) for every orbit O of norm m that is still alive, the set H_j O   -- exact DP over signed assignments.
// Step 1 of a level uses (a) with |z| <= m in place of (a)+(b) (the level criterion; valid whatever is alive).
// Step 2 runs greedy passes over the orbits that step 1 left, using (a) + (b) against the orbits still alive.
// Norm 1: e_i (i < k-1) is dominated by e_{k-1}.
// lcs2: as lcs, with deferral (see main).  Usage: ./lcs2 k r [certfile|-] [maxCand=100000]
#include <bits/stdc++.h>
using namespace std;
int n, R; typedef array<int, 12> Pt;
static int nr(const Pt& a) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); return s; }
static int d1(const Pt& a, const Pt& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
static int layer(const Pt& a) { for (int i = n - 1; i >= 0; i--) if (a[i]) return i; return -1; }
long long testsA = 0, testsB = 0;
// max over z with 1 <= |z| <= M, (z > 0 or layer(z) < j), d(z,x) <= R, of d(z,w) is <= R ?
static bool okA(const Pt& x, const Pt& w, int M, int j) { testsA++;
  static vector<int> cur, nxt; int A = M + 1, B = R + 1; cur.assign(2 * A * B, -1); nxt.assign(2 * A * B, -1);
  auto id = [&](int s, int a, int b) { return (s * A + a) * B + b; };
  cur[id(0, 0, 0)] = 0;
  for (int i = n - 1; i >= 0; i--) { fill(nxt.begin(), nxt.end(), -1);
    for (int s = 0; s < 2; s++) for (int a = 0; a < A; a++) for (int b = 0; b < B; b++) { int c = cur[id(s, a, b)]; if (c < 0) continue;
      for (int v = -(M - a); v <= M - a; v++) {
        if (!s && i >= j && v < 0) continue;
        int nb = b + abs(v - x[i]); if (nb > R) continue; int na = a + abs(v), ns = s || v != 0;
        int nc = c + abs(v - w[i]); int& t = nxt[id(ns, na, nb)]; if (nc > t) t = nc; } }
    swap(cur, nxt); }
  int mx = -1; for (int a = 0; a < A; a++) for (int b = 0; b < B; b++) mx = max(mx, cur[id(1, a, b)]);
  return mx <= R; }
// max over z in H_P y (signed permutations of coordinates 0..P-1 of y), d(z,x) <= R, of d(z,w) is <= R ?
static bool okB(const Pt& y, int P, const Pt& x, const Pt& w) { testsB++;
  int b0 = 0, c0 = 0; for (int i = P; i < n; i++) { b0 += abs(y[i] - x[i]); c0 += abs(y[i] - w[i]); } if (b0 > R) return true;
  // quick lower bound on min d(z,x): match sorted |y| to sorted |x| on 0..P-1
  { vector<int> a, b; for (int i = 0; i < P; i++) { a.push_back(abs(y[i])); b.push_back(abs(x[i])); } sort(a.begin(), a.end()); sort(b.begin(), b.end());
    int lb = b0; for (int i = 0; i < P; i++) lb += abs(a[i] - b[i]); if (lb > R) return true; }
  int S = 1 << P, B = R + 1; vector<int> dp((size_t)S * B, -1); dp[0 * B + b0] = c0;
  for (int mask = 0; mask < S; mask++) { int i = __builtin_popcount(mask); if (i >= P) continue;
    for (int b = 0; b < B; b++) { int c = dp[(size_t)mask * B + b]; if (c < 0) continue;
      for (int t = 0; t < P; t++) { if (mask >> t & 1) continue; int v = y[t];
        for (int sg = 0; sg < (v ? 2 : 1); sg++) { int u = sg ? -v : v; int nb = b + abs(u - x[i]); if (nb > R) continue;
          int nc = c + abs(u - w[i]); int& q = dp[(size_t)(mask | 1 << t) * B + nb]; if (nc > q) q = nc; } } } }
  for (int b = 0; b < B; b++) if (dp[(size_t)(S - 1) * B + b] > R) return false;
  return true; }
static void pr(FILE* f, const Pt& a) { for (int i = 0; i < n; i++) fprintf(f, "%d ", a[i]); }
// Deferral.  D = orbits of norm > m that are still alive (deferred).  At level m:
//   step 1: each x of norm m with a w (|w| <= m-1) passing (a) with |z| <= m and (b) against D is deleted;
//   step 2: greedy passes over the rest of level m with (a) for |z| <= m-1 and (b) against D + the rest;
//   leftovers join D;  step 3: greedy passes over D with w of norm <= m-1, (a) for |z| <= m-1 and (b) against D.
// Everything of norm <= m-1 is present throughout level m, so (a) + (b) covers H_j C at every test.
struct Orb { Pt x; int j, m; bool alive; };
int main(int argc, char** argv) {
  n = atoi(argv[1]); R = atoi(argv[2]); FILE* cert = (argc > 3 && strcmp(argv[3], "-")) ? fopen(argv[3], "w") : nullptr;
  int maxCand = argc > 4 ? atoi(argv[4]) : 100000;
  auto t0 = chrono::steady_clock::now(); auto el = [&]() { return chrono::duration<double>(chrono::steady_clock::now() - t0).count(); };
  vector<Orb> O; vector<pair<int, Pt>> moves; vector<int> D; long long st[4] = {0, 0, 0, 0}; size_t maxD = 0;
  auto cands = [&](const Pt& x, int j, int M) { vector<Pt> C; Pt w{};
    function<void(int)> g = [&](int i) { if (i < 0) { if (layer(w) < j || nr(w) > M || d1(w, x) > R) return; C.push_back(w); return; }
      int lo = min(0, x[i]), hi = max(0, x[i]); if (i == n - 1) hi = max(hi, 1); for (int v = lo; v <= hi; v++) { w[i] = v; g(i - 1); } w[i] = 0; };
    g(n - 1);
    sort(C.begin(), C.end(), [&](const Pt& a, const Pt& b) { int ka = abs(2 * nr(a) - R), kb = abs(2 * nr(b) - R); if (ka != kb) return ka < kb; if (d1(a, x) != d1(b, x)) return d1(a, x) < d1(b, x); return a < b; });
    if ((int)C.size() > maxCand) C.resize(maxCand); return C; };
  auto okAll = [&](const Pt& x, int j, const Pt& w, const vector<int>& S) { for (int p : S) if (O[p].alive && !okB(O[p].x, max(O[p].j, j), x, w)) return false; return true; };
  auto del = [&](int q, const Pt& w, int s) { O[q].alive = false; moves.push_back({q, w}); st[s]++; };
  for (int m = R; m >= 2; m--) {
    vector<int> lev;
    for (int j = 0; j < n; j++) { Pt x{};
      function<void(int, int, int)> g3 = [&](int i, int rem, int mx) { if (i == j) { if (rem == 0) { O.push_back({x, j, m, true}); lev.push_back(O.size() - 1); } return; }
        for (int v = 0; v <= min(rem, mx); v++) { x[i] = v; g3(i + 1, rem - v, v); } x[i] = 0; };
      for (int t = 1; t <= m; t++) { x = Pt{}; x[j] = t; g3(0, m - t, m); } }
    vector<int> rest;
    for (int q : lev) { bool done = false; for (auto& c : cands(O[q].x, O[q].j, m - 1)) if (okA(O[q].x, c, m, O[q].j) && okAll(O[q].x, O[q].j, c, D)) { del(q, c, 1); done = true; break; }
      if (!done) rest.push_back(q); }
    vector<int> S; bool changed = true;
    while (!rest.empty() && changed) { changed = false; S = D; S.insert(S.end(), rest.begin(), rest.end()); vector<int> nr2;
      for (int q : rest) { bool done = false; for (auto& c : cands(O[q].x, O[q].j, m - 1)) if (okA(O[q].x, c, m - 1, O[q].j) && okAll(O[q].x, O[q].j, c, S)) { del(q, c, 2); done = true; changed = true; break; }
        if (!done) nr2.push_back(q); }
      rest = nr2; }
    D.insert(D.end(), rest.begin(), rest.end());
    changed = true;
    while (!D.empty() && changed) { changed = false; vector<int> nd;
      for (int q : D) { if (!O[q].alive) continue; bool done = false;
        for (auto& c : cands(O[q].x, O[q].j, m - 1)) if (okA(O[q].x, c, m - 1, O[q].j) && okAll(O[q].x, O[q].j, c, D)) { del(q, c, 3); done = true; changed = true; break; }
        if (!done) nd.push_back(q); }
      D = nd; }
    maxD = max(maxD, D.size());
    fprintf(stderr, "m=%d orbits=%zu deferred=%zu t=%.0fs\n", m, lev.size(), D.size(), el());
  }
  bool ok = D.empty();
  if (!ok) { printf("STUCK: %zu deferred orbits left:", D.size()); int sh = 0; for (int q : D) { if (sh++ >= 12) break; printf(" [%d:", O[q].m); for (int i = 0; i < n; i++) printf(" %d", O[q].x[i]); printf("]"); } printf("\n"); }
  if (cert) { for (auto& [q, c] : moves) { fprintf(cert, "D "); pr(cert, O[q].x); fprintf(cert, "| "); pr(cert, c); fprintf(cert, "\n"); }
    if (ok) for (int i = 0; i + 1 < n; i++) { Pt e{}, f{}; e[i] = 1; f[n - 1] = 1; fprintf(cert, "D "); pr(cert, e); fprintf(cert, "| "); pr(cert, f); fprintf(cert, "\n"); }
    fclose(cert); }
  printf("k=%d r=%d orbits=%zu step1=%lld step2=%lld step3=%lld maxDeferred=%zu testsA=%lld testsB=%lld t=%.0fs %s\n", n, R, O.size(), st[1], st[2], st[3], maxD, testsA, testsB, el(), ok ? "REACHES {e_k}" : "STUCK");
  return ok ? 0 : 1; }
