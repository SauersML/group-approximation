// Greatest fixed point of the relaxed domination operator on Lmax_k = { x in Z^k : |x|_1 <= r, x > 0 }.
// K starts as Lmax_k.  A point x in K is removed when some w in hull(0, x, e_k) ∩ Lmax_k, w != x, satisfies
// N[x] ∩ K ⊆ N[w]  (w need NOT be in K).  Removal in place is sound by monotonicity.  At the end, K is a set that no
// sequence of (D) moves starting from Lmax_k can ever touch: at the first deletion of a point x of K the current set
// contains K, so N[x] ∩ C ⊄ N[w] for every admissible w.  Hence: K != {e_k}  =>  no (D)-only certificate ends at {e_k}.
// Every "blocked" verdict comes with an explicit blocker z in K with d(z,x) <= r < d(z,w), re-checked before reuse.
// Usage: ./gfp k r [outfile] [startfile]   (outfile: the points of K, one per line; startfile: initial K, default Lmax_k.
// The obstruction only needs the final K to be self-blocked, so any start set is sound; e_k is always added.)
#include <bits/stdc++.h>
using namespace std;
int n, R; vector<long long> cnt[13], off; vector<uint64_t> pres;
static inline long long& OFF(int i, int b, int v) { return off[((size_t)i * (R + 1) + b) * (2 * R + 1) + v + R]; }
static inline long long idx(const int* z) { long long e = 0; int b = R; for (int i = n - 1; i >= 0; i--) { e += OFF(i, b, z[i]); b -= abs(z[i]); } return e; }
static inline bool getb(long long e) { return (pres[e >> 6] >> (e & 63)) & 1; }
static inline void setb(long long e, bool on) { if (on) pres[e >> 6] |= 1ULL << (e & 63); else pres[e >> 6] &= ~(1ULL << (e & 63)); }
static int nr(const int* a) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); return s; }
static int d1(const int* a, const int* b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
static int layer(const int* a) { for (int i = n - 1; i >= 0; i--) if (a[i]) return i; return -1; }
static bool isPos(const int* a) { int L = layer(a); return L >= 0 && a[L] > 0; }
// DFS for a blocker z in K: d(z,x) <= R < d(z,w).
const int *X, *W; int Z[12], sufW[13], sufXW[13], HZ[12]; bool hit; long long nodes = 0;
static void rec(int i, int pz, int px, int pw) {
  if (hit) return; nodes++;
  if (i < 0) { if (pw >= R + 1 && isPos(Z) && getb(idx(Z))) { hit = true; memcpy(HZ, Z, sizeof(Z)); } return; }
  int b = R - pz;
  for (int v = -b; v <= b; v++) { int npx = px + abs(v - X[i]); if (npx > R) continue; int npz = pz + abs(v), npw = pw + abs(v - W[i]);
    if (npw + min(R - npz + sufW[i], R - npx + sufXW[i]) < R + 1) continue;
    Z[i] = v; rec(i - 1, npz, npx, npw); if (hit) break; }
  Z[i] = 0; }
static bool blocker(const int* x, const int* w) { X = x; W = w;
  sufW[0] = sufXW[0] = 0; for (int i = 0; i < n; i++) { sufW[i + 1] = sufW[i] + abs(w[i]); sufXW[i + 1] = sufXW[i] + abs(x[i] - w[i]); }
  hit = false; for (int i = 0; i < n; i++) Z[i] = 0; rec(n - 1, 0, 0, 0); return hit; }
int main(int argc, char** argv) {
  n = atoi(argv[1]); R = atoi(argv[2]);
  for (int i = 0; i <= n; i++) cnt[i].assign(R + 1, 0); for (int b = 0; b <= R; b++) cnt[0][b] = 1;
  for (int i = 1; i <= n; i++) for (int b = 0; b <= R; b++) { long long s = 0; for (int v = -b; v <= b; v++) s += cnt[i - 1][b - abs(v)]; cnt[i][b] = s; }
  off.assign((size_t)n * (R + 1) * (2 * R + 1), 0);
  for (int i = 0; i < n; i++) for (int b = 0; b <= R; b++) { long long s = 0; for (int v = -b; v <= b; v++) { OFF(i, b, v) = s; s += cnt[i][b - abs(v)]; } }
  long long tot = cnt[n][R]; pres.assign(tot / 64 + 1, 0);
  vector<array<signed char, 12>> P;  // points of Lmax, ordered by decreasing norm
  { int z[12] = {0}; function<void(int, int)> gen = [&](int i, int rem) { if (i < 0) { if (isPos(z)) { array<signed char, 12> a{}; for (int t = 0; t < n; t++) a[t] = z[t]; P.push_back(a); } return; }
      for (int v = -rem; v <= rem; v++) { z[i] = v; gen(i - 1, rem - abs(v)); } z[i] = 0; }; gen(n - 1, R); }
  // check ranking is a bijection on the ball
  { vector<uint64_t> seen(tot / 64 + 1, 0); long long c = 0; int z[12] = {0};
    function<void(int, int)> gen = [&](int i, int rem) { if (i < 0) { long long e = idx(z); if (e < 0 || e >= tot || ((seen[e >> 6] >> (e & 63)) & 1)) { printf("ranking not a bijection\n"); exit(1); } seen[e >> 6] |= 1ULL << (e & 63); c++; return; }
      for (int v = -rem; v <= rem; v++) { z[i] = v; gen(i - 1, rem - abs(v)); } z[i] = 0; }; gen(n - 1, R); if (c != tot) { printf("ball count mismatch\n"); exit(1); } }
  auto key = [&](const array<signed char, 12>& a) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); return s; };
  stable_sort(P.begin(), P.end(), [&](const auto& a, const auto& b) { return key(a) > key(b); });
  vector<char> in(P.size(), 1);
  if (argc > 4) { vector<uint64_t> st(tot / 64 + 1, 0); FILE* f = fopen(argv[4], "r"); int z[12] = {0}; long long c = 0;
    while (true) { bool ok = true; for (int i = 0; i < n; i++) if (fscanf(f, "%d", &z[i]) != 1) { ok = false; break; } if (!ok) break;
      if (nr(z) <= R) { long long e = idx(z); st[e >> 6] |= 1ULL << (e & 63); c++; } }
    fclose(f); printf("start set read: %lld points\n", c);
    for (size_t t = 0; t < P.size(); t++) { int zz[12] = {0}; for (int i = 0; i < n; i++) zz[i] = P[t][i]; long long e = idx(zz);
      bool ek = (layer(zz) == n - 1 && zz[n - 1] == 1 && nr(zz) == 1); in[t] = ek || ((st[e >> 6] >> (e & 63)) & 1); } }
  long long alive = 0; for (size_t t = 0; t < P.size(); t++) if (in[t]) { int z[12]; for (int i = 0; i < n; i++) z[i] = P[t][i]; setb(idx(z), 1); alive++; }
  printf("initial |K| = %lld\n", alive); printf("k=%d r=%d |Lmax|=%zu\n", n, R, P.size()); fflush(stdout);
  vector<vector<int>> cache(P.size());  // cached blocker rank per candidate
  auto t0 = chrono::steady_clock::now();
  bool changed = true; int pass = 0;
  while (changed) { changed = false; pass++; long long rem = 0, recheck = 0;
    for (size_t t = 0; t < P.size(); t++) { if (!in[t]) continue; int x[12] = {0}; for (int i = 0; i < n; i++) x[i] = P[t][i];
      // candidates w in hull(0,x,e_k) ∩ Lmax, w != x, d(x,w) <= R  (fixed order)
      vector<array<int, 12>> C; array<int, 12> w{};
      function<void(int)> g = [&](int i) { if (i < 0) { if (!isPos(w.data()) || nr(w.data()) > R) return; int d = d1(w.data(), x); if (d == 0 || d > R) return; C.push_back(w); return; }
        int lo = min(0, x[i]), hi = max(0, x[i]); if (i == n - 1) hi = max(hi, 1); for (int v = lo; v <= hi; v++) { w[i] = v; g(i - 1); } w[i] = 0; };
      g(n - 1);
      auto& cc = cache[t]; bool fresh = cc.empty(); if (fresh) cc.assign(C.size(), -1);
      bool allBlocked = true;
      for (size_t c = 0; c < C.size(); c++) {
        if (cc[c] >= 0 && getb(cc[c])) { recheck++; continue; }
        if (blocker(x, C[c].data())) { cc[c] = (int)idx(HZ); continue; }
        allBlocked = false; break; }
      if (!allBlocked) { in[t] = 0; setb(idx(x), 0); alive--; rem++; changed = true; vector<int>().swap(cc); } }
    double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    printf("pass %d: removed %lld, |K| = %lld, cached rechecks %lld, dfs nodes %lld, t=%.0fs\n", pass, rem, alive, recheck, nodes, el); fflush(stdout); }
  // summary by norm and orbit type
  map<int, long long> byNorm; map<vector<int>, long long> byType;
  FILE* out = argc > 3 ? fopen(argv[3], "w") : nullptr;
  for (size_t t = 0; t < P.size(); t++) if (in[t]) { int s = 0, L = -1; for (int i = 0; i < n; i++) { s += abs(P[t][i]); if (P[t][i]) L = i; }
      byNorm[s]++; vector<int> ty = {s, L, P[t][L]}; vector<int> v; for (int i = 0; i < L; i++) v.push_back(abs(P[t][i])); sort(v.rbegin(), v.rend()); ty.insert(ty.end(), v.begin(), v.end()); byType[ty]++;
      if (out) { for (int i = 0; i < n; i++) fprintf(out, "%d ", P[t][i]); fprintf(out, "\n"); } }
  if (out) fclose(out);
  printf("K by norm:"); for (auto& [a, b] : byNorm) printf(" %d:%lld", a, b); printf("\n");
  printf("K orbit types (norm, layer, last, sorted |lower|): %zu\n", byType.size()); int sh = 0;
  vector<pair<long long, vector<int>>> ts; for (auto& [a, b] : byType) ts.push_back({b, a}); sort(ts.rbegin(), ts.rend());
  for (auto& [b, a] : ts) { if (sh++ >= 20) break; printf("  ("); for (size_t i = 0; i < a.size(); i++) printf("%d%s", a[i], i + 1 < a.size() ? "," : ""); printf(") x%lld\n", b); }
  int ek[12] = {0}; ek[n - 1] = 1;
  printf("RESULT k=%d r=%d |K|=%lld %s\n", n, R, alive, (alive == 1 && getb(idx(ek))) ? "K = {e_k}: no obstruction" : "K != {e_k}: NO (D)-only certificate exists");
}
