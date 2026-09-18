// Hybrid orbit / point generator for lifted certificates on Lmax_k = { x in Z^k : |x|_1 <= r, x > 0 }.
// Exact current set C as a rank bitmap.  Chat = union of the H_L-orbits (L = layer) that still have an alive point;
// Chat contains C and satisfies invariant (I), so an equivariant move x | w tested against H_j Chat is valid for every
// alive point of H_j x (Lemma O with Chat), provided H_j w is fully alive and disjoint from H_j x.
// When no equivariant w exists, each alive point p of the orbit is tried by a point move p | w, tested exactly against C.
// Levels m = r..1; orbits failing at their level are deferred and retried at lower levels.
// Output: point-level lines "D p | w" (for vcert2).  Usage: ./hyb k r certfile [maxCand=400] [budget=1100]
#include <bits/stdc++.h>
using namespace std;
typedef array<int, 12> Pt;
int n, R; vector<long long> cnt[13], off; vector<uint64_t> pres;
static inline long long& OFF(int i, int b, int v) { return off[((size_t)i * (R + 1) + b) * (2 * R + 1) + v + R]; }
static inline long long idx(const int* z) { long long e = 0; int b = R; for (int i = n - 1; i >= 0; i--) { e += OFF(i, b, z[i]); b -= abs(z[i]); } return e; }
static inline bool getb(long long e) { return (pres[e >> 6] >> (e & 63)) & 1; }
static inline void setb(long long e, bool on) { if (on) pres[e >> 6] |= 1ULL << (e & 63); else pres[e >> 6] &= ~(1ULL << (e & 63)); }
static int nr(const int* a) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); return s; }
static int d1(const int* a, const int* b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
static int layer(const int* a) { for (int i = n - 1; i >= 0; i--) if (a[i]) return i; return -1; }
static bool isPos(const int* a) { int L = layer(a); return L >= 0 && a[L] > 0; }
static bool present(const int* a) { return nr(a) <= R && isPos(a) && getb(idx(a)); }
// orbit key of a > 0 under H_L: layer, a[L], sorted |a_0..a_{L-1}|
static uint64_t okey(const int* a) { int L = layer(a); int v[12]; for (int i = 0; i < L; i++) v[i] = abs(a[i]); sort(v, v + L, greater<int>());
  uint64_t k = L; k = k * 64 + a[L]; for (int i = 0; i < L; i++) k = k * 64 + v[i]; return k; }
static uint64_t mkey(const int* a, int j) { int v[12]; for (int i = 0; i < j; i++) v[i] = abs(a[i]); sort(v, v + j, greater<int>());
  uint64_t k = j; for (int i = 0; i < j; i++) k = k * 64 + v[i]; return k; }
static long long osize(const int* a) { int L = layer(a); map<int, int> m; int nz = 0; for (int i = 0; i < L; i++) { m[abs(a[i])]++; if (a[i]) nz++; }
  long long s = 1; for (int i = 2; i <= L; i++) s *= i; for (auto& [v, c] : m) for (int i = 2; i <= c; i++) s /= i; return s << nz; }
unordered_map<uint64_t, long long> alive; vector<unordered_map<uint64_t, int>> lowc;
static void killPoint(const int* p) { setb(idx(p), 0); uint64_t k = okey(p); if (--alive[k] == 0) { int L = layer(p); for (int j = L + 1; j < n; j++) lowc[j][mkey(p, j)]--; } }
// DFS: is there z (in the test set) with d(z,x) <= R < d(z,w)?  mode 0: z in C exactly;  mode 1: z in H_G Chat.
const int *X, *W; int G, MODE, Z[12], sufW[13], sufXW[13]; bool hit; long long nodes = 0;
static bool inTest() { if (!MODE) return isPos(Z) && getb(idx(Z)); int L = layer(Z);
  if (L >= G) { if (Z[L] <= 0) return false; auto it = alive.find(okey(Z)); return it != alive.end() && it->second > 0; }
  auto it = lowc[G].find(mkey(Z, G)); return it != lowc[G].end() && it->second > 0; }
static void rec(int i, int pz, int px, int pw, bool started) {
  if (hit) return; nodes++;
  if (i < 0) { if (started && pw >= R + 1 && inTest()) hit = true; return; }
  int b = R - pz;
  for (int v = -b; v <= b; v++) { int npx = px + abs(v - X[i]); if (npx > R) continue; int npz = pz + abs(v), npw = pw + abs(v - W[i]);
    if (npw + min(R - npz + sufW[i], R - npx + sufXW[i]) < R + 1) continue;
    Z[i] = v; rec(i - 1, npz, npx, npw, started || v != 0); if (hit) break; }
  Z[i] = 0; }
static bool noBad(const int* x, const int* w, int mode, int g) { X = x; W = w; MODE = mode; G = g;
  sufW[0] = sufXW[0] = 0; for (int i = 0; i < n; i++) { sufW[i + 1] = sufW[i] + abs(w[i]); sufXW[i + 1] = sufXW[i] + abs(x[i] - w[i]); }
  hit = false; for (int i = 0; i < n; i++) Z[i] = 0; rec(n - 1, 0, 0, 0, false); return !hit; }
static void orbit(const int* a, int j, vector<Pt>& out) { out.clear(); set<Pt> seen; vector<int> perm(j); iota(perm.begin(), perm.end(), 0);
  do { for (int m = 0; m < (1 << j); m++) { Pt y{}; for (int i = 0; i < n; i++) y[i] = a[i];
      bool skip = false; for (int i = 0; i < j; i++) { if ((m >> i & 1) && a[i] == 0) { skip = true; break; } y[perm[i]] = (m >> i & 1) ? -a[i] : a[i]; }
      if (!skip && seen.insert(y).second) out.push_back(y); } } while (next_permutation(perm.begin(), perm.end())); }
static void boxCands(const int* x, int j, int M, vector<Pt>& C, int maxCand) { C.clear(); Pt w{};
  function<void(int)> g = [&](int i) { if (i < 0) { if (layer(w.data()) < j || nr(w.data()) > M || d1(w.data(), x) > R || d1(w.data(), x) == 0) return; C.push_back(w); return; }
    int lo = min(0, x[i]), hi = max(0, x[i]); if (i == n - 1) hi = max(hi, 1); for (int v = lo; v <= hi; v++) { w[i] = v; g(i - 1); } w[i] = 0; };
  g(n - 1);
  sort(C.begin(), C.end(), [&](const Pt& a, const Pt& b) { int ka = abs(2 * nr(a.data()) - R), kb = abs(2 * nr(b.data()) - R); if (ka != kb) return ka < kb;
    int da = d1(a.data(), x), db = d1(b.data(), x); if (da != db) return da < db; return a < b; });
  if ((int)C.size() > maxCand) C.resize(maxCand); }
int main(int argc, char** argv) {
  n = atoi(argv[1]); R = atoi(argv[2]); FILE* cert = fopen(argv[3], "w"); int maxCand = argc > 4 ? atoi(argv[4]) : 400; double budget = argc > 5 ? atof(argv[5]) : 1100;
  auto t0 = chrono::steady_clock::now(); auto el = [&]() { return chrono::duration<double>(chrono::steady_clock::now() - t0).count(); };
  for (int i = 0; i <= n; i++) cnt[i].assign(R + 1, 0); for (int b = 0; b <= R; b++) cnt[0][b] = 1;
  for (int i = 1; i <= n; i++) for (int b = 0; b <= R; b++) { long long s = 0; for (int v = -b; v <= b; v++) s += cnt[i - 1][b - abs(v)]; cnt[i][b] = s; }
  off.assign((size_t)n * (R + 1) * (2 * R + 1), 0);
  for (int i = 0; i < n; i++) for (int b = 0; b <= R; b++) { long long s = 0; for (int v = -b; v <= b; v++) { OFF(i, b, v) = s; s += cnt[i][b - abs(v)]; } }
  long long tot = cnt[n][R]; pres.assign(tot / 64 + 1, 0); lowc.assign(n, {}); long long present_n = 0;
  { int z[12] = {0}; function<void(int, int)> gen = [&](int i, int rem) { if (i < 0) { if (isPos(z)) { setb(idx(z), 1); present_n++; alive[okey(z)]++; } return; }
      for (int v = -rem; v <= rem; v++) { z[i] = v; gen(i - 1, rem - abs(v)); } z[i] = 0; }; gen(n - 1, R); }
  // lowc: for each orbit (key) with alive > 0 and layer L, add to lowc[j] for j > L: need a representative
  { int z[12] = {0}; set<uint64_t> done; function<void(int, int)> gen = [&](int i, int rem) { if (i < 0) { if (isPos(z)) { uint64_t k = okey(z); if (done.insert(k).second) { int L = layer(z); for (int j = L + 1; j < n; j++) lowc[j][mkey(z, j)]++; } } return; }
      for (int v = -rem; v <= rem; v++) { z[i] = v; gen(i - 1, rem - abs(v)); } z[i] = 0; }; gen(n - 1, R); }
  printf("k=%d r=%d |Lmax|=%lld orbits=%zu\n", n, R, present_n, alive.size()); fflush(stdout);
  Pt ek{}; ek[n - 1] = 1; long long nOrb = 0, nPt = 0, lines = 0; vector<Pt> D;  // deferred orbit reps
  auto pr = [&](const int* a) { for (int i = 0; i < n; i++) fprintf(cert, "%d ", a[i]); };
  vector<Pt> orb, cands; bool timeout = false;
  for (int m = R; m >= 1 && !timeout; m--) {
    vector<Pt> lev;
    for (int j = 0; j < n; j++) { Pt x{};
      function<void(int, int, int)> g3 = [&](int i, int rem, int mx) { if (i == j) { if (rem == 0) lev.push_back(x); return; }
        for (int v = 0; v <= min(rem, mx); v++) { x[i] = v; g3(i + 1, rem - v, v); } x[i] = 0; };
      for (int t = 1; t <= m; t++) { x = Pt{}; x[j] = t; g3(0, m - t, m); } }
    vector<Pt> pend = D; pend.insert(pend.end(), lev.begin(), lev.end()); bool changed = true; int pass = 0;
    while (changed && !pend.empty() && !timeout) { changed = false; pass++; vector<Pt> np;
      for (auto& x : pend) { if (el() > budget) { timeout = true; np.push_back(x); continue; }
        if (x == ek) continue; int j = layer(x.data()); auto it = alive.find(okey(x.data())); // H_j x is part of the H_j orbit... alive counts are per H_L orbit with L = j
        if (it == alive.end() || it->second == 0) { changed = true; continue; }
        orbit(x.data(), j, orb); bool done = false;
        // equivariant move
        boxCands(x.data(), j, m - 1 < 1 ? 0 : m - 1, cands, maxCand);
        for (auto& w : cands) { int L = layer(w.data()); if (L < 0 || w[L] <= 0) continue;
          auto iw = alive.find(okey(w.data())); if (iw == alive.end() || iw->second != osize(w.data())) continue;
          if (L == j && okey(w.data()) == okey(x.data())) continue;  // same orbit
          if (!noBad(x.data(), w.data(), 1, j)) continue;
          // map w along with x: for each orbit point we need hw; recompute by applying the same signed permutation
          vector<int> perm(j); iota(perm.begin(), perm.end(), 0); set<Pt> seen;
          do { for (int mm = 0; mm < (1 << j); mm++) { Pt y{}, yw{}; bool skip = false;
              for (int i = 0; i < n; i++) { y[i] = x[i]; yw[i] = w[i]; }
              for (int i = 0; i < j; i++) { int s = (mm >> i & 1) ? -1 : 1; if (s < 0 && x[i] == 0 && w[i] == 0) { skip = true; break; } y[perm[i]] = s * x[i]; yw[perm[i]] = s * w[i]; }
              if (skip || !seen.insert(y).second) continue; if (!present(y.data())) continue;
              killPoint(y.data()); fprintf(cert, "D "); pr(y.data()); fprintf(cert, "| "); pr(yw.data()); fprintf(cert, "\n"); lines++; } } while (next_permutation(perm.begin(), perm.end()));
          nOrb++; done = true; changed = true; break; }
        if (done) continue;
        // point moves
        bool any = false;
        for (auto& p : orb) { if (!present(p.data())) continue; boxCands(p.data(), 0, R, cands, maxCand); bool ok = false;
          for (auto& w : cands) { if (!present(w.data())) continue; if (!noBad(p.data(), w.data(), 0, 0)) continue;
            killPoint(p.data()); fprintf(cert, "D "); pr(p.data()); fprintf(cert, "| "); pr(w.data()); fprintf(cert, "\n"); lines++; nPt++; ok = true; break; }
          if (ok) any = true; }
        if (any) changed = true;
        if (alive[okey(x.data())] > 0) np.push_back(x); }
      pend = np; }
    D = pend; long long dp = 0; for (auto& x : D) dp += alive[okey(x.data())];
    fprintf(stderr, "m=%d passes=%d deferred orbits=%zu points=%lld orbitMoves=%lld pointMoves=%lld t=%.0fs nodes=%lld\n", m, pass, D.size(), dp, nOrb, nPt, el(), nodes);
  }
  fclose(cert); long long left = 0; for (auto& [k, c] : alive) left += c;
  printf("k=%d r=%d orbitMoves=%lld pointMoves=%lld lines=%lld left=%lld t=%.0fs %s\n", n, R, nOrb, nPt, lines, left, el(), (left == 1 && present(ek.data())) ? "REACHES {e_k}" : (timeout ? "TIMEOUT" : "STUCK"));
  if (!D.empty()) { int sh = 0; printf("deferred:"); for (auto& x : D) { if (sh++ >= 10) break; printf(" ["); for (int i = 0; i < n; i++) printf("%d ", x[i]); printf("x%lld]", alive[okey(x.data())]); } printf("\n"); }
}
