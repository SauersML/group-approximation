// Verifier for layered orbit certificates of VR(Z^k, d_1; r) (lifted peeling links).
// Lmax = { x in Z^k : |x|_1 <= r, x > 0 } (last nonzero coordinate positive).  Layer of x: index of its last nonzero
// coordinate.  H_j = group of signed permutations of coordinates 1..j (0-based: 0..j-1), fixing the others and e_k.
// A line "D x | w" with j = layer(x) stands for deleting every point of the orbit H_j x, the point h x with dominator
// h w.  Checked for each line, on the current set C:
//   (a) x in C, w in C, w != x, d(x,w) <= r, w in hull(0, x, e_k), layer(w) >= j;
//   (b) H_j w and H_j x are different orbits;
//   (c) every point of H_j x and every point of H_j w lies in C (both orbits enumerated explicitly);
//   (d) no z in H_j C with d(z,x) <= r < d(z,w), by exhaustive DFS over the ball.  z in H_j C is decided as:
//       layer(z) >= j: z > 0 and z in C (valid because C ∩ T_i stays a union of H_i orbits for every i: the initial
//       T_i is H_i-invariant and every deletion removes a whole H_j orbit inside T_j);  layer(z) < j: some point of C
//       in layers < j has the same multiset of absolute values in coordinates 0..j-1 (a maintained count).
// Then all of H_j x is deleted.  Success: at the end C = { e_k }.
// Usage: ./overv k r certfile [-x expandedfile]    (-x also writes the point-level moves "D hx | hw")
#include <bits/stdc++.h>
using namespace std;
int n, R; vector<uint64_t> pres; long long presentCount = 0; vector<long long> cnt[17], off;
static inline long long& OFF(int i, int b, int v) { return off[((size_t)i * (R + 1) + b) * (2 * R + 1) + v + R]; }
static inline long long idx(const int* z) { long long e = 0; int b = R; for (int i = n - 1; i >= 0; i--) { e += OFF(i, b, z[i]); b -= abs(z[i]); } return e; }
static inline bool getb(long long e) { return (pres[e >> 6] >> (e & 63)) & 1; }
static inline void setb(long long e, bool on) { if (on) pres[e >> 6] |= 1ULL << (e & 63); else pres[e >> 6] &= ~(1ULL << (e & 63)); }
static int nrm(const int* a) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); return s; }
static int dist(const int* a, const int* b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
static bool isPos(const int* a) { for (int i = n - 1; i >= 0; i--) if (a[i]) return a[i] > 0; return false; }
static int layerOf(const int* a) { for (int i = n - 1; i >= 0; i--) if (a[i]) return i; return -1; }
static bool present(const int* a) { return nrm(a) <= R && isPos(a) && getb(idx(a)); }
vector<map<vector<int>, long long>> low;  // low[j][sorted |coords 0..j-1|] over points of C in layers < j
static vector<int> absKey(const int* a, int j) { vector<int> v(a, a + j); for (auto& t : v) t = abs(t); sort(v.begin(), v.end()); return v; }
static void lowAdd(const int* a, long long d) { int L = layerOf(a); for (int j = L + 1; j < n; j++) low[j][absKey(a, j)] += d; }
// all images of a under H_j, each paired with the same group element applied to b
static void orbitPairs(const int* a, const int* b, int j, vector<pair<array<int, 16>, array<int, 16>>>& out) {
  out.clear(); vector<int> perm(j); iota(perm.begin(), perm.end(), 0); set<array<int, 16>> seen;
  do { for (int m = 0; m < (1 << j); m++) { array<int, 16> ya{}, yb{};
      for (int i = 0; i < n; i++) { ya[i] = a[i]; yb[i] = b[i]; }
      for (int i = 0; i < j; i++) { int s = (m >> i & 1) ? -1 : 1; ya[perm[i]] = s * a[i]; yb[perm[i]] = s * b[i]; }
      if (seen.insert(ya).second) out.push_back({ya, yb}); } } while (next_permutation(perm.begin(), perm.end())); }
const int *X, *W; int G, Z[16], sufW[17], sufXW[17]; bool hit; long long nodes = 0;
static void rec(int i, int pz, int px, int pw, bool started, long long e) {
  if (hit) return; nodes++;
  if (i < 0) { if (!started || pw < R + 1) return; int L = layerOf(Z);
    if (L >= G) { if (Z[L] > 0 && getb(e)) hit = true; }
    else { auto it = low[G].find(absKey(Z, G)); if (it != low[G].end() && it->second > 0) hit = true; }
    return; }
  int b = R - pz;
  for (int v = -b; v <= b; v++) {
    int npx = px + abs(v - X[i]); if (npx > R) continue; int npz = pz + abs(v), npw = pw + abs(v - W[i]);
    if (npw + min(R - npz + sufW[i], R - npx + sufXW[i]) < R + 1) continue;
    Z[i] = v; rec(i - 1, npz, npx, npw, started || v != 0, e + OFF(i, b, v)); if (hit) break; }
  Z[i] = 0; }
static bool noBad(const int* x, const int* w, int g) { X = x; W = w; G = g;
  sufW[0] = sufXW[0] = 0; for (int i = 0; i < n; i++) { sufW[i + 1] = sufW[i] + abs(w[i]); sufXW[i + 1] = sufXW[i] + abs(x[i] - w[i]); }
  hit = false; for (int i = 0; i < n; i++) Z[i] = 0; rec(n - 1, 0, 0, 0, false, 0); return !hit; }
static void fail(const char* why, long long line) { printf("FAIL line %lld: %s\n", line, why); exit(1); }
static bool readPt(FILE* f, int* a) { for (int i = 0; i < n; i++) if (fscanf(f, "%d", &a[i]) != 1) return false; return true; }
static bool readBar(FILE* f) { char c[4]; return fscanf(f, "%3s", c) == 1 && c[0] == '|'; }
int main(int argc, char** argv) {
  n = atoi(argv[1]); R = atoi(argv[2]); FILE* xf = nullptr; if (argc > 5 && !strcmp(argv[4], "-x")) xf = fopen(argv[5], "w");
  for (int i = 0; i <= n; i++) cnt[i].assign(R + 1, 0);
  for (int b = 0; b <= R; b++) cnt[0][b] = 1;
  for (int i = 1; i <= n; i++) for (int b = 0; b <= R; b++) { long long s = 0; for (int v = -b; v <= b; v++) s += cnt[i - 1][b - abs(v)]; cnt[i][b] = s; }
  off.assign((size_t)n * (R + 1) * (2 * R + 1), 0);
  for (int i = 0; i < n; i++) for (int b = 0; b <= R; b++) { long long s = 0; for (int v = -b; v <= b; v++) { OFF(i, b, v) = s; s += cnt[i][b - abs(v)]; } }
  long long tot = cnt[n][R]; pres.assign(tot / 64 + 1, 0); low.assign(n, {});
  { int z[16] = {0}; long long seen = 0; bool bad = false; vector<uint64_t> chk(tot / 64 + 1, 0);
    function<void(int, int)> gen = [&](int i, int rem) { if (i < 0) { long long e = idx(z); if (e < 0 || e >= tot || (chk[e >> 6] >> (e & 63) & 1)) bad = true; else chk[e >> 6] |= 1ULL << (e & 63); seen++;
        if (isPos(z)) { setb(e, 1); presentCount++; lowAdd(z, 1); } return; }
      for (int v = -rem; v <= rem; v++) { z[i] = v; gen(i - 1, rem - abs(v)); } z[i] = 0; }; gen(n - 1, R);
    if (bad || seen != tot) { puts("rank is not a bijection"); return 1; } }
  printf("k=%d r=%d |Lmax|=%lld\n", n, R, presentCount);
  FILE* f = fopen(argv[3], "r"); if (!f) { puts("cannot open cert"); return 1; }
  long long line = 0, moves = 0, pts = 0; char t[4]; vector<pair<array<int, 16>, array<int, 16>>> OX, OW; int en[16] = {0}; en[n - 1] = 1;
  while (fscanf(f, "%3s", t) == 1) { line++; int x[16] = {0}, w[16] = {0};
    if (t[0] == 'P') { int d; if (fscanf(f, "%d", &d) != 1) fail("parse", line); continue; }
    if (t[0] != 'D') fail("unknown move type", line);
    if (!readPt(f, x) || !readBar(f) || !readPt(f, w)) fail("parse", line);
    int j = layerOf(x);
    if (!present(x)) fail("x not present", line); if (!present(w)) fail("w not present", line);
    if (dist(x, w) == 0 || dist(x, w) > R) fail("bad d(x,w)", line);
    for (int i = 0; i < n; i++) { int lo = min(0, x[i]), hi = max(0, x[i]); if (i == n - 1) hi = max(hi, 1); if (w[i] < lo || w[i] > hi) fail("w not in hull(0,x,e_k)", line); }
    if (layerOf(w) < j) fail("layer(w) < layer(x)", line);
    orbitPairs(x, w, j, OX);
    { int dummy[16] = {0}; orbitPairs(w, dummy, j, OW); }
    set<array<int, 16>> ox; for (auto& p : OX) ox.insert(p.first);
    for (auto& p : OW) if (ox.count(p.first)) fail("w in the orbit of x", line);
    for (auto& p : OX) if (!present(p.first.data())) fail("orbit point of x not present", line);
    for (auto& p : OW) if (!present(p.first.data())) fail("orbit point of w not present", line);
    if (!noBad(x, w, j)) fail("domination fails", line);
    for (auto& p : OX) { setb(idx(p.first.data()), 0); presentCount--; lowAdd(p.first.data(), -1); pts++;
      if (xf) { fprintf(xf, "D "); for (int i = 0; i < n; i++) fprintf(xf, "%d ", p.first[i]); fprintf(xf, "| "); for (int i = 0; i < n; i++) fprintf(xf, "%d ", p.second[i]); fprintf(xf, "\n"); } }
    moves++; }
  if (xf) fclose(xf);
  bool ok = presentCount == 1 && present(en);
  printf("orbit moves=%lld point moves=%lld left=%lld dfs=%lld -> %s\n", moves, pts, presentCount, nodes, ok ? "VERIFIED: ends at {e_k}" : "NOT at {e_k}");
  return ok ? 0 : 1; }
