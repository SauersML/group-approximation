// Independent verifier for lifted peeling-link certificates of VR(Z^k, d_1; r), rank-indexed and resumable.
// Same checks as vcert.cpp; the presence bitmap is indexed by a dense rank of the l^1 ball B_k(r) instead of
// the box [-r,r]^k, so memory is |B_k(r)| bits.  The rank is checked to be a bijection B_k(r) -> [0,|B_k(r)|).
// Lmax(k,r) = { x in Z^k : |x|_1 <= r, x > 0 } where x > 0 means the last nonzero coordinate is positive.
//   A|S|B|D x | w :  x, w present, w != x, d(x,w) <= r, w in hull(0, x, e_k), and no present z with
//                    d(z,x) <= r < d(z,w).  Then x is deleted.
//   K u | w m, then m lines  b | v :  link L' = present points z != u with d(z,u) <= r.  Each step: b in L',
//                    v in L', v != b, d(b,v) <= r, v in hull(0, u, b, e_k), and no z in L' with d(z,b) <= r < d(z,v);
//                    then b is removed from L' (temporarily).  At the end: w in L', w in hull(0, u, e_k), and no
//                    z in L' with d(z,w) > r.  Then u is deleted.
// Usage: ./vcert2 k r [-i statein] [-o stateout] certfile [certfile ...]
//   -i: start from the present set in statein (written by -o of a previous run) instead of Lmax.
//   -o: write the present set at the end (one point per line).  Chained runs replay a certificate in chunks.
// Exit 0 iff every move checks and the end set is {e_k}; exit 2 if every move checks but the end set is larger.
#include <bits/stdc++.h>
using namespace std;
int n, R; vector<uint64_t> pres, tmp; long long presentCount = 0; vector<long long> cnt[17], off;
static inline long long& OFF(int i, int b, int v) { return off[((size_t)i * (R + 1) + b) * (2 * R + 1) + v + R]; }
static inline long long idx(const int* z) { long long e = 0; int b = R; for (int i = n - 1; i >= 0; i--) { e += OFF(i, b, z[i]); b -= abs(z[i]); } return e; }
static inline bool getb(const vector<uint64_t>& v, long long e) { return (v[e >> 6] >> (e & 63)) & 1; }
static inline void setb(vector<uint64_t>& v, long long e, bool on) { if (on) v[e >> 6] |= 1ULL << (e & 63); else v[e >> 6] &= ~(1ULL << (e & 63)); }
static int nrm(const int* a) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); return s; }
static int dist(const int* a, const int* b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
static bool isPos(const int* a) { for (int i = n - 1; i >= 0; i--) if (a[i]) return a[i] > 0; return false; }
static bool inLmax(const int* a) { return nrm(a) <= R && isPos(a); }
static bool present(const int* a) { return inLmax(a) && getb(pres, idx(a)); }
static bool inHull(const int* w, vector<const int*> S) { int en[16] = {0}; en[n - 1] = 1; S.push_back(en);
  for (int i = 0; i < n; i++) { int lo = 0, hi = 0; for (auto s : S) { lo = min(lo, s[i]); hi = max(hi, s[i]); } if (w[i] < lo || w[i] > hi) return false; } return true; }
const int *X, *W, *U; bool useTmp; int Z[16], sufW[17], sufXW[17]; bool hit; long long nodes = 0;
static void rec(int i, int pz, int px, int pw, int pu, bool started, long long e) {
  if (hit) return; nodes++;
  if (i < 0) { if (!started || pw < R + 1) return; if (!getb(pres, e)) return; if (useTmp && getb(tmp, e)) return; hit = true; return; }
  int b = R - pz;
  for (int v = -b; v <= b; v++) { if (!started && v < 0) continue;
    int npx = px + abs(v - X[i]); if (npx > R) continue; int npu = U ? pu + abs(v - U[i]) : 0; if (npu > R) continue;
    int npz = pz + abs(v), npw = pw + abs(v - W[i]);
    if (npw + min(R - npz + sufW[i], R - npx + sufXW[i]) < R + 1) continue;
    Z[i] = v; rec(i - 1, npz, npx, npw, npu, started || v != 0, e + OFF(i, b, v)); if (hit) break; }
  Z[i] = 0; }
static bool noBad(const int* x, const int* w, const int* u, bool ut) { X = x; W = w; U = u; useTmp = ut;
  sufW[0] = sufXW[0] = 0; for (int i = 0; i < n; i++) { sufW[i + 1] = sufW[i] + abs(w[i]); sufXW[i + 1] = sufXW[i] + abs(x[i] - w[i]); }
  hit = false; for (int i = 0; i < n; i++) Z[i] = 0; rec(n - 1, 0, 0, 0, 0, false, 0); return !hit; }
static void fail(const char* why, long long line) { printf("FAIL line %lld: %s\n", line, why); exit(1); }
static bool readPt(FILE* f, int* a) { for (int i = 0; i < n; i++) if (fscanf(f, "%d", &a[i]) != 1) return false; return true; }
static bool readBar(FILE* f) { char c[4]; return fscanf(f, "%3s", c) == 1 && c[0] == '|'; }
int main(int argc, char** argv) {
  n = atoi(argv[1]); R = atoi(argv[2]); string sin, sout; int ai = 3;
  while (ai < argc && argv[ai][0] == '-' && argv[ai][1]) { if (!strcmp(argv[ai], "-i")) sin = argv[ai + 1]; else if (!strcmp(argv[ai], "-o")) sout = argv[ai + 1]; else { puts("bad option"); return 1; } ai += 2; }
  for (int i = 0; i <= n; i++) cnt[i].assign(R + 1, 0);
  for (int b = 0; b <= R; b++) cnt[0][b] = 1;
  for (int i = 1; i <= n; i++) for (int b = 0; b <= R; b++) { long long s = 0; for (int v = -b; v <= b; v++) s += cnt[i - 1][b - abs(v)]; cnt[i][b] = s; }
  off.assign((size_t)n * (R + 1) * (2 * R + 1), 0);
  for (int i = 0; i < n; i++) for (int b = 0; b <= R; b++) { long long s = 0; for (int v = -b; v <= b; v++) { OFF(i, b, v) = s; s += cnt[i][b - abs(v)]; } }
  long long tot = cnt[n][R]; pres.assign(tot / 64 + 1, 0); tmp.assign(tot / 64 + 1, 0);
  // bijection check: every point of the ball gets a distinct rank in [0, tot)
  { int z[16] = {0}; long long seen = 0; bool bad = false;
    function<void(int, int)> gen = [&](int i, int rem) { if (i < 0) { long long e = idx(z); if (e < 0 || e >= tot || getb(tmp, e)) bad = true; else setb(tmp, e, 1); seen++;
        if (isPos(z) && sin.empty()) { setb(pres, e, 1); presentCount++; } return; }
      for (int v = -rem; v <= rem; v++) { z[i] = v; gen(i - 1, rem - abs(v)); } z[i] = 0; }; gen(n - 1, R);
    if (bad || seen != tot) { puts("rank is not a bijection"); return 1; } fill(tmp.begin(), tmp.end(), 0); }
  if (!sin.empty()) { FILE* f = fopen(sin.c_str(), "r"); if (!f) { puts("cannot open state"); return 1; } int a[16] = {0};
    while (readPt(f, a)) { if (!inLmax(a)) { puts("state point not in Lmax"); return 1; } long long e = idx(a); if (getb(pres, e)) { puts("duplicate state point"); return 1; } setb(pres, e, 1); presentCount++; } fclose(f); }
  printf("k=%d r=%d |B|=%lld start present=%lld%s\n", n, R, tot, presentCount, sin.empty() ? " (= |Lmax|)" : " (from state)");
  long long line = 0; map<char, long long> ct; long long kSteps = 0;
  for (int fi = ai; fi < argc; fi++) { FILE* f = fopen(argv[fi], "r"); if (!f) { printf("cannot open %s\n", argv[fi]); return 1; }
    char t[4];
    while (fscanf(f, "%3s", t) == 1) { line++; int x[16] = {0}, w[16] = {0};
      if (!readPt(f, x) || !readBar(f) || !readPt(f, w)) fail("parse", line);
      if (!present(x)) fail("x not present", line); if (!present(w)) fail("w not present", line);
      if (dist(x, w) == 0) fail("w == x", line); if (dist(x, w) > R) fail("d(x,w) > r", line);
      if (!inHull(w, {x})) fail("w not in hull(0,x,e_k)", line);
      if (t[0] == 'A' || t[0] == 'S' || t[0] == 'B' || t[0] == 'D') {
        if (!noBad(x, w, nullptr, false)) fail("domination fails", line);
      } else if (t[0] == 'K') { int m; if (fscanf(f, "%d", &m) != 1) fail("parse m", line);
        vector<long long> rm; long long eu = idx(x); setb(tmp, eu, 1); rm.push_back(eu);
        auto inL = [&](const int* a) { return present(a) && !getb(tmp, idx(a)) && dist(a, x) <= R; };
        for (int s = 0; s < m; s++) { int b[16] = {0}, v[16] = {0}; line++;
          if (!readPt(f, b) || !readBar(f) || !readPt(f, v)) fail("parse step", line);
          if (!inL(b)) fail("b not in link", line); if (!inL(v)) fail("v not in link", line);
          if (dist(b, v) == 0 || dist(b, v) > R) fail("bad d(b,v)", line); if (!inHull(v, {x, b})) fail("v not in hull(0,u,b,e_k)", line);
          if (!noBad(b, v, x, true)) fail("link domination fails", line);
          long long eb = idx(b); setb(tmp, eb, 1); rm.push_back(eb); kSteps++; }
        if (!inL(w)) fail("w not in final link", line);
        if (!noBad(x, w, nullptr, true)) fail("final link not a cone on w", line);
        for (auto e : rm) setb(tmp, e, 0);
      } else fail("unknown move type", line);
      setb(pres, idx(x), 0); presentCount--; ct[t[0]]++; }
    fclose(f); }
  if (!sout.empty()) { FILE* f = fopen(sout.c_str(), "w"); int z[16] = {0};
    function<void(int, int)> gen = [&](int i, int rem) { if (i < 0) { if (isPos(z) && getb(pres, idx(z))) { for (int j = 0; j < n; j++) fprintf(f, "%d ", z[j]); fprintf(f, "\n"); } return; }
      for (int v = -rem; v <= rem; v++) { z[i] = v; gen(i - 1, rem - abs(v)); } z[i] = 0; }; gen(n - 1, R); fclose(f); }
  int en[16] = {0}; en[n - 1] = 1; bool ok = presentCount == 1 && present(en);
  printf("moves:"); for (auto& p : ct) printf(" %c=%lld", p.first, p.second); printf(" (K steps %lld) left=%lld dfs=%lld -> %s\n", kSteps, presentCount, nodes, ok ? "VERIFIED: ends at {e_k}" : "all moves valid; end set is not {e_k}");
  return ok ? 0 : 2; }
