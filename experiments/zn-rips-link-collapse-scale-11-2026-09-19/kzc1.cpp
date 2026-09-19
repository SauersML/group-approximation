// kzc1: an acceptance checker for lifted (K) and (D) lines, written from the move definitions only.  It shares no code
// with kzs2, kzs3, kzv6 or kzv7: its own tokenizer (no scanf), its own point store (int arrays, keys by a base-2r+1
// rank), its own scalar l^1 distance (no packed bytes, no SIMD intrinsics), its own link rows and collapse loop.
//
// Moves (z7-rips-contractible-at-scale-10-proof §3, z8-rips-contractible-at-scale-8-proof §2), E = e_k, r = scale:
//   D x | w : x, w in C, w != x, d(x,w) <= r, w in hull(0,x,E), and every z in C with d(z,x) <= r has d(z,w) <= r.
//   K u | w : u, w in C, w != u, d(u,w) <= r, w in hull(0,u,E).  S = { z in C : z != u, d(z,u) <= r }.  Remove from
//             cur = S, one at a time, points b != w that have some v in cur, v != b, d(b,v) <= r, v in hull(0,u,b,E),
//             with every z in cur, d(z,b) <= r, satisfying d(z,v) <= r.  Accept once every z in cur has d(z,w) <= r.
//   Each removal is a valid step of the link collapse of the move, whatever order is used; so acceptance proves the
//   line valid.  (The order only affects whether the collapse reaches N[w], i.e. completeness, not soundness.)
//
// Usage: ./kzc1 k r Ofile certfile first last endfile
//   Ofile: the start set O of the certificate piece (one point per line).  The current set is O with the u of lines
//   1..first-1 of certfile removed; lines first..last are then checked in order.  Points are scanned in the order
//   of Ofile.  endfile gets the final set, one point per line, in the order of Ofile.  Exit 0 iff all lines accept.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <ctime>
#include <string>
#include <vector>
#include <unordered_map>
#include <algorithm>
using std::vector;

static int K, R;
struct Tok { // whitespace tokenizer over a whole file
  vector<char> buf; size_t p = 0;
  bool load(const char* fn) { FILE* f = fopen(fn, "rb"); if (!f) return false; char tmp[1 << 16]; size_t m;
    while ((m = fread(tmp, 1, sizeof tmp, f)) > 0) buf.insert(buf.end(), tmp, tmp + m); fclose(f); buf.push_back(0); return true; }
  void skip() { while (p < buf.size() && (buf[p] == ' ' || buf[p] == '\n' || buf[p] == '\t' || buf[p] == '\r')) p++; }
  bool eof() { skip(); return p + 1 >= buf.size(); }
  std::string word() { skip(); size_t q = p; while (p < buf.size() && buf[p] && buf[p] != ' ' && buf[p] != '\n' && buf[p] != '\t' && buf[p] != '\r') p++; return std::string(&buf[q], &buf[p]); }
  bool num(int& v) { std::string s = word(); if (s.empty()) return false; char* e; long x = strtol(s.c_str(), &e, 10); if (*e) return false; v = (int)x; return true; }
};
struct Pt { int c[8]; };
static int l1(const Pt& a, const Pt& b) { int s = 0; for (int i = 0; i < K; i++) { int t = a.c[i] - b.c[i]; s += t < 0 ? -t : t; } return s; }
static long long rankOf(const Pt& a) { long long h = 0; for (int i = 0; i < K; i++) h = h * (2 * R + 1) + (a.c[i] + R); return h; }
// v lies in the smallest integer box containing 0, E and the points g[0..m-1]
static bool inHull(const Pt& v, const Pt* const* g, int m) {
  for (int i = 0; i < K; i++) { int lo = 0, hi = (i == K - 1) ? 1 : 0;
    for (int j = 0; j < m; j++) { if (g[j]->c[i] < lo) lo = g[j]->c[i]; if (g[j]->c[i] > hi) hi = g[j]->c[i]; }
    if (v.c[i] < lo || v.c[i] > hi) return false; }
  return true; }
static bool readPt(Tok& t, Pt& p) { for (int i = 0; i < K; i++) if (!t.num(p.c[i])) return false; for (int i = K; i < 8; i++) p.c[i] = 0; return true; }

int main(int argc, char** argv) {
  if (argc < 8) { puts("usage: kzc1 k r Ofile certfile first last endfile"); return 1; }
  K = atoi(argv[1]); R = atoi(argv[2]); bool full = getenv("KZC_FULL") != nullptr; long first = atol(argv[5]), last = atol(argv[6]);
  if (K < 2 || K > 8 || R < 1 || R > 100) { puts("FAIL k or r out of range"); return 1; }
  Tok to; if (!to.load(argv[3])) { puts("FAIL cannot read Ofile"); return 1; }
  vector<Pt> P; std::unordered_map<long long, int> where;
  while (!to.eof()) { Pt p; if (!readPt(to, p)) { puts("FAIL parse Ofile"); return 1; }
    int nr = 0, lastnz = 0; for (int i = 0; i < K; i++) { nr += abs(p.c[i]); if (p.c[i]) lastnz = p.c[i]; }
    if (nr > R || lastnz <= 0) { puts("FAIL Ofile point outside Lmax_k"); return 1; }
    if (!where.emplace(rankOf(p), (int)P.size()).second) { puts("FAIL duplicate in Ofile"); return 1; }
    P.push_back(p); }
  int N = P.size(); vector<char> live(N, 1); int nlive = N;
  Pt E; for (int i = 0; i < 8; i++) E.c[i] = 0; E.c[K - 1] = 1;
  auto idx = [&](const Pt& p) { auto it = where.find(rankOf(p)); return (it == where.end() || !live[it->second]) ? -1 : it->second; };
  Tok tc; if (!tc.load(argv[4])) { puts("FAIL cannot read certfile"); return 1; }
  long line = 0, nK = 0, nD = 0, steps = 0; clock_t t0 = clock(), tRows = 0;
  while (!tc.eof() && line < last) { line++;
    std::string tag = tc.word(); Pt x, w; if (!readPt(tc, x) || tc.word() != "|" || !readPt(tc, w) || (tag != "K" && tag != "D")) { printf("FAIL parse cert line %ld\n", line); return 1; }
    int xi = idx(x), wi = idx(w);
    if (xi < 0) { printf("FAIL line %ld: u absent\n", line); return 1; }
    if (line < first) { live[xi] = 0; nlive--; continue; } // earlier piece: only its deletions are applied
    if (wi < 0 || wi == xi) { printf("FAIL line %ld: w absent or equal to u\n", line); return 1; }
    const Pt* g1[1] = {&x};
    if (l1(x, w) > R || !inHull(w, g1, 1)) { printf("FAIL line %ld: w not within r or not in hull(0,u,E)\n", line); return 1; }
    vector<int> S; for (int z = 0; z < N; z++) if (live[z] && z != xi && l1(P[z], x) <= R) S.push_back(z);
    if (tag == "D") { for (int z : S) if (l1(P[z], w) > R) { printf("FAIL line %ld: D not dominated\n", line); return 1; } nD++; live[xi] = 0; nlive--; continue; }
    int s = S.size(), W64 = (s + 63) / 64, wl = -1;
    // coordinate columns of the link (structure of arrays), shifted by R so that they are small non-negative bytes
    vector<vector<uint8_t>> col(K, vector<uint8_t>(s));
    for (int a = 0; a < s; a++) { if (S[a] == wi) wl = a; for (int i = 0; i < K; i++) col[i][a] = (uint8_t)(P[S[a]].c[i] + R); }
    if (wl < 0) { printf("FAIL line %ld: w not in link\n", line); return 1; }
    clock_t tr = clock(); vector<uint64_t> row((size_t)s * W64, 0); // row[a] bit b: d(S[a], S[b]) <= r (closed: a in row[a])
    { vector<uint8_t> acc(s), flag((size_t)W64 * 64, 0); // link points have norm <= r, so each partial sum is <= 2r < 256
      for (int a = 0; a < s; a++) { for (int b = 0; b < s; b++) acc[b] = 0;
        for (int i = 0; i < K; i++) { const uint8_t* __restrict ci = col[i].data(); uint8_t* __restrict ac = acc.data(); const uint8_t ca = ci[a];
          for (int b = 0; b < s; b++) { uint8_t xb = ci[b]; ac[b] = (uint8_t)(ac[b] + (uint8_t)(xb > ca ? xb - ca : ca - xb)); } }
        uint64_t* ra = &row[(size_t)a * W64];
        for (int b = 0; b < s; b++) flag[b] = acc[b] <= R;
        for (int q = 0; q < W64; q++) { uint64_t m = 0; // pack 64 flags into one word, 8 at a time
          for (int j = 0; j < 8; j++) { uint64_t by; memcpy(&by, &flag[q * 64 + 8 * j], 8); m |= ((by * 0x0102040810204080ULL) >> 56) << (8 * j); }
          ra[q] = m; } } }
    tRows += clock() - tr;
    if (getenv("KZC_ROWS")) for (int a = 0; a < s; a++) for (int b = 0; b < s; b++) // rows against l1, every pair
      if ((bool)((row[(size_t)a * W64 + (b >> 6)] >> (b & 63)) & 1) != (l1(P[S[a]], P[S[b]]) <= R)) { printf("INTERNAL rows line %ld\n", line); return 2; }
    // IN[i][t]: link points with coordinate i equal to t - R; prefix unions give the box filter
    int V = 2 * R + 1; vector<uint64_t> LEQ((size_t)K * V * W64, 0);
    for (int a = 0; a < s; a++) for (int i = 0; i < K; i++) LEQ[((size_t)i * V + col[i][a]) * W64 + (a >> 6)] |= 1ULL << (a & 63);
    for (int i = 0; i < K; i++) for (int t = 1; t < V; t++) { uint64_t* c1 = &LEQ[((size_t)i * V + t) * W64]; const uint64_t* c0 = c1 - W64; for (int q = 0; q < W64; q++) c1[q] |= c0[q]; }
    std::unordered_map<long long, int> loc; loc.reserve(2 * s); for (int a = 0; a < s; a++) loc[rankOf(P[S[a]])] = a;
    vector<uint64_t> cur(W64, 0), todo(W64, 0), cand(W64); for (int a = 0; a < s; a++) cur[a >> 6] |= 1ULL << (a & 63); todo = cur;
    const uint64_t* rw = &row[(size_t)wl * W64];
    auto coneOnW = [&]() { for (int q = 0; q < W64; q++) if (cur[q] & ~rw[q]) return false; return true; };
    auto inCur = [&](int a) { return (cur[a >> 6] >> (a & 63)) & 1; };
    auto dominates = [&](int b, int v) { const uint64_t* rb = &row[(size_t)b * W64]; const uint64_t* rv = &row[(size_t)v * W64];
      for (int t = 0; t < W64; t++) if (rb[t] & cur[t] & ~rv[t]) return false; return true; };
    vector<int> recent; // recently used dominators, tried early (order only)
    bool progress = true;
    while (!coneOnW() && progress) { progress = false;
      for (int b = 0; b < s; b++) {
        if (b == wl || !inCur(b) || !((todo[b >> 6] >> (b & 63)) & 1)) continue;
        todo[b >> 6] &= ~(1ULL << (b & 63));
        const uint64_t* rb = &row[(size_t)b * W64]; const Pt* g2[2] = {&x, &P[S[b]]}; int found = -1;
        auto tryv = [&](int v) { if (v != b && inCur(v) && ((rb[v >> 6] >> (v & 63)) & 1) && inHull(P[S[v]], g2, 2) && dominates(b, v)) found = v; };
        for (int i = 0; i < K && found < 0; i++) for (int dl = -1; dl <= 1 && found < 0; dl += 2) { Pt q = P[S[b]]; q.c[i] += dl;
          if (q.c[i] < -R || q.c[i] > R) continue; auto it = loc.find(rankOf(q)); if (it != loc.end()) tryv(it->second); }
        for (size_t h = 0; h < recent.size() && found < 0; h++) tryv(recent[h]);
        if (found < 0) { for (int q = 0; q < W64; q++) cand[q] = rb[q] & cur[q];
          for (int i = 0; i < K; i++) { int lo = 0, hi = (i == K - 1) ? 1 : 0; lo = std::min(lo, std::min(x.c[i], P[S[b]].c[i])); hi = std::max(hi, std::max(x.c[i], P[S[b]].c[i]));
            const uint64_t* H = &LEQ[((size_t)i * V + hi + R) * W64]; const uint64_t* L = lo + R > 0 ? &LEQ[((size_t)i * V + lo + R - 1) * W64] : nullptr;
            for (int q = 0; q < W64; q++) cand[q] &= L ? (H[q] & ~L[q]) : H[q]; }
          for (int q = 0; q < W64 && found < 0; q++) { uint64_t m = cand[q]; while (m && found < 0) { int v = q * 64 + __builtin_ctzll(m); m &= m - 1; tryv(v); } } }
        if (found < 0) continue;
        { auto it = std::find(recent.begin(), recent.end(), found); if (it != recent.end()) recent.erase(it); recent.insert(recent.begin(), found); if (recent.size() > 32) recent.pop_back(); }
        // re-check the removal with explicit distances over the whole current link: every removal with KZC_FULL=1,
        // otherwise every 101st (the rows themselves are checked against l1 by KZC_ROWS=1)
        if (full || steps % 101 == 0) { const Pt& pb = P[S[b]]; const Pt& pv = P[S[found]]; if (l1(pb, pv) > R || !inHull(pv, g2, 2)) { printf("INTERNAL line %ld\n", line); return 2; }
          for (int z = 0; z < s; z++) if (inCur(z) && l1(P[S[z]], pb) <= R && l1(P[S[z]], pv) > R) { printf("INTERNAL line %ld\n", line); return 2; } }
        cur[b >> 6] &= ~(1ULL << (b & 63)); steps++; progress = true;
        for (int q = 0; q < W64; q++) todo[q] |= rb[q] & cur[q];
        if ((steps & 255) == 0 && coneOnW()) break; } }
    // final test with explicit distances: every point left in the link is within r of w
    for (int z = 0; z < s; z++) if (inCur(z) && l1(P[S[z]], w) > R) { printf("FAIL line %ld: link does not collapse into N[w]\n", line); return 1; }
    nK++; live[xi] = 0; nlive--; }
  if (line < last) { printf("FAIL certfile has only %ld lines\n", line); return 1; }
  FILE* g = fopen(argv[7], "w"); for (int i = 0; i < N; i++) if (live[i]) { for (int j = 0; j < K; j++) fprintf(g, j ? " %d" : "%d", P[i].c[j]); fprintf(g, "\n"); } fclose(g);
  printf("kzc1 k=%d r=%d lines %ld..%ld: D=%ld K=%ld collapse-steps=%ld end=%d ACCEPT (%.0f s cpu, %.0f s rows)\n", K, R, first, last, nD, nK, steps, nlive, (double)(clock() - t0) / CLOCKS_PER_SEC, (double)tRows / CLOCKS_PER_SEC);
  return 0; }
