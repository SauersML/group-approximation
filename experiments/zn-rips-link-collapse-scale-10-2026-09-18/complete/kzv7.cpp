// kzv7: kzv6 with AVX-512 row builds (8 packed points per vpsadbw; the compare mask is one byte of the row) and a hash
// table on packed coordinates for the lattice-neighbour lookups.  Same checks, same maximal protected collapse, same
// output as kzv6; it shares no code with the search programs.  Needs AVX-512BW.
// (kzv6 header follows) kzv6: kzv5 without the global N x N adjacency matrix, so that (8,10) sets of 250k+ points fit in 2GB.  It checks the
// same moves with the same maximal protected collapse; it shares no code with the search programs.
// Global neighbourhoods are recomputed for every line from packed coordinates (byte t = coordinate t + 64; vpsadbw sums
// the absolute byte differences, which is exactly the l^1 distance; a deleted point is packed as all-ones, which is at
// distance > 60 from every packed point).  Inside a K line the s x s link rows are computed the same way.
// (kzv5 header follows) kzv5: verifier for compact lifted certificates (D and K lines) on VR(Z^k, d_1; r), E = e_k.  It is kzv3 with a
// faster adjacency build and a faster collapse; it shares no code with the search programs.  All adjacency is
// recomputed from the l^1 distances of the points read from the start file.
//   D x | w : x, w present, w != x, d(x,w) <= r, w in hull(0,x,E), and every present z with d(z,x) <= r has
//             d(z,w) <= r.  Then x is deleted.
//   K u | w : u, w present, w != u, d(u,w) <= r, w in hull(0,u,E).  S = present z != u with d(z,u) <= r.
//             The maximal protected collapse of S is run: while some b in cur, b != w, has v in cur, v != b,
//             d(b,v) <= r, v in hull(0,u,b,E) and N[b] cap cur subset N[v], delete b from cur.
//             Accept iff every z in the final cur has d(z,w) <= r.  Then u is deleted.
// Adjacency: rows are built with vpsadbw when k <= 8 and r <= 60 (AVX2), and pairwise otherwise.
// Only points whose neighbourhood lost a point since their last failed examination are re-examined.
// Usage: ./kzv5 k r startfile certfile [outfile] [budgetSec]
//   With budgetSec it checks no line that would start after budgetSec wall seconds: it then prints PAUSED with the number
//   of lines checked, writes the current set to outfile and exits 3, so a long certificate can be replayed in pieces.
//   startfile: the present set before the certificate (checked to lie in Lmax_k, without duplicates).
//   Exit 0 iff every line checks; prints the size of the end set and whether it is {e_k}; writes it to outfile.
#include <bits/stdc++.h>
#include <immintrin.h>
using namespace std;
int K_, R_;
struct P { int c[12]; bool operator<(const P& o) const { return lexicographical_compare(c, c + K_, o.c, o.c + K_); } };
static int dist(const P& a, const P& b) { int s = 0; for (int i = 0; i < K_; i++) s += abs(a.c[i] - b.c[i]); return s; }
static bool hullOK(const P& w, const vector<const P*>& gens) { // w in the smallest box containing 0 and gens
  for (int i = 0; i < K_; i++) { int lo = 0, hi = 0; for (auto g : gens) { lo = min(lo, g->c[i]); hi = max(hi, g->c[i]); } if (w.c[i] < lo || w.c[i] > hi) return false; } return true; }
static bool readPt(FILE* f, P& p) { for (int i = 0; i < K_; i++) if (fscanf(f, "%d", &p.c[i]) != 1) return false; return true; }
int main(int argc, char** argv) {
  if (argc < 5) { puts("usage: kzv k r startfile certfile [outfile]"); return 1; }
  K_ = atoi(argv[1]); R_ = atoi(argv[2]);
  vector<P> pts; map<P, int> id; P E{}; for (int i = 0; i < 12; i++) E.c[i] = 0; E.c[K_ - 1] = 1;
  { FILE* f = fopen(argv[3], "r"); P p; for (int i = 0; i < 12; i++) p.c[i] = 0;
    while (readPt(f, p)) { int nrm = 0; for (int i = 0; i < K_; i++) nrm += abs(p.c[i]); int last = 0; for (int i = K_ - 1; i >= 0; i--) if (p.c[i]) { last = p.c[i]; break; }
      if (nrm > R_ || last <= 0) { puts("FAIL start point not in Lmax"); return 1; }
      if (id.count(p)) { puts("FAIL duplicate start point"); return 1; } id[p] = pts.size(); pts.push_back(p); } fclose(f); }
  if (!id.count(E)) { puts("FAIL e_k not in start set"); return 1; }
  int N = pts.size(); vector<char> alive(N, 1); int nalive = N;
  if (K_ > 8 || R_ > 60) { puts("kzv7 needs k <= 8 and r <= 60"); return 1; }
  int Np = (N + 7) / 8 * 8; vector<uint64_t> q(Np, ~0ULL);
  for (int j = 0; j < N; j++) { uint64_t z = 0; for (int t = 0; t < 8; t++) z |= (uint64_t)(uint8_t)((t < K_ ? pts[j].c[t] : 0) + 64) << (8 * t); q[j] = z; }
  const __m256i lim = _mm256_set1_epi64x(R_ + 1);
  // present points within r of the packed point a (closed: a itself if present), ascending index
  const __m512i lim8 = _mm512_set1_epi64(R_ + 1);
  auto nearAll = [&](uint64_t a0, const vector<uint64_t>& Q, vector<int>& out) { out.clear(); const __m512i a = _mm512_set1_epi64((long long)a0);
    for (size_t j = 0; j < Q.size(); j += 8) { __m512i sd = _mm512_sad_epu8(a, _mm512_loadu_si512((const void*)&Q[j]));
      unsigned m = _mm512_cmpgt_epi64_mask(lim8, sd); while (m) { out.push_back((int)j + __builtin_ctz(m)); m &= m - 1; } } };
  vector<int> Nx;
  fprintf(stderr, "kzv7: %d start points (implicit adjacency)\n", N);
  FILE* f = fopen(argv[4], "r"); char tag[4]; long long line = 0, nD = 0, nK = 0, steps = 0; auto t0 = clock();
  auto look = [&](const P& p) -> int { auto it = id.find(p); if (it == id.end() || !alive[it->second]) return -1; return it->second; };
  double budget = argc > 6 ? atof(argv[6]) : 1e18; auto w0 = chrono::steady_clock::now(); bool paused = false;
  while (!(paused = chrono::duration<double>(chrono::steady_clock::now() - w0).count() > budget) && fscanf(f, "%3s", tag) == 1) { line++; P x, w; char bar[4];
    if (!readPt(f, x) || fscanf(f, "%3s", bar) != 1 || strcmp(bar, "|") || !readPt(f, w)) { printf("FAIL parse at line %lld\n", line); return 1; }
    int xi = look(x), wi = look(w);
    if (xi < 0 || wi < 0 || xi == wi) { printf("FAIL line %lld: point absent or equal\n", line); return 1; }
    if (dist(x, w) > R_ || !hullOK(w, {&x, &E})) { printf("FAIL line %lld: w not adjacent or not in hull(0,x,E)\n", line); return 1; }
    nearAll(q[xi], q, Nx); // N[x] cap present
    if (tag[0] == 'D') {
      for (int z : Nx) if (dist(pts[z], w) > R_) { printf("FAIL line %lld: D not dominated\n", line); return 1; }
      nD++;
    } else if (tag[0] == 'K') {
      // link S = present neighbours of x other than x, in increasing index order
      vector<int> S; for (int z : Nx) if (z != xi) S.push_back(z);
      int s = S.size(), sw = (s + 63) / 64; vector<uint64_t> adj((size_t)s * sw + 1, 0); int wl = -1;
      { int sp = (s + 7) / 8 * 8; vector<uint64_t> Sq(sp, ~0ULL); for (int i = 0; i < s; i++) Sq[i] = q[S[i]];
        for (int i = 0; i < s; i++) { if (S[i] == wi) wl = i; uint8_t* out = (uint8_t*)&adj[(size_t)i * sw]; const __m512i a = _mm512_set1_epi64((long long)Sq[i]);
          for (int j = 0; j < sp; j += 8) { __m512i sd = _mm512_sad_epu8(a, _mm512_loadu_si512((const void*)&Sq[j]));
            out[j / 8] = (uint8_t)_mm512_cmpgt_epi64_mask(lim8, sd); } } }
      if (wl < 0) { printf("FAIL line %lld: w not in link\n", line); return 1; }
      vector<char> in(s, 1); vector<uint64_t> cm(sw, 0); for (int i = 0; i < s; i++) cm[i / 64] |= 1ULL << (i % 64);
      const uint64_t* rwl = nullptr; if (wl >= 0) rwl = &adj[(size_t)wl * sw];
      auto inside = [&]() { for (int t = 0; t < sw; t++) if (cm[t] & ~rwl[t]) return false; return true; };
      // local index of each link point, for the lattice-neighbour lookups below
      unordered_map<uint64_t, int> lid; lid.reserve(2 * s); for (int i = 0; i < s; i++) lid[q[S[i]]] = i;
      auto domin = [&](int b, int v) { const uint64_t* rb = &adj[(size_t)b * sw]; const uint64_t* rv = &adj[(size_t)v * sw];
        for (int t = 0; t < sw; t++) if (rb[t] & cm[t] & ~rv[t]) return false; return true; };
      // box of (0, x, b, E) for the current b: v must lie in it (hull(0, u, b, E) of the move, with u = x)
      int blo[12], bhi[12];
      auto setbox = [&](int b) { const P& pb = pts[S[b]]; for (int i = 0; i < K_; i++) { blo[i] = min({0, x.c[i], pb.c[i], E.c[i]}); bhi[i] = max({0, x.c[i], pb.c[i], E.c[i]}); } };
      auto inbox = [&](const P& v) { for (int i = 0; i < K_; i++) if (v.c[i] < blo[i] || v.c[i] > bhi[i]) return false; return true; };
      auto okv = [&](int b, int v) { return v != b && in[v] && dist(pts[S[b]], pts[S[v]]) <= R_ && inbox(pts[S[v]]) && domin(b, v); };
      bool again = true; long long sinceCheck = 0;
      // hot: recently successful dominators, tried first (move to front).  Speed only: okv re-checks every condition.
      vector<int> hot; auto promote = [&](int v) { auto it = find(hot.begin(), hot.end(), v); if (it != hot.end()) hot.erase(it); hot.insert(hot.begin(), v); if (hot.size() > 48) hot.pop_back(); };
      // dirty[b]: b has not been examined since a point of N[b] was last removed.  A b that failed stays non-removable
      // until some point of N[b] cap cur is removed (the condition N[b] cap cur subset N[v] only gets weaker), so only
      // dirty points are re-examined.  This affects speed only: every removal is still checked in full.
      vector<uint64_t> dirty(sw, ~0ULL); // bitset
      // LE[i][t]: link points whose coordinate i is <= t, for -r <= t <= r (link points lie in Lmax_k, so |c_i| <= r)
      vector<uint64_t> LE((size_t)K_ * (2 * R_ + 1) * sw, 0), bx(sw);
      for (int j = 0; j < s; j++) for (int i = 0; i < K_; i++) LE[((size_t)i * (2 * R_ + 1) + pts[S[j]].c[i] + R_) * sw + j / 64] |= 1ULL << (j % 64);
      for (int i = 0; i < K_; i++) for (int t = 1; t < 2 * R_ + 1; t++) { uint64_t* cur = &LE[((size_t)i * (2 * R_ + 1) + t) * sw]; const uint64_t* prv = cur - sw; for (int q = 0; q < sw; q++) cur[q] |= prv[q]; }
      while (again && !inside()) { again = false;
        for (int b = 0; b < s; b++) { if (!in[b] || b == wl || !((dirty[b / 64] >> (b % 64)) & 1)) continue; dirty[b / 64] &= ~(1ULL << (b % 64)); const uint64_t* rb = &adj[(size_t)b * sw]; setbox(b);
          bool removed = false;
          // try the lattice neighbours of b first (any valid dominator is acceptable)
          for (int i = 0; i < K_ && !removed; i++) for (int dl = -1; dl <= 1 && !removed; dl += 2) { P q = pts[S[b]]; q.c[i] += dl; if (abs(q.c[i]) > R_) continue; uint64_t key = 0; for (int t = 0; t < 8; t++) key |= (uint64_t)(uint8_t)((t < K_ ? q.c[t] : 0) + 64) << (8 * t);
            auto it = lid.find(key); if (it != lid.end() && okv(b, it->second)) removed = true; }
          for (size_t h = 0; h < hot.size() && !removed; h++) if (okv(b, hot[h])) { removed = true; promote(hot[h]); }
          // candidate filter only: bx = link points inside the box, from the per-coordinate prefix sets (okv re-checks everything)
          if (!removed) { for (int q = 0; q < sw; q++) bx[q] = rb[q] & cm[q];
            for (int i = 0; i < K_; i++) { const uint64_t* hi = &LE[((size_t)i * (2 * R_ + 1) + bhi[i] + R_) * sw];
              const uint64_t* lo = blo[i] > -R_ ? &LE[((size_t)i * (2 * R_ + 1) + blo[i] - 1 + R_) * sw] : nullptr;
              for (int q = 0; q < sw; q++) bx[q] &= lo ? (hi[q] & ~lo[q]) : hi[q]; } }
          for (int q = 0; q < sw && !removed; q++) { uint64_t cand = bx[q];
            while (cand) { int v = q * 64 + __builtin_ctzll(cand); cand &= cand - 1; if (okv(b, v)) { removed = true; promote(v); break; } } }
          if (removed) { in[b] = 0; cm[b / 64] &= ~(1ULL << (b % 64)); again = true; steps++;
            for (int q = 0; q < sw; q++) dirty[q] |= rb[q] & cm[q]; if (++sinceCheck % 256 == 0 && inside()) break; } } }
      const uint64_t* rw = &adj[(size_t)wl * sw]; for (int t = 0; t < sw; t++) if (cm[t] & ~rw[t]) { printf("FAIL line %lld: K link does not collapse into N[w]\n", line); return 1; }
      nK++;
    } else { printf("FAIL line %lld: bad tag\n", line); return 1; }
    alive[xi] = 0; q[xi] = ~0ULL; nalive--; }
  fclose(f);
  bool basis = nalive == 1 && alive[id[E]];
  // |Lmax_k| = (|ball| - 1) / 2 with |ball| = sum_i 2^i C(k,i) C(r,i); the start set was checked to be a duplicate-free subset of Lmax_k
  long long ball = 0; for (int i = 0; i <= K_; i++) { long long a = 1, b = 1; for (int t = 0; t < i; t++) { a = a * (K_ - t) / (t + 1); b = b * (R_ - t) / (t + 1); } ball += (1LL << i) * a * b; }
  printf("start %s Lmax_k (|Lmax_k| = %lld)\n", (long long)N == (ball - 1) / 2 ? "is all of" : "is a proper subset of", (ball - 1) / 2);
  printf("kzv7 k=%d r=%d start=%d lines=%lld D=%lld K=%lld collapse-steps=%lld end=%d %s %s (%.0f s cpu)\n", K_, R_, N, line, nD, nK, steps, nalive, basis ? "END={e_k}" : "END>{e_k}", paused ? "PAUSED" : "ACCEPT", (double)(clock() - t0) / CLOCKS_PER_SEC);
  if (argc > 5) { vector<P> out; for (int i = 0; i < N; i++) if (alive[i]) out.push_back(pts[i]); sort(out.begin(), out.end()); FILE* g = fopen(argv[5], "w");
    for (auto& p : out) { for (int i = 0; i < K_; i++) fprintf(g, "%d ", p.c[i]); fprintf(g, "\n"); } fclose(g); }
  return paused ? 3 : 0;
}
