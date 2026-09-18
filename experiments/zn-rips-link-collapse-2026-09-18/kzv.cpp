// kzv: independent verifier for compact lifted certificates (D and K lines) on VR(Z^k, d_1; r), E = e_k.
// It shares no code with the search programs.  All adjacency is recomputed from explicit l^1 distances.
//   D x | w : x, w present, w != x, d(x,w) <= r, w in hull(0,x,E), and every present z with d(z,x) <= r has
//             d(z,w) <= r.  Then x is deleted.
//   K u | w : u, w present, w != u, d(u,w) <= r, w in hull(0,u,E).  S = present z != u with d(z,u) <= r.
//             A protected collapse of S is run: while some b in cur, b != w, has v in cur, v != b,
//             d(b,v) <= r, v in hull(0,u,b,E) and N[b] cap cur subset N[v], delete b from cur.
//             Accept iff every z in the final cur has d(z,w) <= r.  Then u is deleted.
// Usage: ./kzv k r startfile certfile [outfile]
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
  // global adjacency (closed neighbourhoods) from explicit distances; A[i] row has NW words
  int NW = (N + 63) / 64; vector<uint64_t> A((size_t)N * NW, 0), live(NW, 0);
  for (int i = 0; i < N; i++) { A[(size_t)i * NW + i / 64] |= 1ULL << (i % 64); live[i / 64] |= 1ULL << (i % 64);
    for (int j = i + 1; j < N; j++) if (dist(pts[i], pts[j]) <= R_) { A[(size_t)i * NW + j / 64] |= 1ULL << (j % 64); A[(size_t)j * NW + i / 64] |= 1ULL << (i % 64); } }
  fprintf(stderr, "adjacency of %d points built\n", N);
  FILE* f = fopen(argv[4], "r"); char tag[4]; long long line = 0, nD = 0, nK = 0, steps = 0; auto t0 = clock();
  auto look = [&](const P& p) -> int { auto it = id.find(p); if (it == id.end() || !alive[it->second]) return -1; return it->second; };
  while (fscanf(f, "%3s", tag) == 1) { line++; P x, w; char bar[4];
    if (!readPt(f, x) || fscanf(f, "%3s", bar) != 1 || strcmp(bar, "|") || !readPt(f, w)) { printf("FAIL parse at line %lld\n", line); return 1; }
    int xi = look(x), wi = look(w);
    if (xi < 0 || wi < 0 || xi == wi) { printf("FAIL line %lld: point absent or equal\n", line); return 1; }
    if (dist(x, w) > R_ || !hullOK(w, {&x, &E})) { printf("FAIL line %lld: w not adjacent or not in hull(0,x,E)\n", line); return 1; }
    // link of x among present points
    const uint64_t* Ax = &A[(size_t)xi * NW]; const uint64_t* Aw = &A[(size_t)wi * NW];
    if (tag[0] == 'D') {
      for (int t = 0; t < NW; t++) if (Ax[t] & live[t] & ~Aw[t]) { printf("FAIL line %lld: D not dominated\n", line); return 1; }
      nD++;
    } else if (tag[0] == 'K') {
      // link S = live neighbours of x other than x, in increasing index order
      vector<uint64_t> Sm(NW); for (int t = 0; t < NW; t++) Sm[t] = Ax[t] & live[t]; Sm[xi / 64] &= ~(1ULL << (xi % 64));
      vector<int> S; for (int t = 0; t < NW; t++) { uint64_t b = Sm[t]; while (b) { S.push_back(t * 64 + __builtin_ctzll(b)); b &= b - 1; } }
      int s = S.size(), sw = (s + 63) / 64; vector<uint64_t> adj((size_t)s * sw + 1, 0); int wl = -1;
      for (int i = 0; i < s; i++) { if (S[i] == wi) wl = i; const uint64_t* Ai = &A[(size_t)S[i] * NW]; uint64_t* out = &adj[(size_t)i * sw]; long pos = 0;
        for (int t = 0; t < NW; t++) { if (!Sm[t]) continue; uint64_t g = _pext_u64(Ai[t], Sm[t]); int c = __builtin_popcountll(Sm[t]);
          int q = pos / 64, o = pos % 64; out[q] |= g << o; if (o > 0 && o + c > 64) out[q + 1] |= g >> (64 - o); pos += c; } }
      if (wl < 0) { printf("FAIL line %lld: w not in link\n", line); return 1; }
      vector<char> in(s, 1); vector<uint64_t> cm(sw, 0); for (int i = 0; i < s; i++) cm[i / 64] |= 1ULL << (i % 64);
      const uint64_t* rwl = nullptr; if (wl >= 0) rwl = &adj[(size_t)wl * sw];
      auto inside = [&]() { for (int t = 0; t < sw; t++) if (cm[t] & ~rwl[t]) return false; return true; };
      bool again = wl >= 0;
      while (again && !inside()) { again = false;
        for (int b = 0; b < s; b++) { if (!in[b] || b == wl) continue; const uint64_t* rb = &adj[(size_t)b * sw];
          bool removed = false;
          for (int q = 0; q < sw && !removed; q++) { uint64_t cand = rb[q] & cm[q];
            while (cand) { int v = q * 64 + __builtin_ctzll(cand); cand &= cand - 1; if (v == b || !in[v]) continue;
              if (!hullOK(pts[S[v]], {&x, &pts[S[b]], &E})) continue; const uint64_t* rv = &adj[(size_t)v * sw]; bool dom = true;
              for (int t = 0; t < sw; t++) if (rb[t] & cm[t] & ~rv[t]) { dom = false; break; }
              if (dom) { in[b] = 0; cm[b / 64] &= ~(1ULL << (b % 64)); again = true; steps++; removed = true; break; } } } } }
      const uint64_t* rw = &adj[(size_t)wl * sw]; for (int t = 0; t < sw; t++) if (cm[t] & ~rw[t]) { printf("FAIL line %lld: K link does not collapse into N[w]\n", line); return 1; }
      nK++;
    } else { printf("FAIL line %lld: bad tag\n", line); return 1; }
    alive[xi] = 0; live[xi / 64] &= ~(1ULL << (xi % 64)); nalive--; }
  fclose(f);
  bool basis = nalive == 1 && alive[id[E]];
  // |Lmax_k| = (|ball| - 1) / 2 with |ball| = sum_i 2^i C(k,i) C(r,i); the start set was checked to be a duplicate-free subset of Lmax_k
  long long ball = 0; for (int i = 0; i <= K_; i++) { long long a = 1, b = 1; for (int t = 0; t < i; t++) { a = a * (K_ - t) / (t + 1); b = b * (R_ - t) / (t + 1); } ball += (1LL << i) * a * b; }
  printf("start %s Lmax_k (|Lmax_k| = %lld)\n", (long long)N == (ball - 1) / 2 ? "is all of" : "is a proper subset of", (ball - 1) / 2);
  printf("kzv k=%d r=%d start=%d lines=%lld D=%lld K=%lld collapse-steps=%lld end=%d %s ACCEPT (%.0f s cpu)\n", K_, R_, N, line, nD, nK, steps, nalive, basis ? "END={e_k}" : "END>{e_k}", (double)(clock() - t0) / CLOCKS_PER_SEC);
  if (argc > 5) { vector<P> out; for (int i = 0; i < N; i++) if (alive[i]) out.push_back(pts[i]); sort(out.begin(), out.end()); FILE* g = fopen(argv[5], "w");
    for (auto& p : out) { for (int i = 0; i < K_; i++) fprintf(g, "%d ", p.c[i]); fprintf(g, "\n"); } fclose(g); }
  return 0;
}
