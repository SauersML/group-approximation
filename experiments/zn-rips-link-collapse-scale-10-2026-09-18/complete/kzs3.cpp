// kzs3: block-restricted (K) search for the (8,10) top-shell chains.  For each listed point u still present it builds
// the link S = N(u) cap C minus u exactly as kzv7 does, runs the unprotected collapse of kzs2 (same removal rule:
// b is removed when some v in cur, v != b, d(b,v) <= r, v in hull(0,u,b,E), has N[b] cap cur subset N[v]) and stops
// as soon as some w in cur with w in hull(0,u,E) has cur subset N[w] ("viaZ" in kzs2); it then writes "K u | w".
// It does no (D) moves.  Its output is only a proposal: every line is replayed by kzv7/kzv6, which run the maximal
// collapse protecting w (a superset of the removals found here, since removability only gets easier as cur shrinks).
// Usage: ./kzs3 k r startfile klist certout endout budgetSec
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
  if (argc < 8) { puts("usage: kzs3 k r start klist certout endout budgetSec"); return 1; }
  vector<int> KL; { FILE* f = fopen(argv[4], "r"); P p; for (int i = 0; i < 12; i++) p.c[i] = 0; while (readPt(f, p)) { auto it = id.find(p); if (it != id.end()) KL.push_back(it->second); } fclose(f); }
  fprintf(stderr, "kzs3: %d start points, %zu listed present\n", N, KL.size());
  FILE* cert = fopen(argv[5], "w"); double budget = atof(argv[7]); auto w0 = chrono::steady_clock::now();
  auto el = [&]() { return chrono::duration<double>(chrono::steady_clock::now() - w0).count(); };
  long long nK = 0, nFail = 0; bool outOfTime = false, changed = true; int pass = 0;
  while (changed && !outOfTime) { changed = false; pass++; nFail = 0;
    for (int xi : KL) { if (!alive[xi]) continue; if (el() > budget) { outOfTime = true; break; }
      const P x = pts[xi]; nearAll(q[xi], q, Nx);
      vector<int> S; for (int z : Nx) if (z != xi) S.push_back(z);
      int s = S.size(), sw = (s + 63) / 64; vector<uint64_t> adj((size_t)s * sw + 1, 0);
      { int sp = (s + 7) / 8 * 8; vector<uint64_t> Sq(sp, ~0ULL); for (int i = 0; i < s; i++) Sq[i] = q[S[i]];
        for (int i = 0; i < s; i++) { uint8_t* out = (uint8_t*)&adj[(size_t)i * sw]; const __m512i a = _mm512_set1_epi64((long long)Sq[i]);
          for (int j = 0; j < sp; j += 8) { __m512i sd = _mm512_sad_epu8(a, _mm512_loadu_si512((const void*)&Sq[j]));
            out[j / 8] = (uint8_t)_mm512_cmpgt_epi64_mask(lim8, sd); } } }
      vector<int> cands; for (int i = 0; i < s; i++) if (hullOK(pts[S[i]], {&x, &E})) cands.push_back(i);
      if (cands.empty()) { nFail++; continue; }
      vector<char> in(s, 1); vector<uint64_t> cm(sw, 0); for (int i = 0; i < s; i++) cm[i / 64] |= 1ULL << (i % 64);
      auto covers = [&](int w) { const uint64_t* rw = &adj[(size_t)w * sw]; for (int t = 0; t < sw; t++) if (cm[t] & ~rw[t]) return false; return true; };
      auto findW = [&]() { for (int c : cands) if (in[c] && covers(c)) return c; return -1; };
      unordered_map<uint64_t, int> lid; lid.reserve(2 * s); for (int i = 0; i < s; i++) lid[q[S[i]]] = i;
      auto domin = [&](int b, int v) { const uint64_t* rb = &adj[(size_t)b * sw]; const uint64_t* rv = &adj[(size_t)v * sw];
        for (int t = 0; t < sw; t++) if (rb[t] & cm[t] & ~rv[t]) return false; return true; };
      int blo[12], bhi[12];
      auto setbox = [&](int b) { const P& pb = pts[S[b]]; for (int i = 0; i < K_; i++) { blo[i] = min({0, x.c[i], pb.c[i], E.c[i]}); bhi[i] = max({0, x.c[i], pb.c[i], E.c[i]}); } };
      auto inbox = [&](const P& v) { for (int i = 0; i < K_; i++) if (v.c[i] < blo[i] || v.c[i] > bhi[i]) return false; return true; };
      auto okv = [&](int b, int v) { return v != b && in[v] && dist(pts[S[b]], pts[S[v]]) <= R_ && inbox(pts[S[v]]) && domin(b, v); };
      vector<int> hot; auto promote = [&](int v) { auto it = find(hot.begin(), hot.end(), v); if (it != hot.end()) hot.erase(it); hot.insert(hot.begin(), v); if (hot.size() > 48) hot.pop_back(); };
      vector<uint64_t> dirty(sw, ~0ULL), LE((size_t)K_ * (2 * R_ + 1) * sw, 0), bx(sw);
      for (int j = 0; j < s; j++) for (int i = 0; i < K_; i++) LE[((size_t)i * (2 * R_ + 1) + pts[S[j]].c[i] + R_) * sw + j / 64] |= 1ULL << (j % 64);
      for (int i = 0; i < K_; i++) for (int t = 1; t < 2 * R_ + 1; t++) { uint64_t* cur = &LE[((size_t)i * (2 * R_ + 1) + t) * sw]; const uint64_t* prv = cur - sw; for (int z = 0; z < sw; z++) cur[z] |= prv[z]; }
      int wl = findW(); bool again = true; long long sinceCheck = 0;
      while (wl < 0 && again) { again = false;
        for (int b = 0; b < s; b++) { if (!in[b] || !((dirty[b / 64] >> (b % 64)) & 1)) continue; dirty[b / 64] &= ~(1ULL << (b % 64)); const uint64_t* rb = &adj[(size_t)b * sw]; setbox(b);
          bool removed = false;
          for (int i = 0; i < K_ && !removed; i++) for (int dl = -1; dl <= 1 && !removed; dl += 2) { P qq = pts[S[b]]; qq.c[i] += dl; if (abs(qq.c[i]) > R_) continue; uint64_t key = 0; for (int t = 0; t < 8; t++) key |= (uint64_t)(uint8_t)((t < K_ ? qq.c[t] : 0) + 64) << (8 * t);
            auto it = lid.find(key); if (it != lid.end() && okv(b, it->second)) removed = true; }
          for (size_t h = 0; h < hot.size() && !removed; h++) if (okv(b, hot[h])) { removed = true; promote(hot[h]); }
          if (!removed) { for (int z = 0; z < sw; z++) bx[z] = rb[z] & cm[z];
            for (int i = 0; i < K_; i++) { const uint64_t* hi = &LE[((size_t)i * (2 * R_ + 1) + bhi[i] + R_) * sw];
              const uint64_t* lo = blo[i] > -R_ ? &LE[((size_t)i * (2 * R_ + 1) + blo[i] - 1 + R_) * sw] : nullptr;
              for (int z = 0; z < sw; z++) bx[z] &= lo ? (hi[z] & ~lo[z]) : hi[z]; } }
          for (int z = 0; z < sw && !removed; z++) { uint64_t cand = bx[z];
            while (cand) { int v = z * 64 + __builtin_ctzll(cand); cand &= cand - 1; if (okv(b, v)) { removed = true; promote(v); break; } } }
          if (removed) { in[b] = 0; cm[b / 64] &= ~(1ULL << (b % 64)); again = true;
            for (int z = 0; z < sw; z++) dirty[z] |= rb[z] & cm[z]; if (++sinceCheck % 256 == 0 && (wl = findW()) >= 0) break; } }
        if (wl < 0) wl = findW(); }
      if (wl < 0) { nFail++; continue; }
      fprintf(cert, "K "); for (int i = 0; i < K_; i++) fprintf(cert, "%d ", x.c[i]); fprintf(cert, "| "); for (int i = 0; i < K_; i++) fprintf(cert, "%d ", pts[S[wl]].c[i]); fprintf(cert, "\n"); fflush(cert);
      alive[xi] = 0; q[xi] = ~0ULL; nalive--; nK++; changed = true; }
    fprintf(stderr, "pass %d: K=%lld fail=%lld t=%.0fs\n", pass, nK, nFail, el()); }
  fclose(cert); int lleft = 0; for (int xi : KL) lleft += alive[xi];
  printf("kzs3 k=%d r=%d start=%d K=%lld left=%d listed-left=%d %s\n", K_, R_, N, nK, nalive, lleft, lleft == 0 ? "BLOCK EMPTY" : outOfTime ? "STUCK (time budget)" : "STALL");
  { vector<P> out; for (int i = 0; i < N; i++) if (alive[i]) out.push_back(pts[i]); sort(out.begin(), out.end()); FILE* g = fopen(argv[6], "w");
    for (auto& p : out) { for (int i = 0; i < K_; i++) fprintf(g, "%d ", p.c[i]); fprintf(g, "\n"); } fclose(g); }
  return 0;
}
