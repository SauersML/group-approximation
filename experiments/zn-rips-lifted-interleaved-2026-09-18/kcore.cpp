// Phase C engine on an explicit current set C (file of points), anti-lex order, lift e_n.
// D-move: delete u if N[u] cap C subset N[w], w in C cap hull(0,u,e_n), w != u.
// K-move (lite): pick w in C cap hull(0,u,e_n) adjacent to u; B = (N(u) cap C) \ N[w].  Collapse the link
//   L = N(u) cap C by removing the points of B one at a time, b dominated inside the current link L' by
//   v in L' cap hull(0,u,b,e_n), v != b (N[b] cap L' subset N[v]).  When B is gone, L' subset N[w] and w in L', so the
//   link is a cone: contractible, and Lemma 2 deletes u.  Restricted to any box I with b_n >= 1 the same steps stay
//   valid (all points used lie in I, neighbourhoods only shrink), so the move is uniform.
// Usage: ./kcore n r corefile [outcore] [cert] [maxBad=64] [budgetSec=1100]
#include <bits/stdc++.h>
using namespace std;
typedef array<int8_t, 12> Pt;
int n, R;
static inline int d1(const Pt& a, const Pt& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
static inline int nr(const Pt& a) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); return s; }
static inline bool inhullS(const Pt& w, const Pt* S, int k) { for (int i = 0; i < n; i++) { int lo = 0, hi = 0; for (int j = 0; j < k; j++) { lo = min(lo, (int)S[j][i]); hi = max(hi, (int)S[j][i]); } if (w[i] < lo || w[i] > hi) return false; } return true; }
static void pr(FILE* f, const Pt& a) { for (int i = 0; i < n; i++) fprintf(f, "%d ", a[i]); }
int main(int argc, char** argv) {
  n = atoi(argv[1]); R = atoi(argv[2]); FILE* cert = argc > 5 && string(argv[5]) != "-" ? fopen(argv[5], "w") : nullptr;
  int maxBad = argc > 6 ? atoi(argv[6]) : 64; double budget = argc > 7 ? atof(argv[7]) : 1100;
  auto t0 = chrono::steady_clock::now(); auto el = [&]() { return chrono::duration<double>(chrono::steady_clock::now() - t0).count(); };
  vector<Pt> Pc; { FILE* f = fopen(argv[3], "r"); Pt x{}; int v, k = 0; while (fscanf(f, "%d", &v) == 1) { x[k++] = v; if (k == n) { Pc.push_back(x); x = Pt{}; k = 0; } } fclose(f); }
  int M = Pc.size(); int W = (M + 63) / 64; vector<uint64_t> B((size_t)M * W, 0); auto row = [&](int i) { return &B[(size_t)i * W]; };
  for (int i = 0; i < M; i++) { row(i)[i / 64] |= 1ULL << (i % 64); for (int j = i + 1; j < M; j++) if (d1(Pc[i], Pc[j]) <= R) { row(i)[j / 64] |= 1ULL << (j % 64); row(j)[i / 64] |= 1ULL << (i % 64); } }
  vector<uint64_t> mask(W, 0); for (int j = 0; j < M; j++) mask[j / 64] |= 1ULL << (j % 64);
  vector<char> al(M, 1); int left = M; vector<int> nm(M); for (int i = 0; i < M; i++) nm[i] = nr(Pc[i]);
  vector<int> ord(M); iota(ord.begin(), ord.end(), 0); stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return nm[a] > nm[b]; });
  vector<int> byNorm(M); iota(byNorm.begin(), byNorm.end(), 0); stable_sort(byNorm.begin(), byNorm.end(), [&](int a, int b) { return nm[a] < nm[b]; });
  auto get = [&](int i, int j) { return (row(i)[j / 64] >> (j % 64)) & 1; };
  Pt EN{}; EN[n - 1] = 1; int en = -1; for (int i = 0; i < M; i++) if (Pc[i] == EN) en = i;
  auto kill = [&](int u) { al[u] = 0; mask[u / 64] &= ~(1ULL << (u % 64)); left--; };
  long long nD = 0, nK = 0; int pass = 0; bool changed = true, outOfTime = false;
  vector<uint64_t> Lm(W), bad(W);
  while (changed && left > 1 && !outOfTime) { changed = false; pass++;
    for (int u : ord) { if (!al[u] || left <= 1) continue; if (el() > budget) { outOfTime = true; break; }
      uint64_t* ru = row(u);
      // collect candidates with bad counts
      vector<pair<int,int>> cands; Pt S2[2] = {Pc[u], EN};
      for (int w : byNorm) { if (w == u || !al[w] || !get(u, w) || !inhullS(Pc[w], S2, 2)) continue;
        uint64_t* rw = row(w); int c = 0; for (int k = 0; k < W && c <= maxBad; k++) c += __builtin_popcountll(ru[k] & mask[k] & ~rw[k]);
        if (c == 0) { cands.clear(); cands.push_back({0, w}); break; } if (c <= maxBad) cands.push_back({c, w}); }
      if (cands.empty()) continue;
      if (cands[0].first == 0) { int w = cands[0].second; if (cert) { fprintf(cert, "D "); pr(cert, Pc[u]); fprintf(cert, "| "); pr(cert, Pc[w]); fprintf(cert, "\n"); } kill(u); nD++; changed = true; continue; }
      stable_sort(cands.begin(), cands.end());
      bool done = false;
      for (size_t ci = 0; ci < cands.size() && ci < 6 && !done; ci++) { int w = cands[ci].second; uint64_t* rw = row(w);
        for (int k = 0; k < W; k++) { Lm[k] = ru[k] & mask[k]; bad[k] = Lm[k] & ~rw[k]; } Lm[u / 64] &= ~(1ULL << (u % 64));
        vector<int> B0; for (int k = 0; k < W; k++) { uint64_t b = bad[k]; while (b) { int t = __builtin_ctzll(b); b &= b - 1; B0.push_back(k * 64 + t); } }
        vector<pair<int,int>> steps; vector<char> rem(B0.size(), 0); int remLeft = B0.size(); bool prog = true;
        while (remLeft && prog) { prog = false;
          for (size_t bi = 0; bi < B0.size(); bi++) { if (rem[bi]) continue; int b = B0[bi]; uint64_t* rb = row(b); Pt S3[3] = {Pc[u], Pc[b], EN}; int vf = -1;
            for (int k0 = 0; k0 < W && vf < 0; k0++) { uint64_t bits = Lm[k0] & rb[k0]; while (bits && vf < 0) { int v = k0 * 64 + __builtin_ctzll(bits); bits &= bits - 1;
              if (v == b || !inhullS(Pc[v], S3, 3)) continue;
              uint64_t* rv = row(v); bool ok = true; for (int k = 0; k < W; k++) if (rb[k] & Lm[k] & ~rv[k]) { ok = false; break; }
              if (ok) vf = v; } }
            if (vf < 0) continue; rem[bi] = 1; remLeft--; prog = true; Lm[b / 64] &= ~(1ULL << (b % 64)); steps.push_back({b, vf}); } }
        if (remLeft) continue;
        if (cert) { fprintf(cert, "K "); pr(cert, Pc[u]); fprintf(cert, "| "); pr(cert, Pc[w]); fprintf(cert, "%zu\n", steps.size()); for (auto& s : steps) { pr(cert, Pc[s.first]); fprintf(cert, "| "); pr(cert, Pc[s.second]); fprintf(cert, "\n"); } }
        kill(u); nK++; changed = true; done = true; } }
    vector<int> h(R + 1, 0); for (int i = 0; i < M; i++) if (al[i]) h[nm[i]]++;
    fprintf(stderr, "pass %d: left %d D=%lld K=%lld t=%.0fs by norm:", pass, left, nD, nK, el()); for (int k = 1; k <= R; k++) fprintf(stderr, " %d", h[k]); fprintf(stderr, "\n"); }
  bool okEnd = left == 1 && en >= 0 && al[en];
  printf("n=%d r=%d |C|=%d D=%lld K=%lld left=%d %s%s\n", n, R, M, nD, nK, left, okEnd ? "REACHES {e_n}" : "STUCK", outOfTime ? " (time budget)" : "");
  if (argc > 4 && string(argv[4]) != "-") { FILE* f = fopen(argv[4], "w"); for (int i = 0; i < M; i++) if (al[i]) { pr(f, Pc[i]); fprintf(f, "\n"); } fclose(f); }
  if (cert) fclose(cert); return okEnd ? 0 : 1;
}
