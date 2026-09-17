// Uniform reduction of all anti-lexicographic peeling links of VR(Z^n, d_1; r) at once.
//
// Peeling [0,m]^n in anti-lex order, the link of the removed vertex is Flag(L(I)) with
//   L(I) = { x in I : |x|_1 <= r, x > 0 },   I = prod [-a_i, b_i]  (a box containing 0),
// and Lmax = L([-r,r]^n) contains every L(I).  hull(S) = smallest box containing S.
// Uniform moves on a current set C (starting from Lmax); each is valid simultaneously for every
// C(I) = C cap L(I), because every point it uses lies in hull(0, x) or hull(0, x, y) subset I:
//  (D) remove x if N[x] cap C subset N[w] for some w in C cap hull(0,x), w != x.
//  (K) remove x if lk_C(x) = N(x) cap C collapses to one point p in hull(0,x) using only moves
//      "remove y if N[y] cap C' subset N[w], w in C' cap hull(0,x,y)" (C' = current link set).
// Restricting a valid sequence to L(I) keeps it valid (neighbourhoods only shrink, dominators and
// the final p stay present), so every Flag(L(I)) ~ Flag(L(I) cap K), K = survivors.
// Usage: uniform n r [useK=1] [outK] [certfile] [initfile|-] [dOnly=0] [budgetSeconds=0]
//   initfile: start from this subset of Lmax (e.g. the outK of an earlier dOnly run) instead of Lmax;
//             the certificate written is then the continuation of the earlier one (concatenate them).
//   dOnly=1 : stop after the D stage (lets a large case run in stages under a time limit).
//   budgetSeconds>0: stop the K stage at a move boundary once this many seconds have passed; outK then holds
//             the current set, and a rerun with initfile=outK continues.
// certfile lines: "D x | w" ; "K x | p m" followed by m lines "y | w" (link-collapse steps, in order).
#include <bits/stdc++.h>
using namespace std;
typedef array<int8_t, 12> Pt;
int n, r;
static inline int d1(const Pt& a, const Pt& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
static inline bool inhull3(const Pt& w, const Pt& x, const Pt& y) { // w in hull(0,x,y)
  for (int i = 0; i < n; i++) { int lo = min({0, (int)x[i], (int)y[i]}), hi = max({0, (int)x[i], (int)y[i]}); if (w[i] < lo || w[i] > hi) return false; } return true; }
struct Bits { int N, W; vector<uint64_t> a; void init(int n_) { N = n_; W = (N + 63) / 64; a.assign((size_t)N * W, 0); }
  inline uint64_t* row(int i) { return &a[(size_t)i * W]; } inline void set(int i, int j) { a[(size_t)i * W + j / 64] |= 1ULL << (j % 64); }
  inline bool get(int i, int j) const { return (a[(size_t)i * W + j / 64] >> (j % 64)) & 1; } };
long long nlink = 0, nlinkok = 0;
FILE* cert = nullptr;
static void pr(FILE* f, const Pt& a) { for (int i = 0; i < n; i++) fprintf(f, "%d ", a[i]); }
// collapse link of x (points Lk, all within r of x) with hull(0,x,y) dominators; return true iff one survivor in hull(0,x)
bool linkCollapse(const vector<Pt>& Lk, const Pt& x, vector<pair<int,int>>* steps, int* surv) {
  int N = Lk.size(); if (N == 0) return false;
  Bits B; B.init(N); int W = B.W;
  for (int i = 0; i < N; i++) { B.set(i, i); for (int j = i + 1; j < N; j++) if (d1(Lk[i], Lk[j]) <= r) { B.set(i, j); B.set(j, i); } }
  vector<uint64_t> mask(W, 0); for (int j = 0; j < N; j++) mask[j / 64] |= 1ULL << (j % 64);
  vector<char> alive(N, 1); int left = N;
  vector<int> nrm(N); for (int i = 0; i < N; i++) { int s = 0; for (int k = 0; k < n; k++) s += abs(Lk[i][k]); nrm[i] = s; }
  Pt zero{}; vector<char> inhx(N); for (int i = 0; i < N; i++) inhx[i] = inhull3(Lk[i], x, zero);
  vector<int> ord(N); iota(ord.begin(), ord.end(), 0);
  // remove far points first; keep points of hull(0,x) for last
  stable_sort(ord.begin(), ord.end(), [&](int a, int b) { if (inhx[a] != inhx[b]) return inhx[a] < inhx[b]; return nrm[a] > nrm[b]; });
  bool changed = true;
  while (changed && left > 1) { changed = false;
    for (int y : ord) { if (!alive[y] || left <= 1) continue;
      uint64_t* ry = B.row(y);
      for (int w = 0; w < N; w++) { if (w == y || !alive[w] || !B.get(y, w) || !inhull3(Lk[w], x, Lk[y])) continue;
        uint64_t* rw = B.row(w); bool ok = true;
        for (int k = 0; k < W; k++) if (ry[k] & mask[k] & ~rw[k]) { ok = false; break; }
        if (ok) { alive[y] = 0; mask[y / 64] &= ~(1ULL << (y % 64)); left--; changed = true; steps->push_back({y, w}); break; } } } }
  if (left != 1) return false;
  for (int i = 0; i < N; i++) if (alive[i]) { *surv = i; return inhx[i]; }
  return false;
}
int main(int argc, char** argv) {
  n = atoi(argv[1]); r = atoi(argv[2]); int useK = argc > 3 ? atoi(argv[3]) : 1;
  if (argc > 5) cert = fopen(argv[5], "w");
  bool useInit = argc > 6 && string(argv[6]) != "-"; int dOnly = argc > 7 ? atoi(argv[7]) : 0;
  double budget = argc > 8 ? atof(argv[8]) : 0; auto t0 = chrono::steady_clock::now(); bool outOfTime = false;
  auto elapsed = [&]() { return chrono::duration<double>(chrono::steady_clock::now() - t0).count(); };
  set<Pt> init;
  if (useInit) { FILE* f = fopen(argv[6], "r"); Pt x{}; int v, k = 0; while (fscanf(f, "%d", &v) == 1) { x[k++] = v; if (k == n) { init.insert(x); x = Pt{}; k = 0; } } fclose(f); }
  vector<Pt> P; { Pt x{}; for (int i = 0; i < n; i++) x[i] = (i == n - 1) ? 0 : -r;
    while (true) { int s = 0, last = 0; for (int i = 0; i < n; i++) { s += abs(x[i]); if (x[i]) last = x[i]; }
      if (s <= r && last > 0 && (!useInit || init.count(x))) P.push_back(x);
      int i = 0; while (i < n && x[i] == r) { x[i] = (i == n - 1) ? 0 : -r; i++; } if (i == n) break; x[i]++; } }
  int N = P.size(); Bits B; B.init(N); int W = B.W;
  for (int i = 0; i < N; i++) { B.set(i, i); for (int j = i + 1; j < N; j++) if (d1(P[i], P[j]) <= r) { B.set(i, j); B.set(j, i); } }
  vector<uint64_t> mask(W, 0); for (int j = 0; j < N; j++) mask[j / 64] |= 1ULL << (j % 64);
  vector<char> alive(N, 1); int left = N;
  vector<int> nrm(N); for (int i = 0; i < N; i++) { int s = 0; for (int k = 0; k < n; k++) s += abs(P[i][k]); nrm[i] = s; }
  vector<int> ord(N); iota(ord.begin(), ord.end(), 0);
  stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return nrm[a] > nrm[b]; });
  Pt zero{};
  vector<vector<int>> cand(N);
  for (int u = 0; u < N; u++) for (int w = 0; w < N; w++) if (w != u && B.get(u, w) && inhull3(P[w], P[u], zero)) cand[u].push_back(w);
  auto domD = [&](int u) { uint64_t* ru = B.row(u); for (int w : cand[u]) { if (!alive[w]) continue; uint64_t* rw = B.row(w); bool ok = true;
      for (int k = 0; k < W; k++) if (ru[k] & mask[k] & ~rw[k]) { ok = false; break; } if (ok) return true; } return false; };
  auto domW = [&](int u) { uint64_t* ru = B.row(u); for (int w : cand[u]) { if (!alive[w]) continue; uint64_t* rw = B.row(w); bool ok = true;
      for (int k = 0; k < W; k++) if (ru[k] & mask[k] & ~rw[k]) { ok = false; break; } if (ok) return w; } return -1; };
  auto kill = [&](int u) { alive[u] = 0; mask[u / 64] &= ~(1ULL << (u % 64)); left--; };
  int pass = 0; bool changed = true; int nD = 0, nK = 0;
  // stage 1: (D) only, to exhaustion
  auto Dmove = [&](int u) { int w = domW(u); if (w < 0) return false; if (cert) { fprintf(cert, "D "); pr(cert, P[u]); fprintf(cert, "| "); pr(cert, P[w]); fprintf(cert, "\n"); } kill(u); nD++; return true; };
  while (changed) { changed = false; pass++; for (int u : ord) if (alive[u] && Dmove(u)) changed = true; }
  fprintf(stderr, "stage D: left %d (passes %d)\n", left, pass);
  if (useK && !dOnly) { changed = true;
    while (changed) { changed = false; pass++;
      for (int u : ord) { if (!alive[u]) continue;
        if (budget > 0 && elapsed() > budget) { outOfTime = true; changed = false; break; }
        if (Dmove(u)) { changed = true; continue; }
        vector<Pt> Lk; for (int w = 0; w < N; w++) if (w != u && alive[w] && B.get(u, w)) Lk.push_back(P[w]);
        nlink++; vector<pair<int,int>> st; int sv = -1; if (linkCollapse(Lk, P[u], &st, &sv)) {
          if (cert) { fprintf(cert, "K "); pr(cert, P[u]); fprintf(cert, "| "); pr(cert, Lk[sv]); fprintf(cert, "%zu\n", st.size()); for (auto& q : st) { pr(cert, Lk[q.first]); fprintf(cert, "| "); pr(cert, Lk[q.second]); fprintf(cert, "\n"); } }
          kill(u); changed = true; nK++; } }
      fprintf(stderr, "pass %d left %d D=%d K=%d links=%lld\n", pass, left, nD, nK, nlink); } }
  vector<int> al(n, 0), be(n, 0);
  for (int i = 0; i < N; i++) if (alive[i]) for (int k = 0; k < n; k++) { al[k] = max(al[k], (int)-P[i][k]); be[k] = max(be[k], (int)P[i][k]); }
  if (outOfTime) printf("[stopped by time budget; continue from outK] ");
  printf("n=%d r=%d |Lmax|=%d |K|=%d D=%d K=%d extents:", n, r, N, left, nD, nK);
  for (int k = 0; k < n; k++) printf(" [-%d,%d]", al[k], be[k]); printf("\n");
  if (argc > 4) { FILE* f = fopen(argv[4], "w"); for (int i = 0; i < N; i++) if (alive[i]) { for (int k = 0; k < n; k++) fprintf(f, "%d ", P[i][k]); fprintf(f, "\n"); } fclose(f); }
  if (cert) fclose(cert);
}
