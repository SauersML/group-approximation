// Link-type certificate for contractibility of VR(Z^n, d_1; r).
// Peel the box [0,m]^n in anti-lexicographic order (x < y iff at the largest index where they
// differ, x_i < y_i). When the current least vertex delta is removed, its link is the flag complex
// on L(delta) = { x in ([0,m]^n - delta) : |x|_1 <= r, x > 0 }.  Since |x_i| <= r it depends only on
// a_i = min(delta_i, r), b_i = min(m - delta_i, r), and for i = n only b_n matters (x > 0 forces x_n >= 0).
// Reduction (coordinate clipping, GSS Lemma 3.3, reproved in the proof file): L(I) is homotopy
// equivalent to L(I cap [-c,c]^n), c = floor(r/2). So it suffices that for every
//   a_1..a_{n-1}, b_1..b_n in {0..c}, not all b = 0,
// Flag(L) is contractible. This program certifies each type by explicit greedy vertex removal:
//   (D) u dominated: N[u] subset N[w] for an alive w != u  (strong collapse), or
//   (K) lk(u) in the current set is itself certified contractible by the same procedure (depth-1).
// Every step is checked on the actual adjacency bitsets; a type is certified iff one vertex remains.
// Usage: typecheck n r depth [chunk nchunks [seqfile]]
#include <bits/stdc++.h>
using namespace std;
typedef vector<int8_t> Pt;
int n, r, c;
static inline int d1(const Pt& a, const Pt& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
long long nlink = 0;
size_t collapse(const vector<Pt>& P, int depth, vector<Pt>* core) {
  int N = P.size();
  if (N <= 1) { if (core) *core = P; return N; }
  int W = (N + 63) / 64;
  vector<uint64_t> adj((size_t)N * W, 0);
  for (int i = 0; i < N; i++) { adj[(size_t)i * W + i / 64] |= 1ULL << (i % 64);
    for (int j = i + 1; j < N; j++) if (d1(P[i], P[j]) <= r) { adj[(size_t)i * W + j / 64] |= 1ULL << (j % 64); adj[(size_t)j * W + i / 64] |= 1ULL << (i % 64); } }
  vector<uint64_t> mask(W, 0); for (int j = 0; j < N; j++) mask[j / 64] |= 1ULL << (j % 64);
  vector<char> alive(N, 1);
  vector<int> ord(N); iota(ord.begin(), ord.end(), 0);
  vector<int> nrm(N); for (int i = 0; i < N; i++) { int s = 0; for (int k = 0; k < n; k++) s += abs(P[i][k]); nrm[i] = s; }
  stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return nrm[a] > nrm[b]; });
  // candidate dominators: alive neighbours sorted by distance (closest first), limited list
  vector<vector<int>> cand(N);
  for (int u = 0; u < N; u++) {
    vector<pair<int,int>> v;
    for (int w = 0; w < N; w++) if (w != u) { int dd = d1(P[u], P[w]); if (dd <= r && nrm[w] < nrm[u]) v.push_back({dd, w}); }
    sort(v.begin(), v.end()); for (auto& p : v) cand[u].push_back(p.second);
  }
  int left = N; bool changed = true;
  auto dominated = [&](int u, int w) {
    for (int k = 0; k < W; k++) if (adj[(size_t)u * W + k] & mask[k] & ~adj[(size_t)w * W + k]) return false;
    return true; };
  while (changed && left > 1) {
    changed = false;
    for (int u : ord) {
      if (!alive[u] || left <= 1) continue;
      bool rem = false;
      for (int w : cand[u]) if (alive[w] && dominated(u, w)) { rem = true; break; }
      if (!rem) { // try any alive neighbour (including farther from origin)
        for (int w = 0; w < N && !rem; w++) if (w != u && alive[w] && ((adj[(size_t)u * W + w / 64] >> (w % 64)) & 1) && nrm[w] >= nrm[u] && dominated(u, w)) rem = true;
      }
      if (!rem && depth > 0) {
        vector<Pt> L; for (int w = 0; w < N; w++) if (w != u && alive[w] && ((adj[(size_t)u * W + w / 64] >> (w % 64)) & 1)) L.push_back(P[w]);
        nlink++;
        if (!L.empty() && collapse(L, depth - 1, nullptr) == 1) rem = true;
      }
      if (rem) { alive[u] = 0; mask[u / 64] &= ~(1ULL << (u % 64)); left--; changed = true; }
    }
  }
  if (core) { core->clear(); for (int i = 0; i < N; i++) if (alive[i]) core->push_back(P[i]); }
  return left;
}
// Phase 1: uniform domination on the maximal type Lmax = {x in [-r,r]^{n-1}x[0,r]: |x|_1<=r, x>0}.
// Only "between" dominators w (|w_i|<=|x_i|, w_i x_i>=0, w>0) are used, so w lies in every L(I) containing x.
// A fixed removal sequence valid on Lmax restricts to a valid sequence on every L(I) (current(I) = L(I) cap current(max),
// and N[x] cap current(I) subset N[w] cap current(I)). Hence every L(I) ~ L(I) cap K, K = survivors.
vector<Pt> phase1(vector<Pt> P, vector<pair<Pt,Pt>>* seq) {
  int N = P.size(); int W = (N + 63) / 64;
  vector<uint64_t> adj((size_t)N * W, 0);
  for (int i = 0; i < N; i++) { adj[(size_t)i * W + i / 64] |= 1ULL << (i % 64);
    for (int j = i + 1; j < N; j++) if (d1(P[i], P[j]) <= r) { adj[(size_t)i * W + j / 64] |= 1ULL << (j % 64); adj[(size_t)j * W + i / 64] |= 1ULL << (i % 64); } }
  vector<uint64_t> mask(W, 0); for (int j = 0; j < N; j++) mask[j / 64] |= 1ULL << (j % 64);
  vector<char> alive(N, 1);
  vector<int> nrm(N); for (int i = 0; i < N; i++) { int s = 0; for (int k = 0; k < n; k++) s += abs(P[i][k]); nrm[i] = s; }
  vector<int> ord(N); iota(ord.begin(), ord.end(), 0);
  stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return nrm[a] > nrm[b]; });
  auto between = [&](const Pt& w, const Pt& x) { int last = 0; for (int i = 0; i < n; i++) { if (abs(w[i]) > abs(x[i]) || w[i] * x[i] < 0) return false; if (w[i]) last = w[i]; } return last > 0; };
  vector<vector<int>> cand(N);
  for (int u = 0; u < N; u++) { vector<pair<int,int>> v; for (int w = 0; w < N; w++) if (w != u && between(P[w], P[u]) && d1(P[u], P[w]) <= r) v.push_back({d1(P[u], P[w]), w}); sort(v.begin(), v.end()); for (auto& p : v) cand[u].push_back(p.second); }
  bool changed = true;
  while (changed) { changed = false;
    for (int u : ord) { if (!alive[u]) continue;
      for (int w : cand[u]) { if (!alive[w]) continue; bool ok = true;
        for (int k = 0; k < W; k++) if (adj[(size_t)u * W + k] & mask[k] & ~adj[(size_t)w * W + k]) { ok = false; break; }
        if (ok) { alive[u] = 0; mask[u / 64] &= ~(1ULL << (u % 64)); changed = true; if (seq) seq->push_back({P[u], P[w]}); break; } } } }
  vector<Pt> K; for (int i = 0; i < N; i++) if (alive[i]) K.push_back(P[i]); return K;
}
int main(int argc, char** argv) {
  n = atoi(argv[1]); r = atoi(argv[2]); int depth = atoi(argv[3]);
  long chunk = argc > 5 ? atol(argv[4]) : 0, nchunks = argc > 5 ? atol(argv[5]) : 1;
  c = r;
  vector<Pt> Lmax; { Pt x(n); vector<int> lo(n, -r), hi(n, r); lo[n-1] = 0; for (int i = 0; i < n; i++) x[i] = lo[i];
    while (true) { int s = 0, last = 0; for (int i = 0; i < n; i++) { s += abs(x[i]); if (x[i]) last = x[i]; }
      if (s <= r && last > 0) Lmax.push_back(x);
      int i = 0; while (i < n && x[i] == hi[i]) { x[i] = lo[i]; i++; } if (i == n) break; x[i]++; } }
  vector<pair<Pt,Pt>> seq;
  vector<Pt> K = phase1(Lmax, &seq);
  if (argc > 6) { FILE* f = fopen(argv[6], "w");
    for (auto& pr : seq) { for (int i = 0; i < n; i++) fprintf(f, "%d ", pr.first[i]); fprintf(f, "| "); for (int i = 0; i < n; i++) fprintf(f, "%d ", pr.second[i]); fprintf(f, "\n"); }
    fclose(f); }
  vector<int> alpha(n, 0), beta(n, 0);
  for (auto& p : K) for (int i = 0; i < n; i++) { alpha[i] = max(alpha[i], (int)-p[i]); beta[i] = max(beta[i], (int)p[i]); }
  printf("phase1: |Lmax|=%zu |K|=%zu extents:", Lmax.size(), K.size()); for (int i = 0; i < n; i++) printf(" [-%d,%d]", alpha[i], beta[i]); printf("\n"); fflush(stdout);
  set<vector<int8_t>> Kset(K.begin(), K.end());
  long ntypes = 1; for (int i = 0; i < n - 1; i++) ntypes *= (alpha[i] + 1); for (int i = 0; i < n; i++) ntypes *= (beta[i] + 1);
  long certified = 0, failed = 0, skipped = 0; size_t maxpts = 0;
  auto t0 = chrono::steady_clock::now();
  for (long t = 0; t < ntypes; t++) {
    if (t % nchunks != chunk) continue;
    vector<int> a(n, 0), b(n, 0); long q = t;
    for (int i = 0; i < n - 1; i++) { a[i] = q % (alpha[i] + 1); q /= (alpha[i] + 1); }
    for (int i = 0; i < n; i++) { b[i] = q % (beta[i] + 1); q /= (beta[i] + 1); }
    bool any = false; for (int i = 0; i < n; i++) if (b[i] > 0) any = true;
    if (!any) { skipped++; continue; }
    vector<Pt> P; Pt x(n);
    // enumerate x in prod [-a_i, b_i], |x|_1 <= r, x > 0 (last nonzero coordinate positive)
    vector<int> lo(n), hi(n); for (int i = 0; i < n; i++) { lo[i] = -a[i]; hi[i] = b[i]; }
    for (int i = 0; i < n; i++) x[i] = lo[i];
    while (true) {
      int s = 0, last = 0; for (int i = 0; i < n; i++) { s += abs(x[i]); if (x[i]) last = x[i]; }
      if (s <= r && last > 0 && Kset.count(x)) P.push_back(x);
      int i = 0; while (i < n && x[i] == hi[i]) { x[i] = lo[i]; i++; } if (i == n) break; x[i]++;
    }
    maxpts = max(maxpts, P.size());
    vector<Pt> core;
    size_t left = collapse(P, depth, &core);
    if (left == 1) certified++;
    else { failed++; printf("FAIL type a=");
      for (int i = 0; i < n - 1; i++) printf("%d", a[i]); printf(" b="); for (int i = 0; i < n; i++) printf("%d", b[i]);
      printf(" |L|=%zu core=%zu\n", P.size(), left); fflush(stdout); }
  }
  double sec = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
  printf("n=%d r=%d c=%d depth=%d chunk=%ld/%ld types=%ld certified=%ld failed=%ld skipped=%ld maxpts=%zu linkcalls=%lld sec=%.1f\n",
         n, r, c, depth, chunk, nchunks, ntypes, certified, failed, skipped, maxpts, nlink, sec);
}
