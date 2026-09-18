// Recursive link-collapse certificate for VR(P, d_1; r), P a finite subset of Z^n.
// A vertex v of a flag complex X may be deleted when lk(v) = Flag(N(v)) is contractible:
// X = (X - v) u cone(lk v), glued along lk v, so X ~ X - v. lk(v) is certified contractible
// by running the same procedure (depth-1) on N(v) until one vertex remains. Depth 0 = plain
// vertex domination (N[u] subset N[w]; lk(u) is then a cone on w).
// Box mode:  linkcollapse box n r m depth     (P = [0,m]^n; VR(box) is a retract of VR(Z^n))
// File mode: linkcollapse file n r depth path (P = points in file)
// Prints core size; "core=1" certifies VR(P;r) contractible.
#include <bits/stdc++.h>
using namespace std;
int n, r;
typedef vector<int> Pt;
static inline int d1(const Pt& a, const Pt& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
long long linkcalls = 0;
// returns remaining points after greedy collapse
vector<Pt> collapse(vector<Pt> P, int depth, bool top) {
  int N = P.size();
  if (N <= 1) return P;
  int W = (N + 63) / 64;
  vector<uint64_t> adj((size_t)N * W, 0);
  for (int i = 0; i < N; i++) for (int j = 0; j < N; j++) if (d1(P[i], P[j]) <= r) adj[(size_t)i * W + j / 64] |= 1ULL << (j % 64);
  vector<char> alive(N, 1); vector<uint64_t> mask(W, 0);
  for (int j = 0; j < N; j++) mask[j / 64] |= 1ULL << (j % 64);
  // order: far from centroid first
  vector<double> cen(n, 0); for (auto& p : P) for (int i = 0; i < n; i++) cen[i] += p[i] / (double)N;
  vector<int> ord(N); iota(ord.begin(), ord.end(), 0);
  vector<double> key(N); for (int i = 0; i < N; i++) { double s = 0; for (int k = 0; k < n; k++) s += fabs(P[i][k] - cen[k]); key[i] = s; }
  stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return key[a] > key[b]; });
  int left = N; bool changed = true; int pass = 0;
  while (changed && left > 1) {
    changed = false; pass++;
    for (int u : ord) {
      if (!alive[u] || left <= 1) continue;
      bool rem = false;
      // domination: N[u] & mask subset N[w]
      for (int w = 0; w < N && !rem; w++) {
        if (w == u || !alive[w]) continue;
        if (!((adj[(size_t)u * W + w / 64] >> (w % 64)) & 1)) continue;
        bool sub = true;
        for (int k = 0; k < W; k++) { uint64_t x = adj[(size_t)u * W + k] & mask[k] & ~adj[(size_t)w * W + k]; if (x) { sub = false; break; } }
        if (sub) rem = true;
      }
      if (!rem && depth > 0) {
        vector<Pt> L;
        for (int w = 0; w < N; w++) if (w != u && alive[w] && ((adj[(size_t)u * W + w / 64] >> (w % 64)) & 1)) L.push_back(P[w]);
        linkcalls++;
        if (!L.empty() && collapse(L, depth - 1, false).size() == 1) rem = true;
      }
      if (rem) { alive[u] = 0; mask[u / 64] &= ~(1ULL << (u % 64)); left--; changed = true; }
    }
    if (top) fprintf(stderr, "pass %d left %d linkcalls %lld\n", pass, left, linkcalls);
  }
  vector<Pt> out; for (int i = 0; i < N; i++) if (alive[i]) out.push_back(P[i]);
  return out;
}
int main(int argc, char** argv) {
  string mode = argv[1]; n = atoi(argv[2]); r = atoi(argv[3]);
  vector<Pt> P; int depth; string tag;
  if (mode == "box") {
    int m = atoi(argv[4]); depth = atoi(argv[5]);
    Pt c(n, 0);
    while (true) { P.push_back(c); int i = 0; while (i < n && c[i] == m) { c[i] = 0; i++; } if (i == n) break; c[i]++; }
    tag = "box m=" + to_string(m);
  } else {
    depth = atoi(argv[4]); ifstream f(argv[5]); Pt c(n);
    while (true) { for (int i = 0; i < n; i++) f >> c[i]; if (!f) break; P.push_back(c); }
    tag = string("file ") + argv[5];
  }
  auto core = collapse(P, depth, true);
  printf("n=%d r=%d %s depth=%d |P|=%zu core=%zu linkcalls=%lld\n", n, r, tag.c_str(), depth, P.size(), core.size(), linkcalls);
  if (argc > 6 && mode == "box") { FILE* f = fopen(argv[6], "w"); for (auto& p : core) { for (int x : p) fprintf(f, "%d ", x); fprintf(f, "\n"); } fclose(f); }
}
