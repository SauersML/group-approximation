// Strong-collapse (vertex domination) of VR([0,m]^n, d_1; r).
// v is removed if some present w != v has N[v] subset N[w] (closed nbhds in current set).
// Removing a dominated vertex from a flag complex is a strong collapse (homotopy equivalence).
// Clamping Z^n -> [0,m]^n is 1-Lipschitz and idempotent, so VR(box) is a retract of VR(Z^n):
// a box whose VR complex is NOT contractible refutes contractibility of VR(Z^n; r).
// Usage: collapse n r m [maxdelta] [dumpcore]
#include <bits/stdc++.h>
using namespace std;
int n, r, m, K;
vector<vector<int>> offs(int rad) {
  vector<vector<int>> out; vector<int> o(n, -rad);
  while (true) {
    int s = 0; for (int x : o) s += abs(x);
    if (s <= rad) out.push_back(o);
    int i = 0; while (i < n && o[i] == rad) { o[i] = -rad; i++; }
    if (i == n) break; o[i]++;
  }
  return out;
}
int main(int argc, char** argv) {
  n = atoi(argv[1]); r = atoi(argv[2]); m = atoi(argv[3]);
  K = argc > 4 ? atoi(argv[4]) : 2;
  const char* dump = argc > 5 ? argv[5] : nullptr;
  long N = 1; for (int i = 0; i < n; i++) N *= (m + 1);
  vector<long> stride(n); { long s = 1; for (int i = 0; i < n; i++) { stride[i] = s; s *= (m + 1); } }
  vector<char> alive(N, 1);
  auto all = offs(r);
  vector<vector<int>> deltas; for (auto& d : offs(K)) { int s=0; for (int x:d) s+=abs(x); if (s>0) deltas.push_back(d); }
  // sort deltas by l1 length
  sort(deltas.begin(), deltas.end(), [](auto&a, auto&b){int sa=0,sb=0; for(int x:a)sa+=abs(x); for(int x:b)sb+=abs(x); return sa<sb;});
  vector<vector<vector<int>>> bad(deltas.size());
  for (size_t j = 0; j < deltas.size(); j++)
    for (auto& o : all) { int s = 0; for (int i = 0; i < n; i++) s += abs(o[i] - deltas[j][i]); if (s > r) bad[j].push_back(o); }
  // order: far from centre first
  vector<long> order(N); iota(order.begin(), order.end(), 0);
  vector<int> dc(N);
  for (long p = 0; p < N; p++) { long q = p; int s = 0; for (int i = 0; i < n; i++) { int c = q % (m + 1); q /= (m + 1); s += abs(2 * c - m); } dc[p] = s; }
  stable_sort(order.begin(), order.end(), [&](long a, long b) { return dc[a] > dc[b]; });
  long left = N; bool changed = true; int pass = 0;
  vector<int> c(n);
  while (changed && left > 1) {
    changed = false; pass++;
    for (long p : order) {
      if (!alive[p]) continue;
      { long q = p; for (int i = 0; i < n; i++) { c[i] = q % (m + 1); q /= (m + 1); } }
      for (size_t j = 0; j < deltas.size(); j++) {
        long wp = 0; bool ok = true;
        for (int i = 0; i < n; i++) { int x = c[i] + deltas[j][i]; if (x < 0 || x > m) { ok = false; break; } wp += x * stride[i]; }
        if (!ok || !alive[wp]) continue;
        bool dom = true;
        for (auto& o : bad[j]) {
          long up = 0; bool in = true;
          for (int i = 0; i < n; i++) { int x = c[i] + o[i]; if (x < 0 || x > m) { in = false; break; } up += x * stride[i]; }
          if (in && alive[up]) { dom = false; break; }
        }
        if (dom) { alive[p] = 0; left--; changed = true; break; }
      }
    }
    fprintf(stderr, "pass %d left %ld\n", pass, left);
  }
  printf("n=%d r=%d m=%d K=%d core=%ld passes=%d\n", n, r, m, K, left, pass);
  if (dump) { FILE* f = fopen(dump, "w");
    for (long p = 0; p < N; p++) if (alive[p]) { long q = p; for (int i = 0; i < n; i++) { fprintf(f, "%d ", (int)(q % (m + 1))); q /= (m + 1); } fprintf(f, "\n"); }
    fclose(f); }
}
