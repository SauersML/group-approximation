// Independent checker for a (D)-obstruction set K ⊆ Lmax_k = { x in Z^k : |x|_1 <= r, x > 0 }.
// Checks: K ⊆ Lmax_k, no duplicates, e_k ∈ K, K != {e_k}, and for every x ∈ K \ {e_k} and every
// w ∈ hull(0, x, e_k) ∩ Lmax_k with w != x there is z ∈ K with d(z, x) <= r < d(z, w)  (z = x when d(x, w) > r).
// Uses only pairwise distances inside K (no search over the ball).  Usage: ./kchk k r Kfile
#include <bits/stdc++.h>
using namespace std;
int n, R;
static int layer(const int* a) { for (int i = n - 1; i >= 0; i--) if (a[i]) return i; return -1; }
int main(int argc, char** argv) {
  n = atoi(argv[1]); R = atoi(argv[2]); FILE* f = fopen(argv[3], "r"); vector<array<int, 12>> K; set<array<int, 12>> S;
  while (true) { array<int, 12> a{}; bool ok = true; for (int i = 0; i < n; i++) if (fscanf(f, "%d", &a[i]) != 1) { ok = false; break; } if (!ok) break;
    int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); int L = layer(a.data());
    if (s > R || L < 0 || a[L] <= 0) { printf("FAIL: point not in Lmax\n"); return 1; }
    if (!S.insert(a).second) { printf("FAIL: duplicate\n"); return 1; } K.push_back(a); }
  array<int, 12> ek{}; ek[n - 1] = 1; if (!S.count(ek)) { printf("FAIL: e_k not in K\n"); return 1; }
  if (K.size() < 2) { printf("FAIL: K = {e_k}\n"); return 1; }
  auto d = [&](const array<int, 12>& a, const array<int, 12>& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; };
  long long pairs = 0, cands = 0;
  for (auto& x : K) { if (x == ek) continue;
    vector<const array<int, 12>*> nb; for (auto& z : K) if (d(z, x) <= R) nb.push_back(&z);
    array<int, 12> w{}; bool bad = false;
    function<void(int)> g = [&](int i) { if (bad) return; if (i < 0) { int s = 0; for (int t = 0; t < n; t++) s += abs(w[t]); int L = layer(w.data());
        if (s > R || L < 0 || w[L] <= 0 || w == x) return; cands++;
        bool blk = false; for (auto z : nb) { pairs++; if (d(*z, w) > R) { blk = true; break; } }
        if (!blk) { bad = true; printf("FAIL: x ="); for (int t = 0; t < n; t++) printf(" %d", x[t]); printf("  dominated by w ="); for (int t = 0; t < n; t++) printf(" %d", w[t]); printf("\n"); } return; }
      int lo = min(0, x[i]), hi = max(0, x[i]); if (i == n - 1) hi = max(hi, 1); for (int v = lo; v <= hi; v++) { w[i] = v; g(i - 1); } w[i] = 0; };
    g(n - 1); if (bad) return 1; }
  printf("OBSTRUCTION VERIFIED: k=%d r=%d |K|=%zu, every x in K\\{e_k} blocked for all %lld (x,w) pairs (%lld distance tests)\n", n, R, K.size(), cands, pairs);
}
