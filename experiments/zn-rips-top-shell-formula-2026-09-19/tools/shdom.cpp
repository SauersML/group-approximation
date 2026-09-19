// shdom n r ufile: argmax witness w = s e_i + e_n (i = first index of max |u_i|, s = sgn u_i).  Enumerates the bad set
// B = {b in Lmax : b_n = 0, s b_i <= 0, |b| in {r-1,r}, d(u,b) <= r, b != u} directly and, for every b (env ONLYUNB=1:
// unbalanced b only), searches v = b + delta (|delta| <= 2, delta_n in {0,1}) with: v != b,u; v in Lmax (v > 0, |v| <= r);
// v not in Z0 (|v| <= r-1 or v_n >= 1); d(v,w) <= r; v in hull(0,u,b,E); v in sh{0,u,b}, i.e. for every sign vector
// sigma: <sigma,v> >= min(0,<sigma,u>,<sigma,b>).  (Sign-hull lemma: then B(0,r) cap B(u,r) cap B(b,r) is inside B(v,r).)
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <map>
#include <algorithm>
#include <functional>
using namespace std;
bool ab = false; int n, r; typedef vector<int> P;
int nm(const P& a) { int s = 0; for (int x : a) s += abs(x); return s; }
int dd(const P& a, const P& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
bool pos(const P& a) { int ln = 0; for (int t : a) if (t) ln = t; return ln > 0; }
bool balv(const vector<int>& a, const vector<int>& y) { int s = a.size(); for (int m = 0; m < (1 << s); m++) { int A = 0, c = 0;
    for (int i = 0; i < s; i++) { int sg = (m >> i & 1) ? 1 : -1; A += sg * a[i]; c += sg * y[i]; } if (A >= 0 ? (c < 0 || c > A) : (c > 0 || c < A)) return false; } return true; }
map<vector<int>, bool> memo;
bool balancedPart(vector<int> a) { sort(a.begin(), a.end()); auto it = memo.find(a); if (it != memo.end()) return it->second;
  int s = a.size(), N = 0; for (int t : a) N += t; bool ok = false; vector<int> y(s, 0);
  function<void(int,int)> rec = [&](int i, int tot) { if (ok) return; if (i == s) { if (tot >= 1 && 2 * tot <= N && balv(a, y)) ok = true; return; }
    for (int t = 0; t <= a[i] && 2 * (tot + t) <= N; t++) { y[i] = t; rec(i + 1, tot + t); } y[i] = 0; };
  rec(0, 0); memo[a] = ok; return ok; }
bool insh(const P& v, const P& u, const P& b) { // sigma_n irrelevant when u_n = b_n = 0 only if v_n = 0; handle generally
  for (int m = 0; m < (1 << n); m++) { long sv = 0, su = 0, sb = 0; for (int t = 0; t < n; t++) { int sg = (m >> t & 1) ? 1 : -1; sv += sg * v[t]; su += sg * u[t]; sb += sg * b[t]; }
    if (sv < min(0L, min(su, sb))) return false; } return true; }
int main(int argc, char** argv) {
  n = atoi(argv[1]); r = atoi(argv[2]); bool onlyunb = getenv("ONLYUNB") != 0; bool wall = getenv("WIT") != 0; ab = getenv("ALLOWBAD") != 0;
  vector<P> D; for (int a = 0; a < n; a++) for (int sa = -1; sa <= 1; sa += 2) { P t(n, 0); t[a] = sa; D.push_back(t);
      for (int c = a; c < n; c++) for (int sc = -1; sc <= 1; sc += 2) { P t2 = t; t2[c] += sc; if (nm(t2) == 2) D.push_back(t2); } }
  { vector<P> D2; for (auto& t : D) if (t[n - 1] >= 0 && t[n - 1] <= 1) D2.push_back(t); D = D2; }
  sort(D.begin(), D.end(), [](const P& a, const P& b) { return nm(a) < nm(b) || (nm(a) == nm(b) && a < b); });
  FILE* f = fopen(argv[3], "r"); P u(n); long NFAR = 0; long U = 0, NB = 0, NUNB = 0, NFAIL = 0, NFU = 0;
  map<long, long> hist;
  while (true) { bool okr = true; for (int i = 0; i < n; i++) if (fscanf(f, "%d", &u[i]) != 1) okr = false; if (!okr) break; U++;
    int im0 = -1; for (int i = 0; i < n; i++) if (u[i] && (im0 < 0 || abs(u[i]) > abs(u[im0]))) im0 = i; vector<int> good;
    for (int im = 0; im < n; im++) { if (!u[im] || (!wall && im != im0)) continue; int s = u[im] > 0 ? 1 : -1;
    P w(n, 0); w[im] = s; w[n - 1] = 1; long nb = 0, nunb = 0, nfail = 0, nfar = 0; P b(n, 0);
    function<void(int,int,int)> rec = [&](int t, int nb_, int du) {
      if (nb_ > r || du > r) return;
      if (t == n - 1) { b[n - 1] = 0; if (nb_ < r - 1 || !pos(b) || b == u) return; nb++;
        vector<int> mag; for (int x : b) if (x) mag.push_back(abs(x)); bool isb = balancedPart(mag); if (!isb) nunb++; if (isb && onlyunb) return;
        for (auto& dl : D) { P v = b; for (int q = 0; q < n; q++) v[q] += dl[q];
          if (v == u || !pos(v) || nm(v) > r || (nm(v) == r && v[n - 1] == 0) || (dd(v, w) > r && !(ab && nm(v) < nm(b)))) continue;
          bool hu = true; for (int q = 0; q < n && hu; q++) { int lo = min(0, min(u[q], b[q])), hi = max(q == n - 1 ? 1 : 0, max(u[q], b[q])); if (v[q] < lo || v[q] > hi) hu = false; }
          if (!hu || !insh(v, u, b)) continue; return; }
        { P lo(n), hi(n), v(n); for (int q = 0; q < n; q++) { lo[q] = min(0, min(u[q], b[q])); hi[q] = max(q == n - 1 ? 1 : 0, max(u[q], b[q])); }
          bool fnd = false;
          function<void(int,int)> bx = [&](int q, int nv) { if (fnd || nv > r) return; if (q == n) {
              if (v == u || v == b || !pos(v) || (nv == r && v[n - 1] == 0) || (dd(v, w) > r && !(ab && nm(v) < nm(b))) || !insh(v, u, b)) return; fnd = true; return; }
            for (int x = lo[q]; x <= hi[q]; x++) { v[q] = x; bx(q + 1, nv + abs(x)); } v[q] = 0; };
          bx(0, 0); if (fnd) { nfar++; return; } }
        nfail++; if (!wall && NFAIL + nfail <= 30) { printf(" FAIL%s u=", isb ? "(bal)" : ""); for (int x : u) printf("%d ", x); printf(" b="); for (int x : b) printf("%d ", x); printf("\n"); } return; }
      for (int x = -r; x <= r; x++) { if (t == im && s * x > 0) continue; b[t] = x; rec(t + 1, nb_ + abs(x), du + abs(x - u[t])); } b[t] = 0; };
    rec(0, 0, 0);
    if (!nfail) good.push_back(im); if (!wall) { NB += nb; NUNB += nunb; NFAR += nfar; NFAIL += nfail; if (nfail) NFU++; } }
    if (wall) { if (good.empty()) NFU++; printf("GOOD u="); for (int x : u) printf("%d ", x); printf(" :"); for (int g : good) printf(" %d", g); printf("\n"); fflush(stdout); } }
  printf("TOTAL n=%d r=%d u=%ld bad=%ld unbalanced=%ld far=%ld fail=%ld failing_u=%ld (%s)\n", n, r, U, NB, NUNB, NFAR, NFAIL, NFU, onlyunb ? "unbalanced only" : "all bad");
}
