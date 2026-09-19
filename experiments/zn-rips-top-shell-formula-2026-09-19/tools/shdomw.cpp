// shdomw n r ufile: general witnesses w (|w|<=WMAX, all w in hull(0,u,E)), complete v box search.  Env TOPF=1: F = Top; TOPF=2: F = {x in Top : x_k <= 1}
// (w, v must have norm <= r-1; used for u in Top minus Z0), else F = Z0.  Env ONLYUNB=1: skip balanced u (Claim 3).
// Original shdom header follows: argmax witness w = s e_i + e_n (i = first index of max |u_i|, s = sgn u_i).  Enumerates the bad set
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
bool ab = false; int TOPF = 0; int n, r; typedef vector<int> P;
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
  n = atoi(argv[1]); r = atoi(argv[2]); int WMAX = getenv("WMAX") ? atoi(getenv("WMAX")) : 3; bool stop1 = getenv("STOP1") != 0; TOPF = getenv("TOPF") ? atoi(getenv("TOPF")) : 0; bool onlyunb = getenv("ONLYUNB") != 0; long SKIP = 0;
  vector<P> D; for (int a = 0; a < n; a++) for (int sa = -1; sa <= 1; sa += 2) { P t(n, 0); t[a] = sa; D.push_back(t);
      for (int c = a; c < n; c++) for (int sc = -1; sc <= 1; sc += 2) { P t2 = t; t2[c] += sc; if (nm(t2) == 2) D.push_back(t2); } }
  { vector<P> D2; for (auto& t : D) if (t[n - 1] >= 0 && t[n - 1] <= 1) D2.push_back(t); D = D2; }
  sort(D.begin(), D.end(), [](const P& a, const P& b) { return nm(a) < nm(b) || (nm(a) == nm(b) && a < b); });
  FILE* f = fopen(argv[3], "r"); P u(n); long U = 0, NFU = 0;
  while (true) { bool okr = true; for (int i = 0; i < n; i++) if (fscanf(f, "%d", &u[i]) != 1) okr = false; if (!okr) break;
    if (onlyunb) { vector<int> mg; for (int x : u) if (x) mg.push_back(abs(x)); if (balancedPart(mg)) { SKIP++; continue; } } U++;
    vector<P> W; P w(n, 0);
    function<void(int,int)> gw = [&](int q, int nw) { if (nw > WMAX) return; if (q == n) { if (nw < 1 || !pos(w) || w == u || dd(w, u) > r || (nw == r && (TOPF == 1 || w[n - 1] == 0 || (TOPF == 2 && w[n - 1] <= 1)))) return; W.push_back(w); return; }
      int lo = min(0, u[q]), hi = max(q == n - 1 ? 1 : 0, u[q]); for (int x = lo; x <= hi; x++) { w[q] = x; gw(q + 1, nw + abs(x)); } w[q] = 0; };
    gw(0, 0); { int im = -1; for (int i = 0; i < n; i++) if (u[i] && (im < 0 || abs(u[i]) > abs(u[im]))) im = i;
      auto key = [&](const P& a) { int k = nm(a) * 4; bool am = a[im] != 0 && a[n - 1] == 1 && nm(a) == 2; return am ? 0 : k + (a[n - 1] == 1 ? 0 : 1); };
      stable_sort(W.begin(), W.end(), [&](const P& a, const P& b) { return key(a) < key(b); }); }
    int ngood = 0; printf("u="); for (int x : u) printf("%d ", x); printf(" witnesses=%zu good:", W.size());
    for (auto& ww : W) { long nb = 0, nfail = 0; P b(n, 0); int nw = nm(ww);
      function<void(int,int,int)> rec = [&](int t, int nb_, int du) {
        if (nb_ > r || du > r || nfail) return;
        if (t == n) { if (nb_ < r - nw + 1 || !pos(b) || b == u || dd(b, ww) <= r) return; nb++;
          vector<int> mag; for (int x : b) if (x) mag.push_back(abs(x));
          for (auto& dl : D) { P v = b; for (int q = 0; q < n; q++) v[q] += dl[q];
            if (v == u || !pos(v) || v[n - 1] < 0 || nm(v) > r || (nm(v) == r && (TOPF == 1 || v[n - 1] == 0 || (TOPF == 2 && v[n - 1] <= 1))) || dd(v, ww) > r) continue;
            bool hu = true; for (int q = 0; q < n && hu; q++) { int lo = min(0, min(u[q], b[q])), hi = max(q == n - 1 ? 1 : 0, max(u[q], b[q])); if (v[q] < lo || v[q] > hi) hu = false; }
            if (!hu || !insh(v, u, b)) continue; return; }
          { P lo(n), hi(n), v(n); for (int q = 0; q < n; q++) { lo[q] = min(0, min(u[q], b[q])); hi[q] = max(q == n - 1 ? 1 : 0, max(u[q], b[q])); }
            bool fnd = false;
            function<void(int,int)> bx = [&](int q, int nv) { if (fnd || nv > r) return; if (q == n) {
                if (v == u || v == b || !pos(v) || (nv == r && (TOPF == 1 || v[n - 1] == 0 || (TOPF == 2 && v[n - 1] <= 1))) || dd(v, ww) > r || !insh(v, u, b)) return; fnd = true; return; }
              for (int x = lo[q]; x <= hi[q]; x++) { v[q] = x; bx(q + 1, nv + abs(x)); } v[q] = 0; };
            bx(0, 0); if (fnd) return; }
          nfail++; return; }
        int lo = (t == n - 1) ? 0 : -r; for (int x = lo; x <= r; x++) { b[t] = x; rec(t + 1, nb_ + abs(x), du + abs(x - u[t])); } b[t] = 0; };
      rec(0, 0, 0);
      if (!nfail) { ngood++; printf(" ["); for (int x : ww) printf("%d", x); printf("]"); if (stop1) break; } }
    printf("  ngood=%d\n", ngood); fflush(stdout); if (!ngood) NFU++; }
  printf("TOTAL n=%d r=%d u=%ld failing_u=%ld WMAX=%d TOPF=%d skipped_balanced=%ld\n", n, r, U, NFU, WMAX, (int)TOPF, SKIP);
}
