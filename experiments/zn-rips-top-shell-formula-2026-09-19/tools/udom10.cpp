// udom10 n r ufile: udom9 with a choice of norm-two witness s e_j + e_n.  Env WIT=max: j = first index of max |u_j|
// (argmax witness); WIT=all: every j with u_j != 0 (reports the best); default: j = last nonzero index (formula).
// Env SIG=1 prints the step delta used for each unbalanced bad b.  The udom9 header follows.
// udom9 n r ufile: for each u in ufile (|u|=r, u_n=0, u>0), w=e_j+e_n.  Bad b in S0=N(u) cap Lmax_n (b!=u).
// Balanced b: count only (hand lemma T0).  Unbalanced b: search a universal dominator v: v in S0, v!=b, |v|<=r-1 or
// v_n>=1, d(v,w)<=r, v in hull(0,u,b,E), and d(z,v)<=r for all z in S0 cap N[b].  Candidates: b+delta (|delta|<=2),
// then every hull point of S0 (fallback).  Prints per-u line and totals; lists failures.
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <map>
#include <algorithm>
#include <functional>
#include <string>
using namespace std;
int n, r; typedef vector<int> P; vector<P> L;
static inline int d(const P& a, const P& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
int nm(const P& a) { int s = 0; for (int x : a) s += abs(x); return s; }
bool pos(const P& a) { int ln = 0; for (int t : a) if (t) ln = t; return ln > 0; }
void gen(P& x, int i, int rem) { if (i == n) { if (pos(x)) L.push_back(x); return; }
  int lo = (i == n - 1) ? 0 : -rem; for (int v = lo; v <= rem; v++) { x[i] = v; gen(x, i + 1, rem - abs(v)); } x[i] = 0; }
bool balv(const vector<int>& a, const vector<int>& y) { int s = a.size(); for (int m = 0; m < (1 << s); m++) { int A = 0, c = 0;
    for (int i = 0; i < s; i++) { int sg = (m >> i & 1) ? 1 : -1; A += sg * a[i]; c += sg * y[i]; } if (A >= 0 ? (c < 0 || c > A) : (c > 0 || c < A)) return false; } return true; }
map<vector<int>, bool> memo;
bool balancedPart(vector<int> a) { sort(a.begin(), a.end()); auto it = memo.find(a); if (it != memo.end()) return it->second;
  int s = a.size(), N = 0; for (int t : a) N += t; bool ok = false; vector<int> y(s, 0);
  // exhaustive over 0<=y<=a with 1<=|y|<=N/2
  function<void(int,int)> rec = [&](int i, int tot) { if (ok) return; if (i == s) { if (tot >= 1 && 2 * tot <= N && balv(a, y)) ok = true; return; }
    for (int t = 0; t <= a[i] && 2 * (tot + t) <= N; t++) { y[i] = t; rec(i + 1, tot + t); } y[i] = 0; };
  rec(0, 0); memo[a] = ok; return ok; }
int main(int argc, char** argv) {
  bool chk = getenv("CHKBAL") != 0; const char* wv = getenv("WIT"); bool wall = wv != 0 && string(wv) == "all"; bool sig = getenv("SIG") != 0; bool wmax = wv != 0 && string(wv) == "max"; n = atoi(argv[1]); r = atoi(argv[2]); P x(n, 0); gen(x, 0, r); fprintf(stderr, "|Lmax|=%zu\n", L.size());
  vector<P> D; for (int a = 0; a < n; a++) for (int sa = -1; sa <= 1; sa += 2) { P t(n, 0); t[a] = sa; D.push_back(t);
      for (int c = a; c < n; c++) for (int sc = -1; sc <= 1; sc += 2) { P t2 = t; t2[c] += sc; if (nm(t2) == 2) D.push_back(t2); } }
  sort(D.begin(), D.end()); D.erase(unique(D.begin(), D.end()), D.end());
  FILE* f = fopen(argv[3], "r"); long U = 0, NB = 0, NBAL = 0, NUNB = 0, NLOC = 0, NFAR = 0, NFAIL = 0; P u(n);
  while (true) { bool okr = true; for (int i = 0; i < n; i++) if (fscanf(f, "%d", &u[i]) != 1) okr = false; if (!okr) break; U++;
    int jl = -1; for (int i = 0; i < n; i++) if (u[i]) jl = i; long bestf = 1L<<40; int besti = -1; int im = -1; for (int i = 0; i < n; i++) if (u[i] && (im < 0 || abs(u[i]) > abs(u[im]))) im = i; if (wmax) jl = im;
    for (int j = 0; j < n; j++) { if (!u[j] || (!wall && j != jl)) continue; P w(n, 0); w[j] = u[j] > 0 ? 1 : -1; w[n - 1] = 1;
    vector<int> S; for (int a = 0; a < (int)L.size(); a++) if (d(L[a], u) <= r && L[a] != u) S.push_back(a);
    long nb = 0, nbal = 0, nunb = 0, nloc = 0, nfar = 0, nfail = 0;
    for (int a : S) { const P& b = L[a]; if (d(b, w) <= r) continue; nb++;
      vector<int> mag; for (int t : b) if (t) mag.push_back(abs(t)); bool isb = balancedPart(mag); if (isb) { nbal++; if (!chk) continue; } else nunb++;
      vector<const P*> Nb; for (int c : S) if (d(L[c], b) <= r) Nb.push_back(&L[c]);
      auto good = [&](const P& v) { if (v == b || v == u || !pos(v) || v[n - 1] < 0 || nm(v) > r || d(v, u) > r || d(v, w) > r || d(v, b) > r) return false;
        if (!(nm(v) <= r - 1 || v[n - 1] >= 1)) return false;
        for (int i = 0; i < n; i++) { int lo = min(0, min(u[i], b[i])), hi = max(i == n - 1 ? 1 : 0, max(u[i], b[i])); if (v[i] < lo || v[i] > hi) return false; }
        for (auto z : Nb) if (d(*z, v) > r) return false; return true; };
      bool found = false; P dlf; for (auto& dl : D) { P v = b; for (int i = 0; i < n; i++) v[i] += dl[i]; if (good(v)) { found = true; dlf = dl; break; } }
      if (found) { if (!isb) { nloc++; if (sig) { printf(" SIG i=%d u=", j); for (int t : u) printf("%d ", t); printf(" b="); for (int t : b) printf("%d ", t); printf(" d="); for (int t : dlf) printf("%d ", t); printf("\n"); } } continue; }
      for (int c : S) if (good(L[c])) { found = true; break; }
      if (found) { if (!isb) nfar++; continue; }
      nfail++; printf(isb ? " BALFAIL u=" : " FAIL u="); for (int t : u) printf("%d ", t); printf(" b="); for (int t : b) printf("%d ", t); printf("\n"); }
    if (nfail < bestf) { bestf = nfail; besti = j; }
    printf("u="); for (int t : u) printf("%d ", t); printf(" wi=%d |S0|", j); printf("=%zu bad=%ld bal=%ld unb=%ld local=%ld far=%ld fail=%ld\n", S.size(), nb, nbal, nunb, nloc, nfar, nfail); fflush(stdout);
    NB += nb; NBAL += nbal; NUNB += nunb; NLOC += nloc; NFAR += nfar; NFAIL += nfail; }
    printf("BEST u="); for (int t : u) printf("%d ", t); printf(" wi=%d fail=%ld\n", besti, bestf); fflush(stdout); }
  printf("TOTAL n=%d r=%d u=%ld bad=%ld balanced=%ld unbalanced=%ld local=%ld far=%ld fail=%ld\n", n, r, U, NB, NBAL, NUNB, NLOC, NFAR, NFAIL); }
