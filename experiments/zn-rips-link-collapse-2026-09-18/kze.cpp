// kze (kz with neighbour-first dominator search and periodic early stop): lifted (D) + (K) engine with compact certificates (E = e_n).
// D x | w : w in C, w != x, w in hull(0,x,E), N[x] cap C subset N[w].
// K u | w : S = N(u) cap C minus u, w in S cap hull(0,u,E).  The verifier runs the maximal protected collapse of S:
//           repeatedly remove b in cur, b != w, having v in cur, v != b, v in hull(0,u,b,E), N[b] cap cur subset N[v];
//           success iff at the end cur subset N[w].  (The verifier re-derives the steps; soundness does not depend on their order.)
// The engine computes the unprotected core Z of S, prefers w in Z with Z subset N[w], and otherwise confirms a
// candidate w by running the protected collapse itself.
// Usage: ./kz n r startfile outcore cert [budgetSec=1100] [order=0] [protTries=4]
#include <bits/stdc++.h>
#include <immintrin.h>
using namespace std;
typedef array<int8_t, 12> Pt;
int n, R;
static inline int d1(const Pt& a, const Pt& b) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i] - b[i]); return s; }
static inline int nr(const Pt& a) { int s = 0; for (int i = 0; i < n; i++) s += abs(a[i]); return s; }
static inline bool inh(const Pt& w, const Pt& a, const Pt& b, const Pt& c) { for (int i = 0; i < n; i++) {
    int lo = min({0, (int)a[i], (int)b[i], (int)c[i]}), hi = max({0, (int)a[i], (int)b[i], (int)c[i]}); if (w[i] < lo || w[i] > hi) return false; } return true; }
static void pr(FILE* f, const Pt& a) { for (int i = 0; i < n; i++) fprintf(f, "%d ", a[i]); }
int main(int argc, char** argv) {
  n = atoi(argv[1]); R = atoi(argv[2]);
  FILE* cert = string(argv[5]) != "-" ? fopen(argv[5], "w") : nullptr;
  double budget = argc > 6 ? atof(argv[6]) : 1100; int order = argc > 7 ? atoi(argv[7]) : 0; int protTries = argc > 8 ? atoi(argv[8]) : 4;
  auto t0 = chrono::steady_clock::now(); auto el = [&]() { return chrono::duration<double>(chrono::steady_clock::now() - t0).count(); };
  vector<Pt> Pc; { FILE* f = fopen(argv[3], "r"); Pt x{}; int v, k = 0; while (fscanf(f, "%d", &v) == 1) { x[k++] = v; if (k == n) { Pc.push_back(x); x = Pt{}; k = 0; } } fclose(f); }
  int M = Pc.size(); int W = (M + 63) / 64; vector<uint64_t> B((size_t)M * W, 0); auto row = [&](int i) { return &B[(size_t)i * W]; };
  for (int i = 0; i < M; i++) { row(i)[i / 64] |= 1ULL << (i % 64); for (int j = i + 1; j < M; j++) if (d1(Pc[i], Pc[j]) <= R) { row(i)[j / 64] |= 1ULL << (j % 64); row(j)[i / 64] |= 1ULL << (i % 64); } }
  fprintf(stderr, "M=%d adjacency built t=%.0fs\n", M, el());
  vector<uint64_t> mask(W, 0); for (int j = 0; j < M; j++) mask[j / 64] |= 1ULL << (j % 64);
  unordered_map<uint64_t,int> gid; auto key = [&](const Pt& a) { uint64_t h = 0; for (int i = 0; i < n; i++) h = h * 64 + (uint64_t)(a[i] + 32); return h; };
  for (int i = 0; i < M; i++) gid[key(Pc[i])] = i; vector<int> loc(M, -1);
  vector<char> al(M, 1); int left = M; vector<int> nm(M); for (int i = 0; i < M; i++) nm[i] = nr(Pc[i]);
  vector<int> ord(M); iota(ord.begin(), ord.end(), 0);
  if (order == 0) stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return nm[a] > nm[b]; });
  else stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return nm[a] < nm[b]; });
  Pt EN{}; EN[n - 1] = 1; Pt Z0{}; int en = -1; for (int i = 0; i < M; i++) if (Pc[i] == EN) en = i;
  auto kill = [&](int u) { al[u] = 0; mask[u / 64] &= ~(1ULL << (u % 64)); left--; };
  long long nD = 0, nK = 0, nKz = 0, nKp = 0, nFail = 0; int pass = 0; bool changed = true, outOfTime = false;
  bool dmode = true;
  while (left > 1 && !outOfTime) { changed = false; pass++;
    for (int u : ord) { if (!al[u] || u == en || left <= 1) continue; if (el() > budget) { outOfTime = true; break; }
      uint64_t* ru = row(u);
      vector<int> L; for (int k = 0; k < W; k++) { uint64_t b = ru[k] & mask[k]; while (b) { int t = __builtin_ctzll(b); b &= b - 1; int j = k * 64 + t; if (j != u) L.push_back(j); } }
      // (D)
      int dw = -1; for (int j : L) { if (!inh(Pc[j], Pc[u], EN, Z0)) continue; uint64_t* rw = row(j); bool ok = true;
        for (int k = 0; k < W; k++) if (ru[k] & mask[k] & ~rw[k]) { ok = false; break; } if (ok) { dw = j; break; } }
      if (dw >= 0) { if (cert) { fprintf(cert, "D "); pr(cert, Pc[u]); fprintf(cert, "| "); pr(cert, Pc[dw]); fprintf(cert, "\n"); } kill(u); nD++; changed = true; continue; }
      if (dmode) continue;
      // (K)
      int s = L.size(); int SW = (s + 63) / 64; vector<int> cands;
      for (int li = 0; li < s; li++) if (inh(Pc[L[li]], Pc[u], EN, Z0)) cands.push_back(li);
      if (cands.empty()) continue;
      vector<uint64_t> LA((size_t)s * SW, 0); auto lr = [&](int i) { return &LA[(size_t)i * SW]; };
      // compact global rows onto the link with pext (L is sorted ascending)
      vector<pair<int,uint64_t>> wm; for (int k = 0; k < W; k++) { uint64_t m = ru[k] & mask[k]; if (k == u / 64) m &= ~(1ULL << (u % 64)); if (m) wm.push_back({k, m}); }
      for (int i = 0; i < s; i++) { uint64_t* ri = row(L[i]); uint64_t* li = lr(i); int pos = 0;
        for (auto& pm : wm) { uint64_t bits = _pext_u64(ri[pm.first], pm.second); int c = __builtin_popcountll(pm.second);
          int q = pos >> 6, o = pos & 63; li[q] |= bits << o; if (o && o + c > 64) li[q + 1] |= bits >> (64 - o); pos += c; } }
      auto covers = [&](const vector<uint64_t>& cur, int w) { uint64_t* rw = lr(w); for (int k = 0; k < SW; k++) if (cur[k] & ~rw[k]) return false; return true; };
      for (int i = 0; i < s; i++) loc[L[i]] = i;
      auto dominated = [&](const vector<uint64_t>& cur, int b, int v) { uint64_t* rb = lr(b); uint64_t* rv = lr(v); for (int k = 0; k < SW; k++) if (rb[k] & cur[k] & ~rv[k]) return false; return true; };
      auto stopNow = [&](const vector<uint64_t>& cur, int prot) { if (prot >= 0) return covers(cur, prot);
        for (int c : cands) if (((cur[c / 64] >> (c % 64)) & 1) && covers(cur, c)) return true; return false; };
      auto collapse = [&](vector<uint64_t>& cur, int prot) {
        bool prog = true;
        while (prog) { prog = false; if (stopNow(cur, prot)) return; int sinceCheck = 0;
          for (int b = 0; b < s; b++) { if (b == prot || !((cur[b / 64] >> (b % 64)) & 1)) continue; uint64_t* rb = lr(b); const Pt& pb = Pc[L[b]];
            bool found = false;
            // first try the lattice neighbours b +- e_i inside hull(0,u,b,E)
            for (int i = 0; i < n && !found; i++) { int lo = min({0, (int)Pc[u][i], (int)pb[i], (int)EN[i]}), hi = max({0, (int)Pc[u][i], (int)pb[i], (int)EN[i]});
              for (int dl = -1; dl <= 1 && !found; dl += 2) { int nv = pb[i] + dl; if (nv < lo || nv > hi) continue; Pt q = pb; q[i] = nv;
                auto it = gid.find(key(q)); if (it == gid.end()) continue; int v = loc[it->second]; if (v < 0 || !((cur[v / 64] >> (v % 64)) & 1)) continue;
                if (dominated(cur, b, v)) found = true; } }
            for (int k0 = 0; k0 < SW && !found; k0++) { uint64_t bits = cur[k0] & rb[k0];
              while (bits) { int v = k0 * 64 + __builtin_ctzll(bits); bits &= bits - 1; if (v == b || !inh(Pc[L[v]], Pc[u], pb, EN)) continue;
                if (dominated(cur, b, v)) { found = true; break; } } }
            if (found) { cur[b / 64] &= ~(1ULL << (b % 64)); prog = true; if (++sinceCheck >= 256) { sinceCheck = 0; if (stopNow(cur, prot)) return; } } } } };
      vector<uint64_t> cur(SW, 0); for (int i = 0; i < s; i++) cur[i / 64] |= 1ULL << (i % 64);
      collapse(cur, -1);
      int wl = -1; vector<pair<int,int>> other;
      for (int c : cands) { if (covers(cur, c)) { if ((cur[c / 64] >> (c % 64)) & 1) { wl = c; break; } other.push_back({0, c}); }
        else { int cnt = 0; uint64_t* rw = lr(c); for (int k = 0; k < SW; k++) cnt += __builtin_popcountll(cur[k] & ~rw[k]); other.push_back({cnt, c}); } }
      bool viaZ = wl >= 0;
      if (wl < 0) { sort(other.begin(), other.end());
        for (int t = 0; t < (int)other.size() && t < protTries; t++) { int c = other[t].second; vector<uint64_t> c2(SW, 0); for (int i = 0; i < s; i++) c2[i / 64] |= 1ULL << (i % 64);
          collapse(c2, c); if (covers(c2, c)) { wl = c; break; } } }
      for (int i = 0; i < s; i++) loc[L[i]] = -1;
      if (wl < 0) { nFail++; continue; }
      if (cert) { fprintf(cert, "K "); pr(cert, Pc[u]); fprintf(cert, "| "); pr(cert, Pc[L[wl]]); fprintf(cert, "\n"); }
      kill(u); nK++; if (viaZ) nKz++; else nKp++; changed = true;
      if (nK % 200 == 0) { fprintf(stderr, "  K=%lld (viaZ %lld, prot %lld) D=%lld fail=%lld left=%d t=%.0fs\n", nK, nKz, nKp, nD, nFail, left, el()); fflush(stderr); if (cert) fflush(cert); } }
    vector<int> h(R + 1, 0); for (int i = 0; i < M; i++) if (al[i]) h[nm[i]]++;
    fprintf(stderr, "pass %d: left %d D=%lld K=%lld (viaZ %lld prot %lld) fail=%lld t=%.0fs by norm:", pass, left, nD, nK, nKz, nKp, nFail, el()); for (int k = 1; k <= R; k++) fprintf(stderr, " %d", h[k]); fprintf(stderr, " %s\n", dmode ? "[D sweep]" : "[D+K sweep]"); nFail = 0;
    if (dmode) { if (!changed) dmode = false; } else { if (!changed) break; dmode = true; } }
  bool okEnd = left == 1 && en >= 0 && al[en];
  printf("n=%d r=%d |C|=%d D=%lld K=%lld left=%d %s%s\n", n, R, M, nD, nK, left, okEnd ? "REACHES {e_n}" : "STUCK", outOfTime ? " (time budget)" : "");
  if (string(argv[4]) != "-") { FILE* f = fopen(argv[4], "w"); for (int i = 0; i < M; i++) if (al[i]) { pr(f, Pc[i]); fprintf(f, "\n"); } fclose(f); }
  if (cert) fclose(cert); return okEnd ? 0 : 1;
}
