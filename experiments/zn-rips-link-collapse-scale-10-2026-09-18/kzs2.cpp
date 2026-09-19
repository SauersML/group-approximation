// kzs2: kzs with AVX-512 neighbourhood and link-row builds (8 packed points per vpsadbw, the compare mask is one byte
// of the row).  Same scan order, same moves, same certificate as kzs.
// kzs: kzh with IMPLICIT adjacency (n <= 8): no M x M bit matrix; every neighbourhood is recomputed with vpsadbw from the
// packed coordinates of the live points (a dead point's packed word is all-ones, so it is never within r). Memory is
// O(M + s^2/8) for a link of size s, so (8,10) fits in 2GB. Same scan order, same moves, same certificate as kzh/kzf.
// kzh: kzf plus two search-order switches (KZ_KFIRST=1: skip the opening D-only sweep; KZ_KSEL=1: attempt (K) only at u with |u|=r, u_n=0). Same moves, same certificate format.
// kzf: kze (../zn-rips-link-collapse-2026-09-18/kze.cpp) with a vpsadbw adjacency build for n <= 8; same moves, same certificate format. Lifted (D) + (K) engine, E = e_n.
// D x | w : w in C, w != x, w in hull(0,x,E), N[x] cap C subset N[w].
// K u | w : S = N(u) cap C minus u, w in S cap hull(0,u,E).  The verifier runs the maximal protected collapse of S:
//           repeatedly remove b in cur, b != w, having v in cur, v != b, v in hull(0,u,b,E), N[b] cap cur subset N[v];
//           success iff at the end cur subset N[w].  (Confluent: the final set does not depend on the order.)
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
  int M = Pc.size(); if (n > 8) { fprintf(stderr, "kzs needs n <= 8\n"); return 2; }
  int Mp = (M + 7) / 8 * 8; vector<uint64_t> pk(Mp, ~0ULL); // byte t = coordinate t + 64
  for (int i = 0; i < M; i++) { uint64_t z = 0; for (int t = 0; t < 8; t++) z |= (uint64_t)(uint8_t)((t < n ? Pc[i][t] : 0) + 64) << (8 * t); pk[i] = z; }
  const __m256i lim = _mm256_set1_epi64x(R + 1);
  // nbr(q, P, np, out): indices j < np with d1(q, P[j]) <= R, ascending; P padded with ~0 to a multiple of 4
  const __m512i lim8 = _mm512_set1_epi64(R);
  auto nbr = [&](uint64_t q, const uint64_t* P, int np, vector<int>& out) { out.clear(); const __m512i a = _mm512_set1_epi64((long long)q);
    for (int j = 0; j < np; j += 8) { __m512i s = _mm512_sad_epu8(a, _mm512_loadu_si512((const void*)&P[j]));
      unsigned m = _mm512_cmple_epu64_mask(s, lim8); while (m) { int t = __builtin_ctz(m); m &= m - 1; out.push_back(j + t); } } };
  const __m256i limR = _mm256_set1_epi64x(R);
  // allNear(q, P, np): every P[j] (j < np) within R of q (padding ~0 entries must be excluded by np)
  auto allNear = [&](uint64_t q, const uint64_t* P, int np) { const __m256i a = _mm256_set1_epi64x((long long)q); int j = 0;
    for (; j + 4 <= np; j += 4) { __m256i s = _mm256_sad_epu8(a, _mm256_loadu_si256((const __m256i*)&P[j]));
      if (_mm256_movemask_pd(_mm256_castsi256_pd(_mm256_cmpgt_epi64(s, limR)))) return false; }
    for (; j < np; j++) { uint64_t x = q, y = P[j]; int d = 0; for (int t = 0; t < 8; t++) d += abs((int)((x >> (8 * t)) & 255) - (int)((y >> (8 * t)) & 255)); if (d > R) return false; }
    return true; };
  fprintf(stderr, "M=%d packed (implicit adjacency) t=%.0fs\n", M, el());
  unordered_map<uint64_t,int> gid; auto key = [&](const Pt& a) { uint64_t h = 0; for (int i = 0; i < n; i++) h = h * 64 + (uint64_t)(a[i] + 32); return h; };
  for (int i = 0; i < M; i++) gid[key(Pc[i])] = i; vector<int> loc(M, -1);
  vector<char> al(M, 1); int left = M; vector<int> nm(M); for (int i = 0; i < M; i++) nm[i] = nr(Pc[i]);
  vector<int> ord(M); iota(ord.begin(), ord.end(), 0);
  if (order == 0) stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return nm[a] > nm[b]; });
  else stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return nm[a] < nm[b]; });
  Pt EN{}; EN[n - 1] = 1; Pt Z0{}; int en = -1; for (int i = 0; i < M; i++) if (Pc[i] == EN) en = i;
  auto kill = [&](int u) { al[u] = 0; pk[u] = ~0ULL; left--; };
  vector<int> L; vector<uint64_t> Lp;
  long long nD = 0, nK = 0, nKz = 0, nKp = 0, nFail = 0; int pass = 0; bool changed = true, outOfTime = false;
  bool dmode = !getenv("KZ_KFIRST"); const bool ksel = getenv("KZ_KSEL") != nullptr, donly = getenv("KZ_DONLY") != nullptr;
  // KZ_KLIST=file: attempt (K) only at the listed points (as kzh); KZ_DONLY=1: D sweeps only, stop at the D-stall set
  vector<char> kok(M, 1); if (getenv("KZ_KLIST")) { fill(kok.begin(), kok.end(), 0); FILE* f = fopen(getenv("KZ_KLIST"), "r"); Pt x{}; int v, k = 0, c = 0;
    while (fscanf(f, "%d", &v) == 1) { x[k++] = v; if (k == n) { auto it = gid.find(key(x)); if (it != gid.end()) { kok[it->second] = 1; c++; } x = Pt{}; k = 0; } } fclose(f); fprintf(stderr, "KLIST: %d points present\n", c); }
  while (left > 1 && !outOfTime) { changed = false; pass++;
    for (int u : ord) { if (!al[u] || u == en || left <= 1) continue; if (el() > budget) { outOfTime = true; break; }
      nbr(pk[u], pk.data(), Mp, L); L.erase(find(L.begin(), L.end(), u));
      { int s0 = L.size(); Lp.assign((s0 + 7) / 8 * 8, ~0ULL); for (int i = 0; i < s0; i++) Lp[i] = pk[L[i]]; }
      // (D)
      int dw = -1; for (int j : L) { if (!inh(Pc[j], Pc[u], EN, Z0)) continue; if (allNear(pk[j], Lp.data(), (int)L.size())) { dw = j; break; } }
      if (dw >= 0) { if (cert) { fprintf(cert, "D "); pr(cert, Pc[u]); fprintf(cert, "| "); pr(cert, Pc[dw]); fprintf(cert, "\n"); } kill(u); nD++; changed = true; continue; }
      if (dmode) continue;
      if (ksel && (nm[u] != R || Pc[u][n - 1] != 0)) continue;
      if (!kok[u]) continue;
      // (K)
      int s = L.size(); int SW = (s + 63) / 64; vector<int> cands;
      for (int li = 0; li < s; li++) if (inh(Pc[L[li]], Pc[u], EN, Z0)) cands.push_back(li);
      if (cands.empty()) continue;
      vector<uint64_t> LA((size_t)s * SW, 0); auto lr = [&](int i) { return &LA[(size_t)i * SW]; };
      // link rows by vpsadbw among the link points (L ascending, so the bit order is that of kzf's pext compaction)
      for (int i = 0; i < s; i++) { uint8_t* li = (uint8_t*)lr(i); const __m512i a = _mm512_set1_epi64((long long)Lp[i]);
        for (int j = 0; j < (int)Lp.size(); j += 8) { __m512i sd = _mm512_sad_epu8(a, _mm512_loadu_si512((const void*)&Lp[j]));
          li[j / 8] = (uint8_t)_mm512_cmple_epu64_mask(sd, lim8); } }
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
    if (dmode) { if (!changed) { if (donly) break; dmode = false; } } else { if (!changed) break; dmode = true; } }
  bool okEnd = left == 1 && en >= 0 && al[en];
  printf("n=%d r=%d |C|=%d D=%lld K=%lld left=%d %s%s\n", n, R, M, nD, nK, left, okEnd ? "REACHES {e_n}" : "STUCK", outOfTime ? " (time budget)" : "");
  if (string(argv[4]) != "-") { FILE* f = fopen(argv[4], "w"); for (int i = 0; i < M; i++) if (al[i]) { pr(f, Pc[i]); fprintf(f, "\n"); } fclose(f); }
  if (cert) fclose(cert); return okEnd ? 0 : 1;
}
