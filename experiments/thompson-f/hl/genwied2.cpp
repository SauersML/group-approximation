// Does a u = b v have a nonzero solution of degree D (letters <= L) for a random pair a, b in F_p[S]?
// A: F_p^{2|U|} -> F_p^{rows}, (u, v) -> a u - b v.  B = C A with C a random sparse 2|U| x rows matrix.
// Wiedemann: minimal polynomial of the sequence w^T B^i x (Berlekamp--Massey).
//   constant term != 0  =>  B nonsingular  =>  A injective (deterministic): no solution for this pair.
//   constant term == 0  =>  B singular (whp).  Then we build z = B-annihilated vector and test A z == 0.
//   A z == 0 with z != 0 is an explicit exact solution (u, v) for this specialization.
// usage: genwied D L "0,0;0,1;..." seed
#include <bits/stdc++.h>
using namespace std;
typedef vector<uint8_t> Word; typedef uint64_t u64; typedef unsigned __int128 u128;
static const u64 P = 2305843009213693951ULL;  // 2^61 - 1
static inline u64 mm(u64 a, u64 b) { u128 z = (u128)a * b; u64 lo = (u64)(z & P), hi = (u64)(z >> 61); u64 r = lo + hi; if (r >= P) r -= P; return r; }
static inline u64 ad(u64 a, u64 b) { u64 r = a + b; if (r >= P) r -= P; return r; }
static inline u64 sb(u64 a, u64 b) { return a >= b ? a - b : a + P - b; }
static u64 pw(u64 a, u64 e) { u64 r = 1; while (e) { if (e & 1) r = mm(r, a); a = mm(a, a); e >>= 1; } return r; }
static u64 iv(u64 a) { return pw(a, P - 2); }
static Word lml(int j, const Word& w) { Word o; o.reserve(w.size() + 1); size_t k = 0; while (k < w.size() && w[k] < j) { o.push_back(w[k]); j++; k++; } o.push_back((uint8_t)j); for (; k < w.size(); k++) o.push_back(w[k]); return o; }
static Word mul(const Word& a, const Word& b) { Word r = b; for (int i = (int)a.size() - 1; i >= 0; i--) r = lml(a[i], r); return r; }
struct VH { size_t operator()(const Word& w) const { size_t h = 1469598103934665603ULL; for (auto c : w) { h ^= c; h *= 1099511628211ULL; } return h; } };

int main(int argc, char** argv) {
  if (argc < 5) { fprintf(stderr, "usage: D L monomials seed\n"); return 1; }
  int D = atoi(argv[1]), L = atoi(argv[2]); u64 seed = strtoull(argv[4], 0, 10);
  vector<Word> S; { string spec = argv[3]; stringstream ss(spec); string mono; while (getline(ss, mono, ';')) { Word w; stringstream ms(mono); string lt; while (getline(ms, lt, ',')) w.push_back((uint8_t)stoi(lt)); S.push_back(w); } }
  auto t0 = chrono::steady_clock::now();
  vector<Word> U; Word cur(D, 0);
  function<void(int, int)> rec = [&](int pos, int lo) { if (pos == D) { U.push_back(cur); return; } for (int v = lo; v <= L; v++) { cur[pos] = (uint8_t)v; rec(pos + 1, v); } };
  rec(0, 0);
  size_t n = U.size(), k = S.size(), N = 2 * n;
  unordered_map<Word, uint32_t, VH> tid; tid.reserve(n * k * 2);
  vector<uint32_t> img(n * k);
  for (size_t y = 0; y < n; y++) for (size_t s = 0; s < k; s++) { Word z = mul(S[s], U[y]); auto it = tid.find(z); uint32_t id; if (it == tid.end()) { id = tid.size(); tid.emplace(move(z), id); } else id = it->second; img[y * k + s] = id; }
  size_t R = tid.size(); tid.clear(); tid.rehash(0);
  mt19937_64 rng(seed * 7919 + 17);
  auto rnd = [&]() { return rng() % (P - 1) + 1; };
  vector<u64> A(k), Bc(k); for (auto& x : A) x = rnd(); for (auto& x : Bc) x = rnd();
  if (getenv("PRINTCOEF")) { printf("alpha"); for (auto x : A) printf(" %llu", (unsigned long long)x); printf("\nbeta"); for (auto x : Bc) printf(" %llu", (unsigned long long)x); printf("\n"); }
  // C: N x R, each row 4 random entries
  const int CR = 4; vector<uint32_t> ccol(N * CR); vector<u64> cval(N * CR);
  for (size_t i = 0; i < N * CR; i++) { ccol[i] = rng() % R; cval[i] = rnd(); }
  vector<u64> tmpR(R);
  auto applyA = [&](const vector<u64>& x, vector<u64>& out) {  // out in F_p^R
    fill(out.begin(), out.end(), 0);
    for (size_t y = 0; y < n; y++) { u64 xu = x[y], xv = x[n + y]; if (!xu && !xv) continue;
      for (size_t s = 0; s < k; s++) { u64 c = sb(mm(A[s], xu), mm(Bc[s], xv)); uint32_t r = img[y * k + s]; out[r] = ad(out[r], c); } }
  };
  auto applyB = [&](const vector<u64>& x, vector<u64>& out) {
    applyA(x, tmpR);
    for (size_t i = 0; i < N; i++) { u64 acc = 0; for (int q = 0; q < CR; q++) acc = ad(acc, mm(cval[i * CR + q], tmpR[ccol[i * CR + q]])); out[i] = acc; }
  };
  vector<u64> w(N), x(N); for (auto& t : w) t = rnd(); for (auto& t : x) t = rnd();
  size_t M = 2 * N + 2; vector<u64> seq(M); vector<u64> cur_v = x, nxt(N);
  for (size_t i = 0; i < M; i++) { u64 acc = 0; for (size_t j = 0; j < N; j++) acc = ad(acc, mm(w[j], cur_v[j])); seq[i] = acc; if (i + 1 < M) { applyB(cur_v, nxt); cur_v.swap(nxt); } }
  // Berlekamp--Massey: connection polynomial Cp with seq[i] + sum_{j>=1} Cp[j] seq[i-j] = 0
  vector<u64> Cp{1}, Bp{1}; size_t Ldeg = 0, m = 1; u64 b = 1;
  for (size_t i = 0; i < M; i++) {
    u64 d = seq[i]; for (size_t j = 1; j <= Ldeg && j < Cp.size(); j++) d = ad(d, mm(Cp[j], seq[i - j]));
    if (d == 0) { m++; continue; }
    vector<u64> T = Cp; u64 coef = mm(d, iv(b)); if (Cp.size() < Bp.size() + m) Cp.resize(Bp.size() + m, 0);
    for (size_t j = 0; j < Bp.size(); j++) Cp[j + m] = sb(Cp[j + m], mm(coef, Bp[j]));
    if (2 * Ldeg <= i) { Ldeg = i + 1 - Ldeg; Bp = T; b = d; m = 1; } else m++;
  }
  Cp.resize(Ldeg + 1, 0);
  // minimal polynomial f(z) = z^L + Cp[1] z^{L-1} + ... + Cp[L]; constant term = Cp[L]
  u64 c0 = Cp[Ldeg];
  double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
  printf("{\"D\":%d,\"L\":%d,\"nS\":%zu,\"U\":%zu,\"rows\":%zu,\"minpoly_deg\":%zu,\"const_term_zero\":%s,\"seconds\":%.1f", D, L, k, n, R, Ldeg, c0 == 0 ? "true" : "false", secs);
  if (c0 == 0 && Ldeg > 0) {
    // f(z) = z * g(z); vector q = g(B) x ; apply B repeatedly until zero: last nonzero is in ker B.
    size_t t = 0; while (t < Ldeg && Cp[Ldeg - t] == 0) t++;  // f(z) = z^t h(z)
    // g(z) = f(z) / z^t = sum_{i=0}^{Ldeg-t} Cp[i] z^{Ldeg-t-i}
    size_t gdeg = Ldeg - t; vector<u64> q(N, 0), pv = x;
    for (size_t i = 0; i <= gdeg; i++) { u64 c = Cp[gdeg - i]; if (c) for (size_t j = 0; j < N; j++) q[j] = ad(q[j], mm(c, pv[j])); if (i < gdeg) { applyB(pv, nxt); pv.swap(nxt); } }
    // Horner check not needed; iterate B on q until it vanishes
    vector<u64> last = q; bool found = false; size_t iters = 0;
    while (iters <= t + 2) { bool zero = all_of(q.begin(), q.end(), [](u64 v) { return v == 0; }); if (zero) { found = iters > 0; break; } last = q; applyB(q, nxt); q.swap(nxt); iters++; }
    bool nonzero = any_of(last.begin(), last.end(), [](u64 v) { return v != 0; });
    vector<u64> outR(R); applyA(last, outR); bool inkerA = all_of(outR.begin(), outR.end(), [](u64 v) { return v == 0; });
    size_t su = 0, sv = 0; for (size_t y = 0; y < n; y++) { su += last[y] != 0; sv += last[n + y] != 0; }
    printf(",\"kernel_vector_found\":%s,\"in_ker_A\":%s,\"supp_u\":%zu,\"supp_v\":%zu", (found && nonzero) ? "true" : "false", inkerA ? "true" : "false", su, sv);
  }
  printf("}\n");
  return 0;
}
