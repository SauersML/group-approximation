// Maximal stubborn subset of the PREFIX WORLD P_a(S) of the positive monoid M of Thompson's F.
//
// Background.  M = < x_0, x_1, ... | x_j x_i = x_i x_{j+1} (i<j) > is the monoid of forests of
// binary trees on the roots 0,1,2,..., almost all trivial; x_j z joins roots j, j+1 of z.
// For a finite homogeneous S subset M_d and w in S M_a put N(w) = { z : w in S z }.  A finite
// nonempty Z is STUBBORN if every z in Z has at most one w in S z with N(w) cap Z = {z}; a
// stubborn set forbids every private-pivot (triangular doubling) order for S, because the
// order-minimum of Z then has at most one private point
// (claim thompson-f-p22-monomials-admit-no-private-pivot-order, item 1).
//
// TAIL SPLITTING (this file's reason to exist).  Let K = K(S) = 2 + max last letter, so every
// s in S is a forest on K leaves with d carets and K-d roots.  Writing z = (u ; v) with u the
// first K roots, one has s z = (s.u ; v), and every factorisation w = s' z' keeps the SAME tail
// v.  Hence Z is stubborn iff each fibre Z_v = { u : (u;v) in Z } is stubborn in the finite
// prefix world
//       P_a = { forests with exactly K roots and a carets },   |P_a| = f(K+a, K),
// f(n,r) = (r/n) C(2n-r-1, n-1).  So core(M_D) != empty iff core(P_a) != empty for some a <= D,
// and no "letters <= L" truncation parameter is needed.  Products land in
//       B_a = { forests with K-d roots and a+d carets },  same number K+a of leaves.
// Both layers are ranked exactly by a lattice-path rank, so no hash table is used and the
// predecessor sets are recomputed locally by peeling.
//
// Usage:  prefix_core a "i1,i2;j1,j2;..." [corefile]
// Output: one JSON line.
#include <bits/stdc++.h>
using namespace std;

typedef unsigned long long u64;

struct Code {
  u64 b = 0;
  int len = 0;
};
static inline Code cat(Code a, Code c) { return Code{a.b | (c.b << a.len), a.len + c.len}; }
static inline int bit(const Code &c, int i) { return (int)((c.b >> i) & 1ULL); }

// ------------------------------------------------------------------ small tree helpers (setup)
struct Node {
  int l = -1, r = -1;
};  // -1,-1 = leaf
static vector<Node> pool;
static int mkleaf() { pool.push_back(Node{-1, -1}); return (int)pool.size() - 1; }
static int mkcaret(int a, int b) { pool.push_back(Node{a, b}); return (int)pool.size() - 1; }
static void emit(int t, Code &c) {
  if (pool[t].l < 0) { c.len += 1; return; }            // leaf: bit 0
  c.b |= 1ULL << c.len; c.len += 1;                      // caret: bit 1
  emit(pool[t].l, c); emit(pool[t].r, c);
}

// monomial (non-decreasing letters) -> forest on K leaves, as a Code
static Code mono_code(const vector<int> &w, int K) {
  vector<int> roots(K);
  for (int i = 0; i < K; i++) roots[i] = mkleaf();
  for (int i = (int)w.size() - 1; i >= 0; i--) {
    int j = w[i];
    if (j + 1 >= (int)roots.size()) { fprintf(stderr, "K too small\n"); exit(2); }
    int m = mkcaret(roots[j], roots[j + 1]);
    roots.erase(roots.begin() + j, roots.begin() + j + 2);
    roots.insert(roots.begin() + j, m);
  }
  Code c;
  for (int t : roots) emit(t, c);
  return c;
}

// ------------------------------------------------------------------ lattice-path rank/unrank
// A forest of r trees with n leaves is the bit word of length L = 2n-r with n zeros (leaves,
// bit 0) and n-r ones (carets, bit 1) in preorder, such that every PROPER prefix has
// #0 - #1 < r.  Order used: bit 1 before bit 0.
struct Layer {
  int n, r, L;
  vector<u64> cnt;  // cnt[pos*(W)+dd+off]
  int off, W;
  u64 total;
  void build(int n_, int r_) {
    n = n_; r = r_; L = 2 * n - r; off = n - r; W = n + 1;
    cnt.assign((size_t)(L + 1) * W, 0);
    auto at = [&](int pos, int dd) -> u64 & { return cnt[(size_t)pos * W + dd + off]; };
    at(L, r) = 1;
    for (int pos = L - 1; pos >= 0; pos--)
      for (int dd = -off; dd <= r; dd++) {
        if (((pos ^ dd) & 1) != 0) continue;  // parity
        int zeros = (pos + dd) / 2, ones = (pos - dd) / 2;
        if (zeros < 0 || ones < 0 || zeros > n || ones > n - r) continue;
        u64 v = 0;
        if (ones < n - r) v += at(pos + 1, dd - 1);
        if (zeros < n && (pos + 1 == L ? (dd + 1 == r) : (dd + 1 <= r - 1))) v += at(pos + 1, dd + 1);
        at(pos, dd) = v;
      }
    total = at(0, 0);
  }
  inline u64 rank(const Code &c) const {
    u64 rk = 0; int dd = 0;
    for (int pos = 0; pos < L; pos++) {
      int b = bit(c, pos);
      int zeros = (pos + dd) / 2, ones = (pos - dd) / 2;
      if (b == 0) {  // bit 1 branch comes first
        if (ones < n - r) rk += cnt[(size_t)(pos + 1) * W + (dd - 1) + off];
        dd += 1;
      } else {
        dd -= 1;
      }
      (void)zeros;
    }
    return rk;
  }
  inline Code unrank(u64 rk) const {
    Code c; c.len = L; int dd = 0;
    for (int pos = 0; pos < L; pos++) {
      int ones = (pos - dd) / 2, zeros = (pos + dd) / 2;
      u64 one_branch = 0;
      if (ones < n - r) one_branch = cnt[(size_t)(pos + 1) * W + (dd - 1) + off];
      (void)zeros;
      if (rk < one_branch) { c.b |= 1ULL << pos; dd -= 1; }
      else { rk -= one_branch; dd += 1; }
    }
    return c;
  }
};

// ------------------------------------------------------------------ forest surgery
// split a forest code into its r root-tree codes
static inline void split(const Code &c, int r, Code *out) {
  int pos = 0;
  for (int i = 0; i < r; i++) {
    int start = pos, bal = 0;
    do { bal += bit(c, pos) ? -1 : 1; pos++; } while (bal != 1);
    out[i] = Code{(c.b >> start) & ((pos - start) == 64 ? ~0ULL : ((1ULL << (pos - start)) - 1)),
                  pos - start};
  }
}
// w = s . u  (graft: the i-th leaf of s receives u's i-th root tree)
static inline Code graft(const Code &s, int K, const Code *ut) {
  Code w; int i = 0;
  for (int p = 0; p < s.len; p++) {
    if (bit(s, p)) { w.b |= 1ULL << w.len; w.len += 1; }
    else { w = cat(w, ut[i]); i++; }
  }
  (void)K;
  return w;
}
// u with s . u == w, or len<0 on failure
static inline Code peel(const Code &s, const Code &w) {
  Code u; int pos = 0;
  for (int p = 0; p < s.len; p++) {
    if (bit(s, p)) {
      if (pos >= w.len || !bit(w, pos)) return Code{0, -1};
      pos++;
    } else {
      int start = pos, bal = 0;
      do {
        if (pos >= w.len) return Code{0, -1};
        bal += bit(w, pos) ? -1 : 1; pos++;
      } while (bal != 1);
      u = cat(u, Code{(w.b >> start) & ((1ULL << (pos - start)) - 1), pos - start});
    }
  }
  if (pos != w.len) return Code{0, -1};
  return u;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: prefix_core a \"mono;mono;...\" [corefile]\n"); return 1; }
  int a = atoi(argv[1]);
  vector<vector<int>> S;
  { string spec = argv[2]; stringstream ss(spec); string mono;
    while (getline(ss, mono, ';')) { vector<int> w; stringstream ms(mono); string lt;
      while (getline(ms, lt, ',')) w.push_back(stoi(lt));
      if (!is_sorted(w.begin(), w.end())) { fprintf(stderr, "monomial not in normal form\n"); return 1; }
      S.push_back(w); } }
  int d = (int)S[0].size();
  for (auto &s : S) if ((int)s.size() != d) { fprintf(stderr, "S not homogeneous\n"); return 1; }
  // K(S) = the number of leaves S touches.  Applying x_{s_t} in s = x_{s_0}...x_{s_{d-1}} from the
  // right needs root s_t + 1 to still exist after d-1-t merges, i.e. K >= s_t + d - t + 1.
  int K = 0;
  for (auto &s : S) for (int t = 0; t < d; t++) K = max(K, s[t] + d - t + 1);
  int nS = (int)S.size();
  vector<Code> SC(nS);
  for (int i = 0; i < nS; i++) SC[i] = mono_code(S[i], K);
  for (int i = 0; i < nS; i++) for (int j = 0; j < i; j++)
    if (SC[i].b == SC[j].b && SC[i].len == SC[j].len) { fprintf(stderr, "duplicate monomial\n"); return 1; }

  int n = K + a;
  Layer A, B; A.build(n, K); B.build(n, K - d);
  if (A.L > 62 || B.L > 62) { fprintf(stderr, "code too long\n"); return 2; }
  size_t nA = (size_t)A.total, nB = (size_t)B.total;

  vector<u64> codes(nA);
  for (size_t i = 0; i < nA; i++) codes[i] = A.unrank(i).b;
  // self-test: rank is the inverse of unrank
  for (size_t t = 0; t < min<size_t>(nA, 1000); t++) {
    size_t i = (size_t)((double)t * nA / min<size_t>(nA, 1000));
    if (A.rank(Code{codes[i], A.L}) != i) { fprintf(stderr, "rank self-test failed\n"); return 3; }
  }

  vector<uint8_t> surv(nB, 0);
  vector<uint8_t> priv(nA, 0);
  vector<uint8_t> alive(nA, 1);
  Code ut[16];

  auto succ = [&](size_t i, int s) {
    Code u{codes[i], A.L};
    split(u, K, ut);
    return graft(SC[s], K, ut);
  };
  // pass 1: survivor counts
  for (size_t i = 0; i < nA; i++) {
    Code u{codes[i], A.L}; split(u, K, ut);
    for (int s = 0; s < nS; s++) {
      Code w = graft(SC[s], K, ut);
      u64 t = B.rank(w);
      if (surv[t] < 250) surv[t]++;
    }
  }
  // sanity: every product has a genuine peel back to its source
  {
    Code u{codes[0], A.L}; split(u, K, ut);
    for (int s = 0; s < nS; s++) {
      Code w = graft(SC[s], K, ut);
      Code z = peel(SC[s], w);
      if (z.len != A.L || z.b != codes[0]) { fprintf(stderr, "peel self-test failed\n"); return 3; }
    }
  }
  // pass 2: private counts
  vector<size_t> stack;
  for (size_t i = 0; i < nA; i++) {
    Code u{codes[i], A.L}; split(u, K, ut);
    int c = 0;
    for (int s = 0; s < nS; s++) if (surv[B.rank(graft(SC[s], K, ut))] == 1) c++;
    priv[i] = (uint8_t)min(c, 250);
    if (c >= 2) stack.push_back(i);
  }
  long long removed = 0;
  while (!stack.empty()) {
    size_t i = stack.back(); stack.pop_back();
    if (!alive[i] || priv[i] < 2) continue;
    alive[i] = 0; removed++;
    Code u{codes[i], A.L}; split(u, K, ut);
    for (int s = 0; s < nS; s++) {
      Code w = graft(SC[s], K, ut);
      u64 t = B.rank(w);
      if (surv[t] == 0) continue;
      if (--surv[t] == 1) {
        for (int s2 = 0; s2 < nS; s2++) {
          Code z = peel(SC[s2], w);
          if (z.len < 0) continue;
          size_t j = (size_t)A.rank(z);
          if (!alive[j]) continue;
          if (priv[j] < 250) priv[j]++;
          if (priv[j] >= 2) stack.push_back(j);
          break;
        }
      }
    }
  }
  // independent re-verification of stubbornness of the survivors, from scratch
  vector<size_t> core;
  for (size_t i = 0; i < nA; i++) if (alive[i]) core.push_back(i);
  bool verified = true;
  long long score = 0;
  if (!core.empty()) {
    unordered_map<u64, int> cnt2;
    cnt2.reserve(core.size() * nS * 2);
    for (size_t i : core) {
      Code u{codes[i], A.L}; split(u, K, ut);
      for (int s = 0; s < nS; s++) cnt2[graft(SC[s], K, ut).b]++;
    }
    score = (long long)cnt2.size();
    int maxpriv = 0;
    for (size_t i : core) {
      Code u{codes[i], A.L}; split(u, K, ut);
      int c = 0;
      for (int s = 0; s < nS; s++) if (cnt2[graft(SC[s], K, ut).b] == 1) c++;
      maxpriv = max(maxpriv, c);
    }
    verified = (maxpriv <= 1);
  }
  printf("{\"a\":%d,\"K\":%d,\"d\":%d,\"|S|\":%d,\"|P_a|\":%zu,\"|B_a|\":%zu,\"core\":%zu,"
         "\"|S.core|\":%lld,\"removed\":%lld,\"verified_stubborn\":%s}\n",
         a, K, d, nS, nA, nB, core.size(), score, removed, verified ? "true" : "false");
  if (argc >= 4 && !core.empty()) {
    FILE *f = fopen(argv[3], "w");
    for (size_t i : core) fprintf(f, "%llu\n", (unsigned long long)codes[i]);
    fclose(f);
  }
  (void)succ;
  return verified ? 0 : 4;
}
