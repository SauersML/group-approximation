// Maximal "stubborn" subset of a finite universe U = M_{D,L} of the positive monoid of F,
// for a homogeneous monomial set S.  (Obstruction to private-pivot orders.)
//
// M = < x_0, x_1, ... | x_j x_i = x_i x_{j+1} (i < j) >, normal forms x_{i_1}...x_{i_D},
// i_1 <= ... <= i_D.  For w in S*U let N(w) = { z in U : w in S z }.
// Z subset M_D is STUBBORN if every z in Z has at most one w in S z with N(w) cap Z = {z}.
// If a nonempty finite stubborn Z exists, no total order on M gives every m two private points
// in S m (claim thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs): the minimum z
// of Z has all its private points among { w in S z : N(w) cap Z = {z} }.
// Stubborn sets are closed under union, and the peeling below (remove any z having >= 2
// successors whose surviving predecessor set is {z}) never removes a point of a stubborn subset,
// so the survivor set is the maximal stubborn subset of U.  It is then re-verified from scratch.
//
// Usage: stubborn_core D L "0,0;0,1;..." [corefile]
// Output: one JSON line.
#include <bits/stdc++.h>
using namespace std;
typedef vector<uint8_t> Word;
typedef unsigned __int128 Key;

static Word left_mul_letter(int j, const Word& w) {
  Word out; out.reserve(w.size() + 1);
  size_t k = 0, n = w.size();
  while (k < n && w[k] < j) { out.push_back(w[k]); j++; k++; }
  if (j > 255) { fprintf(stderr, "letter overflow\n"); exit(2); }
  out.push_back((uint8_t)j);
  for (; k < n; k++) out.push_back(w[k]);
  return out;
}
static Word mul(const Word& a, const Word& b) {
  Word r = b;
  for (int i = (int)a.size() - 1; i >= 0; i--) r = left_mul_letter(a[i], r);
  return r;
}
static Key key_of(const Word& w) {
  if (w.size() > 20) { fprintf(stderr, "word too long\n"); exit(2); }
  Key k = (Key)w.size();
  for (size_t i = 0; i < w.size(); i++) {
    if (w[i] > 63) { fprintf(stderr, "letter too large for key\n"); exit(2); }
    k |= (Key)w[i] << (8 + 6 * i);
  }
  return k;
}
struct KeyHash { size_t operator()(const Key& k) const {
  uint64_t lo = (uint64_t)k, hi = (uint64_t)(k >> 64);
  return std::hash<uint64_t>()(lo * 0x9E3779B97F4A7C15ULL ^ hi); } };

static void selftest() {
  for (int i = 0; i < 5; i++) for (int j = i + 1; j < 7; j++) {
    Word a = mul(Word{(uint8_t)j}, Word{(uint8_t)i});
    if (!(a.size() == 2 && a[0] == i && a[1] == j + 1)) { fprintf(stderr, "relation fail\n"); exit(3); }
  }
  mt19937 rng(7);
  for (int t = 0; t < 20000; t++) {
    Word w[3];
    for (int q = 0; q < 3; q++) { int len = rng() % 5; for (int z = 0; z < len; z++) w[q].push_back(rng() % 6); sort(w[q].begin(), w[q].end()); }
    if (mul(mul(w[0], w[1]), w[2]) != mul(w[0], mul(w[1], w[2]))) { fprintf(stderr, "assoc fail\n"); exit(3); }
  }
}

static string wstr(const Word& w) { string s; for (size_t i = 0; i < w.size(); i++) { if (i) s += ","; s += to_string(w[i]); } return s; }

int main(int argc, char** argv) {
  if (argc < 4) { fprintf(stderr, "usage: D L monomials [corefile]\n"); return 1; }
  selftest();
  int D = atoi(argv[1]), L = atoi(argv[2]);
  vector<Word> S; { string spec = argv[3]; stringstream ss(spec); string mono;
    while (getline(ss, mono, ';')) { Word w; stringstream ms(mono); string lt; while (getline(ms, lt, ',')) w.push_back((uint8_t)stoi(lt));
      if (!is_sorted(w.begin(), w.end())) { fprintf(stderr, "monomial not in normal form\n"); return 1; } S.push_back(w); } }
  int nS = S.size();
  vector<Word> U; Word cur(D, 0);
  function<void(int, int)> rec = [&](int pos, int lo) {
    if (pos == D) { U.push_back(cur); return; }
    for (int v = lo; v <= L; v++) { cur[pos] = (uint8_t)v; rec(pos + 1, v); }
  };
  rec(0, 0);
  int nU = U.size();
  unordered_map<Key, int, KeyHash> tidx; tidx.reserve((size_t)nU * nS);
  vector<int> adj((size_t)nU * nS);
  for (int y = 0; y < nU; y++) for (int s = 0; s < nS; s++) {
    Word p = mul(S[s], U[y]); Key k = key_of(p);
    auto itr = tidx.find(k); int id;
    if (itr == tidx.end()) { id = tidx.size(); tidx.emplace(k, id); } else id = itr->second;
    adj[(size_t)y * nS + s] = id;
    for (int s2 = 0; s2 < s; s2++) if (adj[(size_t)y * nS + s2] == id) { fprintf(stderr, "cancellation fail\n"); return 3; }
  }
  int nT = tidx.size();
  { unordered_map<Key, int, KeyHash>().swap(tidx); }
  // predecessor CSR
  vector<int> start(nT + 1, 0), pred((size_t)nU * nS);
  for (size_t e = 0; e < adj.size(); e++) start[adj[e] + 1]++;
  for (int t = 0; t < nT; t++) start[t + 1] += start[t];
  { vector<int> fillp(start.begin(), start.end() - 1);
    for (int y = 0; y < nU; y++) for (int s = 0; s < nS; s++) pred[fillp[adj[(size_t)y * nS + s]]++] = y; }
  // peeling
  vector<char> alive(nU, 1);
  vector<int> surv(nT), priv(nU, 0);
  for (int t = 0; t < nT; t++) surv[t] = start[t + 1] - start[t];
  for (int y = 0; y < nU; y++) for (int s = 0; s < nS; s++) if (surv[adj[(size_t)y * nS + s]] == 1) priv[y]++;
  vector<int> stack;
  for (int y = 0; y < nU; y++) if (priv[y] >= 2) stack.push_back(y);
  long long removed = 0;
  while (!stack.empty()) {
    int y = stack.back(); stack.pop_back();
    if (!alive[y] || priv[y] < 2) continue;
    alive[y] = 0; removed++;
    for (int s = 0; s < nS; s++) {
      int t = adj[(size_t)y * nS + s];
      if (--surv[t] == 1) {
        for (int e = start[t]; e < start[t + 1]; e++) if (alive[pred[e]]) {
          int z = pred[e]; if (++priv[z] >= 2) stack.push_back(z); break; }
      }
    }
  }
  // independent verification of stubbornness of the survivors
  vector<int> core; for (int y = 0; y < nU; y++) if (alive[y]) core.push_back(y);
  vector<int> surv2(nT, 0);
  for (int y : core) for (int s = 0; s < nS; s++) surv2[adj[(size_t)y * nS + s]]++;
  int maxpriv = 0; long long priv0 = 0, priv1 = 0;
  for (int y : core) { int c = 0; for (int s = 0; s < nS; s++) if (surv2[adj[(size_t)y * nS + s]] == 1) c++;
    maxpriv = max(maxpriv, c); if (c == 0) priv0++; else if (c == 1) priv1++; }
  bool verified = (maxpriv <= 1);
  // recompute products directly from words for the core (no hash reuse)
  if (!core.empty()) {
    map<Word, int> cnt; for (int y : core) for (int s = 0; s < nS; s++) cnt[mul(S[s], U[y])]++;
    for (int y : core) { int c = 0; for (int s = 0; s < nS; s++) if (cnt[mul(S[s], U[y])] == 1) c++; if (c > 1) verified = false; }
    long long sy = cnt.size();
    printf("{\"D\":%d,\"L\":%d,\"S\":\"%s\",\"U\":%d,\"SU\":%d,\"core\":%zu,\"S_core\":%lld,\"core_priv0\":%lld,\"core_priv1\":%lld,\"verified_stubborn\":%s,\"first_core_word\":\"%s\"}\n",
      D, L, argv[3], nU, nT, core.size(), sy, priv0, priv1, verified ? "true" : "false", wstr(U[core[0]]).c_str());
  } else {
    printf("{\"D\":%d,\"L\":%d,\"S\":\"%s\",\"U\":%d,\"SU\":%d,\"core\":0,\"removed\":%lld}\n", D, L, argv[3], nU, nT, removed);
  }
  if (argc >= 5 && !core.empty()) { FILE* f = fopen(argv[4], "w"); for (int y : core) fprintf(f, "%s\n", wstr(U[y]).c_str()); fclose(f); }
  return verified ? 0 : 4;
}
