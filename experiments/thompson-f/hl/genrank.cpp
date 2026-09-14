// Generic solvability of a u = b v in K[M] for a, b supported on a homogeneous monomial set S of
// Thompson's F positive monoid M, with u, v homogeneous of degree D and letters <= L.
// Coefficients of a, b are random in F_p (p = 2^31 - 1); by Schwartz--Zippel the rank of the map
// (u, v) -> a u - b v equals the generic rank with high probability.
// Output: |U|, rank, kernel dimension = 2|U| - rank (kernel > 0 means a solution exists for this
// specialization; if it persists across seeds, the generic pair is solvable in degree D).
// usage: genrank D L "0,0;0,1;..." seed
#include <bits/stdc++.h>
using namespace std;
typedef vector<uint8_t> Word;
typedef uint64_t u64;
static const u64 P = 2147483647ULL;
static u64 mulm(u64 a, u64 b) { return (a * b) % P; }
static u64 powm(u64 a, u64 e) { u64 r = 1; while (e) { if (e & 1) r = mulm(r, a); a = mulm(a, a); e >>= 1; } return r; }
static u64 inv(u64 a) { return powm(a, P - 2); }

static Word left_mul_letter(int j, const Word& w) {
  Word out; out.reserve(w.size() + 1); size_t k = 0, n = w.size();
  while (k < n && w[k] < j) { out.push_back(w[k]); j++; k++; }
  out.push_back((uint8_t)j); for (; k < n; k++) out.push_back(w[k]); return out;
}
static Word mul(const Word& a, const Word& b) { Word r = b; for (int i = (int)a.size() - 1; i >= 0; i--) r = left_mul_letter(a[i], r); return r; }

typedef vector<pair<uint32_t, u64>> SVec;  // sorted by row index

int main(int argc, char** argv) {
  if (argc < 5) { fprintf(stderr, "usage: D L monomials seed\n"); return 1; }
  int D = atoi(argv[1]), L = atoi(argv[2]); unsigned seed = atoi(argv[4]);
  vector<Word> S; { string spec = argv[3]; stringstream ss(spec); string mono;
    while (getline(ss, mono, ';')) { Word w; stringstream ms(mono); string lt; while (getline(ms, lt, ',')) w.push_back((uint8_t)stoi(lt)); S.push_back(w); } }
  vector<Word> U; Word cur(D, 0);
  function<void(int, int)> rec = [&](int pos, int lo) { if (pos == D) { U.push_back(cur); return; } for (int v = lo; v <= L; v++) { cur[pos] = (uint8_t)v; rec(pos + 1, v); } };
  rec(0, 0);
  map<Word, uint32_t> tidx;  // ordered: row order = lexicographic order of image words
  vector<vector<uint32_t>> img(U.size(), vector<uint32_t>(S.size()));
  { vector<Word> imgs; for (size_t y = 0; y < U.size(); y++) for (size_t s = 0; s < S.size(); s++) tidx.emplace(mul(S[s], U[y]), 0);
    uint32_t id = 0; for (auto& kv : tidx) kv.second = id++;
    for (size_t y = 0; y < U.size(); y++) for (size_t s = 0; s < S.size(); s++) img[y][s] = tidx[mul(S[s], U[y])]; }
  mt19937_64 rng(seed); vector<u64> A(S.size()), B(S.size());
  for (auto& x : A) x = 1 + rng() % (P - 1); for (auto& x : B) x = 1 + rng() % (P - 1);
  unordered_map<uint32_t, SVec> piv; piv.reserve(2 * U.size());
  long long rank = 0; size_t maxfill = 0;
  auto insert_col = [&](SVec v) {
    // reduce v against pivots keyed by leading row index
    while (!v.empty()) {
      auto it = piv.find(v[0].first);
      if (it == piv.end()) { u64 c = inv(v[0].second); for (auto& e : v) e.second = mulm(e.second, c); maxfill = max(maxfill, v.size()); piv.emplace(v[0].first, move(v)); rank++; return; }
      const SVec& p = it->second; u64 c = v[0].second;  // v <- v - c * p (p normalized)
      SVec r; r.reserve(v.size() + p.size());
      size_t i = 0, j = 0;
      while (i < v.size() || j < p.size()) {
        if (j == p.size() || (i < v.size() && v[i].first < p[j].first)) { r.push_back(v[i++]); }
        else if (i == v.size() || p[j].first < v[i].first) { r.push_back({p[j].first, (P - mulm(c, p[j].second)) % P}); j++; }
        else { u64 x = (v[i].second + P - mulm(c, p[j].second)) % P; if (x) r.push_back({v[i].first, x}); i++; j++; }
      }
      v.swap(r);
    }
  };
  auto t0 = chrono::steady_clock::now();
  for (size_t y = 0; y < U.size(); y++) {
    for (int side = 0; side < 2; side++) {
      SVec v; for (size_t s = 0; s < S.size(); s++) v.push_back({img[y][s], side == 0 ? A[s] : (P - B[s]) % P});
      sort(v.begin(), v.end()); insert_col(move(v));
    }
  }
  double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
  printf("{\"D\":%d,\"L\":%d,\"nS\":%zu,\"U\":%zu,\"rows\":%zu,\"rank\":%lld,\"kernel\":%lld,\"seed\":%u,\"maxfill\":%zu,\"seconds\":%.1f}\n",
         D, L, S.size(), U.size(), tidx.size(), rank, 2LL * (long long)U.size() - rank, seed, maxfill, secs);
  return 0;
}
