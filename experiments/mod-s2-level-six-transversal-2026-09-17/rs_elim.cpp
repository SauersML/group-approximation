// Abelianised Reidemeister-Schreier + exact unit elimination over Z.
// Input (text, from level6_dump.py):
//   k                      number of cosets
//   k lines: act[c][0..9]  (right action of the 10 Artin generators)
//   nrel, then per relation: len_l (g e)*  len_r (g e)*
//   ntw,  then per twist word: len (g e)*
// Output (text): ncols_alive, list of alive column ids; nrows then rows;
//   nv then v rows (one per coset c and twist word t, order c-major).
// Row format: len then (col val)* with original Schreier column ids.
// All arithmetic is int64 with overflow checks (abort on overflow).
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <queue>
#include <array>
#include <tuple>
using namespace std;
typedef long long ll;
typedef vector<pair<int, ll>> Row;

static int K;
static vector<array<int, 10>> act, inv_;
static unordered_map<ll, int> genid;   // key c*10+g -> column

static ll safe_add(ll a, ll b) {
  ll r;
  if (__builtin_add_overflow(a, b, &r)) { fprintf(stderr, "overflow\n"); exit(2); }
  return r;
}
static ll safe_mul(ll a, ll b) {
  ll r;
  if (__builtin_mul_overflow(a, b, &r)) { fprintf(stderr, "overflow\n"); exit(2); }
  return r;
}

static int trace(int c, const vector<pair<int, int>>& w, unordered_map<int, ll>& vec, int sign) {
  for (auto& ge : w) {
    int g = ge.first, e = ge.second;
    if (e > 0) {
      auto it = genid.find((ll)c * 10 + g);
      if (it != genid.end()) vec[it->second] += sign;
      c = act[c][g];
    } else {
      c = inv_[c][g];
      auto it = genid.find((ll)c * 10 + g);
      if (it != genid.end()) vec[it->second] -= sign;
    }
  }
  return c;
}

static Row tosorted(unordered_map<int, ll>& m) {
  Row r;
  for (auto& p : m) if (p.second) r.push_back(p);
  sort(r.begin(), r.end());
  return r;
}

static vector<pair<int, int>> readword() {
  int n; if (scanf("%d", &n) != 1) exit(3);
  vector<pair<int, int>> w(n);
  for (int i = 0; i < n; i++) if (scanf("%d %d", &w[i].first, &w[i].second) != 2) exit(3);
  return w;
}

// r := r - f * p  (both sorted)
static Row axpy(const Row& r, ll f, const Row& p) {
  Row out; out.reserve(r.size() + p.size());
  size_t i = 0, j = 0;
  while (i < r.size() || j < p.size()) {
    if (j == p.size() || (i < r.size() && r[i].first < p[j].first)) { out.push_back(r[i++]); }
    else if (i == r.size() || p[j].first < r[i].first) {
      out.push_back({p[j].first, -safe_mul(f, p[j].second)}); j++;
    } else {
      ll v = safe_add(r[i].second, -safe_mul(f, p[j].second));
      if (v) out.push_back({r[i].first, v});
      i++; j++;
    }
  }
  return out;
}

static ll coef(const Row& r, int col) {
  auto it = lower_bound(r.begin(), r.end(), make_pair(col, (ll)-9e18));
  if (it != r.end() && it->first == col) return it->second;
  return 0;
}

int main(int argc, char** argv) {
  // argv[1]: NSWITCH; when the alive column count drops to NSWITCH the sparse
  // Markowitz phase stops and the streaming dense phase finishes the job.
  int NSWITCH = argc > 1 ? atoi(argv[1]) : 0;
  // argv[2] (optional): modular mode.  At the switch point write, for each
  // prime p, the image of every twist vector in Z^n / (L + pZ^n) to this
  // file and stop (no second phase, no stdout output).
  FILE* modp = argc > 2 ? fopen(argv[2], "w") : nullptr;
  if (scanf("%d", &K) != 1) return 3;
  act.resize(K); inv_.resize(K);
  for (int c = 0; c < K; c++) for (int g = 0; g < 10; g++) if (scanf("%d", &act[c][g]) != 1) return 3;
  for (int c = 0; c < K; c++) for (int g = 0; g < 10; g++) inv_[act[c][g]][g] = c;
  // Schreier tree by BFS in the same order as level8_purebraid.schreier
  vector<char> seen(K, 0); seen[0] = 1;
  vector<int> q{0};
  vector<vector<char>> tree(K, vector<char>(10, 0));
  for (size_t h = 0; h < q.size(); h++) {
    int c = q[h];
    for (int g = 0; g < 10; g++) {
      int d = act[c][g];
      if (!seen[d]) { seen[d] = 1; tree[c][g] = 1; q.push_back(d); }
    }
  }
  if ((int)q.size() != K) { fprintf(stderr, "not transitive\n"); return 4; }
  int ng = 0;
  for (int c = 0; c < K; c++) for (int g = 0; g < 10; g++) if (!tree[c][g]) genid[(ll)c * 10 + g] = ng++;
  int nrel; if (scanf("%d", &nrel) != 1) return 3;
  vector<Row> rows;
  for (int r = 0; r < nrel; r++) {
    auto L = readword(); auto R = readword();
    for (int c = 0; c < K; c++) {
      unordered_map<int, ll> m;
      int e1 = trace(c, L, m, 1), e2 = trace(c, R, m, -1);
      if (e1 != e2) { fprintf(stderr, "relation fails\n"); return 5; }
      Row x = tosorted(m);
      if (!x.empty()) rows.push_back(x);
    }
  }
  int ntw; if (scanf("%d", &ntw) != 1) return 3;
  vector<vector<pair<int, int>>> tw(ntw);
  for (int t = 0; t < ntw; t++) tw[t] = readword();
  // optional selection of (coset, twist) pairs; -1 means all, c-major
  int nsel; if (scanf("%d", &nsel) != 1) nsel = -1;
  vector<pair<int, int>> sel;
  if (nsel < 0) { for (int c = 0; c < K; c++) for (int t = 0; t < ntw; t++) sel.push_back({c, t}); }
  else { sel.resize(nsel); for (auto& p : sel) if (scanf("%d %d", &p.first, &p.second) != 2) return 3; }
  vector<Row> V;
  for (auto& p : sel) {
    int c = p.first, t = p.second;
    unordered_map<int, ll> m;
    if (trace(c, tw[t], m, 1) != c) { fprintf(stderr, "twist moves coset\n"); return 6; }
    V.push_back(tosorted(m));
  }
  fprintf(stderr, "cosets %d gens %d relators %zu v %zu\n", K, ng, rows.size(), V.size());
  // column occurrence lists (may hold stale ids; checked on use)
  vector<vector<int>> colr(ng), colv(ng);
  for (size_t r = 0; r < rows.size(); r++) for (auto& p : rows[r]) colr[p.first].push_back(r);
  for (size_t t = 0; t < V.size(); t++) for (auto& p : V[t]) colv[p.first].push_back(t);
  vector<char> alive(ng, 1), rowdead(rows.size(), 0);
  vector<Row> disc; vector<tuple<int, ll, Row>> pivlog;
  // Markowitz passes: pivot on a unit entry (r, j) only if
  // (len(r) - 1) * (count(j) - 1) <= T; T grows when a pass stalls.
  bool progress = true; int round = 0; long elim = 0;
  long long T = 0; const long long TMAX = 1LL << 40;
  for (int phase = 0; phase < 2; phase++) {
  T = 0;
  while (true) {
    round++;
    // drop duplicate rows up to sign (exact: a duplicate relator is redundant)
    {
      unordered_map<size_t, vector<int>> h;
      size_t dropped = 0;
      for (size_t r = 0; r < rows.size(); r++) {
        if (rowdead[r]) continue;
        if (rows[r].empty()) { rowdead[r] = 1; continue; }
        if (rows[r][0].second < 0) for (auto& p : rows[r]) p.second = -p.second;
        size_t hv = rows[r].size();
        for (auto& p : rows[r]) hv = hv * 1000003u ^ ((size_t)p.first * 31u + (size_t)p.second);
        auto& b = h[hv];
        bool dup = false;
        for (int o : b) if (rows[o] == rows[r]) { dup = true; break; }
        if (dup) { rowdead[r] = 1; rows[r].clear(); rows[r].shrink_to_fit(); dropped++; }
        else b.push_back(r);
      }
      if (dropped) fprintf(stderr, "round %d: dropped %zu duplicate rows\n", round, dropped);
    }
    // rebuild exact column counts (drop stale ids)
    for (int g = 0; g < ng; g++) colr[g].clear();
    for (size_t r = 0; r < rows.size(); r++) if (!rowdead[r]) for (auto& p : rows[r]) colr[p.first].push_back(r);
    progress = false;
    vector<pair<size_t, int>> order;
    for (size_t r = 0; r < rows.size(); r++) if (!rowdead[r]) order.push_back({rows[r].size(), (int)r});
    sort(order.begin(), order.end());
    bool anyunit = false;
    for (auto& o : order) {
      int r = o.second;
      if (rowdead[r]) continue;
      Row& v = rows[r];
      if (v.empty()) { rowdead[r] = 1; continue; }
      int j = -1; long long best = -1;
      for (auto& p : v) if (p.second == 1 || p.second == -1) {
        anyunit = true;
        long long cst = (long long)(v.size() - 1) * (long long)(colr[p.first].size() - 1);
        if (best < 0 || cst < best) { best = cst; j = p.first; }
      }
      if (j < 0 || best > T) continue;
      Row piv = v; ll s = coef(piv, j);
      if (phase == 1) pivlog.emplace_back(j, s, piv);
      rowdead[r] = 1; rows[r].clear(); rows[r].shrink_to_fit();
      vector<int> cr; cr.swap(colr[j]);
      for (int q2 : cr) {
        if (rowdead[q2]) continue;
        ll a = coef(rows[q2], j);
        if (!a) continue;
        Row nr = axpy(rows[q2], safe_mul(a, s), piv);
        for (auto& p : nr) if (coef(rows[q2], p.first) == 0) colr[p.first].push_back(q2);
        rows[q2].swap(nr);
      }
      vector<int> cv; cv.swap(colv[j]);
      for (int t : cv) {
        ll a = coef(V[t], j);
        if (!a) continue;
        Row nr = axpy(V[t], safe_mul(a, s), piv);
        for (auto& p : nr) if (coef(V[t], p.first) == 0) colv[p.first].push_back(t);
        V[t].swap(nr);
      }
      alive[j] = 0; elim++;
      progress = true;
    }
    size_t live = 0, nnz = 0, vnnz = 0;
    for (size_t r = 0; r < rows.size(); r++) if (!rowdead[r] && !rows[r].empty()) { live++; nnz += rows[r].size(); }
    for (auto& v : V) vnnz += v.size();
    int ac = 0; for (int g = 0; g < ng; g++) ac += alive[g];
    fprintf(stderr, "round %d T=%lld: eliminated %ld, alive cols %d, live rows %zu, nnz %zu, v nnz %zu\n",
            round, T, elim, ac, live, nnz, vnnz);
    if (!anyunit) break;
    if (phase == 0 && ac <= NSWITCH) break;
    if (!progress) { if (T >= TMAX) break; T = (T == 0) ? 1 : 2 * T; }
  }
  if (phase == 0 && NSWITCH > 0) {
    // Selection phase over the n alive columns.  For each prime p in PR, a
    // greedy RREF modulo p picks a maximal set of rows independent mod p; the
    // union of these rows (plus every EXTRA-th remaining row) is the output
    // sublattice L0 of the relator lattice L.  L0 and L have the same rank over
    // Q (the rank mod the large prime is a lower bound for the rational rank of
    // L0, and never exceeds that of L).  Downstream: if Z^n/L0 is torsion free
    // then L0 = L, because L/L0 is a finite subgroup of Z^n/L0.
    vector<int> acol; vector<int> cidx(ng, -1);
    for (int g = 0; g < ng; g++) if (alive[g]) { cidx[g] = acol.size(); acol.push_back(g); }
    int n = acol.size();
    vector<unsigned long long> PR = {2147483647ULL, 2ULL, 3ULL, 5ULL};
    if (modp) PR = {2147483647ULL, 2ULL, 3ULL, 5ULL, 7ULL, 11ULL, 13ULL, 2147483629ULL};
    const int EXTRA = 1009;
    vector<char> selected(rows.size(), 0);
    typedef unsigned long long ull;
    auto pw = [](ull a, ull e, ull m) { ull r = 1; a %= m; while (e) { if (e & 1) r = r * a % m; a = a * a % m; e >>= 1; } return r; };
    for (ull P_ : PR) {
      vector<int> pivrow(n, -1); vector<vector<ull>> basis; vector<int> nonpiv(n);
      for (int i = 0; i < n; i++) nonpiv[i] = i;
      vector<ull> x(n);
      size_t nsel = 0;
      for (size_t r = 0; r < rows.size(); r++) {
        if (rowdead[r] || rows[r].empty()) continue;
        if ((int)basis.size() == n) break;
        for (int k : nonpiv) x[k] = 0;
        for (auto& p : rows[r]) { ll v = p.second % (ll)P_; if (v < 0) v += P_; x[cidx[p.first]] = v; }
        for (auto& p : rows[r]) {
          int j = cidx[p.first];
          if (pivrow[j] < 0 || !x[j]) continue;
          ull a = x[j]; const vector<ull>& b = basis[pivrow[j]];
          for (int k : nonpiv) if (b[k]) x[k] = (x[k] + (P_ - a) * b[k]) % P_;
        }
        int j = -1;
        for (int k : nonpiv) if (x[k]) { j = k; break; }
        if (j < 0) continue;
        vector<ull> y(n, 0);
        ull inv = pw(x[j], P_ - 2, P_);
        for (int k : nonpiv) if (x[k]) y[k] = x[k] * inv % P_;
        for (auto& b : basis) {
          ull a = b[j];
          if (!a) continue;
          for (int k : nonpiv) if (y[k]) b[k] = (b[k] + (P_ - a) * y[k]) % P_;
        }
        pivrow[j] = basis.size(); basis.push_back(y);
        nonpiv.erase(find(nonpiv.begin(), nonpiv.end(), j));
        if (!selected[r]) { selected[r] = 1; nsel++; }
      }
      fprintf(stderr, "select mod %llu: rank %zu of %d cols, new rows %zu\n", P_, basis.size(), n, nsel);
      if (modp) {
        // basis is the RREF of (all live rows) mod p, i.e. of L + pZ^n.  The
        // reduction of v modulo it, read on the non-pivot columns, is the
        // image of v in (Z^n / (L + pZ^n)) = F_p^(n - rank).
        fprintf(modp, "%llu %zu %zu\n", P_, basis.size(), nonpiv.size());
        for (int k : nonpiv) fprintf(modp, "%d ", acol[k]);
        fprintf(modp, "\n");
        for (auto& v : V) {
          for (int k = 0; k < n; k++) x[k] = 0;
          for (auto& p : v) { ll a = p.second % (ll)P_; if (a < 0) a += P_; x[cidx[p.first]] = a; }
          for (int j = 0; j < n; j++) {
            if (pivrow[j] < 0 || !x[j]) continue;
            ull a = x[j]; const vector<ull>& b = basis[pivrow[j]];
            for (int k : nonpiv) if (b[k]) x[k] = (x[k] + (P_ - a) * b[k]) % P_;
            x[j] = 0;
          }
          for (int k : nonpiv) fprintf(modp, "%llu ", x[k]);
          fprintf(modp, "\n");
        }
        fflush(modp);
      }
    }
    if (modp) {
      fclose(modp);
      if (argc > 3) {
        // argv[3]: also write the switch-point lattice L0 (rows selected mod
        // p plus every EXTRA-th row) and the twist vectors, in the stdout format.
        FILE* f = fopen(argv[3], "w");
        const int EXTRA = 1009;
        fprintf(f, "%d\n", n);
        for (int g : acol) fprintf(f, "%d ", g);
        fprintf(f, "\n");
        vector<int> keep; size_t idx = 0;
        for (size_t r = 0; r < rows.size(); r++) {
          if (rowdead[r] || rows[r].empty()) continue;
          if (selected[r] || (idx++ % EXTRA) == 0) keep.push_back(r);
        }
        fprintf(f, "%zu\n", keep.size());
        for (int r : keep) {
          fprintf(f, "%zu", rows[r].size());
          for (auto& p : rows[r]) fprintf(f, " %d %lld", p.first, p.second);
          fprintf(f, "\n");
        }
        fprintf(f, "%zu\n", V.size());
        for (auto& v : V) {
          fprintf(f, "%zu", v.size());
          for (auto& p : v) fprintf(f, " %d %lld", p.first, p.second);
          fprintf(f, "\n");
        }
        fclose(f);
      }
      return 0;
    }
    size_t kept = 0, idx = 0;
    for (size_t r = 0; r < rows.size(); r++) {
      if (rowdead[r] || rows[r].empty()) continue;
      if (!selected[r] && (idx++ % EXTRA) != 0) { rowdead[r] = 1; disc.emplace_back(); disc.back().swap(rows[r]); }
      else kept++;
    }
    fprintf(stderr, "selection kept %zu rows\n", kept);
  }
  if (phase == 0 && NSWITCH > 0) continue;
  break;
  }
  vector<int> cols; for (int g = 0; g < ng; g++) if (alive[g]) cols.push_back(g);
  printf("%zu\n", cols.size());
  for (int g : cols) printf("%d ", g);
  printf("\n");
  size_t live = 0; for (size_t r = 0; r < rows.size(); r++) if (!rowdead[r] && !rows[r].empty()) live++;
  printf("%zu\n", live);
  for (size_t r = 0; r < rows.size(); r++) if (!rowdead[r] && !rows[r].empty()) {
    printf("%zu", rows[r].size());
    for (auto& p : rows[r]) printf(" %d %lld", p.first, p.second);
    printf("\n");
  }
  printf("%zu\n", V.size());
  for (auto& v : V) {
    printf("%zu", v.size());
    for (auto& p : v) printf(" %d %lld", p.first, p.second);
    printf("\n");
  }
  // Verification section: every row discarded by the selection, pushed
  // through the phase-2 pivot log; the nonzero results (deduplicated up to
  // sign) must lie in the span of the live rows (checked downstream).
  {
    vector<Row> outd;
    unordered_map<size_t, vector<int>> h;
    for (auto& x0 : disc) {
      Row x; x.swap(x0);
      for (auto& pl : pivlog) {
        ll a = coef(x, get<0>(pl));
        if (a) x = axpy(x, safe_mul(a, get<1>(pl)), get<2>(pl));
      }
      if (x.empty()) continue;
      if (x[0].second < 0) for (auto& p : x) p.second = -p.second;
      size_t hv = x.size();
      for (auto& p : x) hv = hv * 1000003u ^ ((size_t)p.first * 31u + (size_t)p.second);
      auto& b = h[hv];
      bool dup = false;
      for (int o : b) if (outd[o] == x) { dup = true; break; }
      if (!dup) { b.push_back(outd.size()); outd.push_back(x); }
    }
    fprintf(stderr, "verification rows: discarded %zu, distinct nonzero residues %zu\n", disc.size(), outd.size());
    printf("%zu\n", outd.size());
    for (auto& v : outd) {
      printf("%zu", v.size());
      for (auto& p : v) printf(" %d %lld", p.first, p.second);
      printf("\n");
    }
  }
  return 0;
}
