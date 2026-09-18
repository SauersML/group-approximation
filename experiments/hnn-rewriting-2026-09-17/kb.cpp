// Knuth-Bendix completion for group presentations, wreath or shortlex ordering.
// A finite complete (confluent, terminating) rewriting system for a group
// certifies type FP_infinity (Anick, Squier, Kobayashi).
// Input on stdin:
//   line 1: letters in rank order smallest..largest (inverse of x is swapcase(x))
//   line 2: ordering: wreath | shortlex
//   line 3: max_rules max_len
//   further lines: relators (words over letters)
// Output: status and, if complete, the rules (independently re-verified).
#include <bits/stdc++.h>
using namespace std;

static int rnk[256];
static bool wreath = true;

static int cmpShortlex(const string &u, const string &v) {
  if (u.size() != v.size()) return u.size() < v.size() ? -1 : 1;
  for (size_t i = 0; i < u.size(); i++)
    if (u[i] != v[i]) return rnk[(unsigned char)u[i]] < rnk[(unsigned char)v[i]] ? -1 : 1;
  return 0;
}

static int cmpWreath(const string &u, const string &v) {
  if (u == v) return 0;
  int m = -1;
  for (unsigned char c : u) m = max(m, rnk[c]);
  for (unsigned char c : v) m = max(m, rnk[c]);
  if (m < 0) return 0;
  int cu = 0, cv = 0;
  for (unsigned char c : u) cu += rnk[c] == m;
  for (unsigned char c : v) cv += rnk[c] == m;
  if (cu != cv) return cu < cv ? -1 : 1;
  // split into pieces separated by the top letter
  size_t pu = 0, pv = 0;
  while (true) {
    size_t qu = pu, qv = pv;
    while (qu < u.size() && rnk[(unsigned char)u[qu]] != m) qu++;
    while (qv < v.size() && rnk[(unsigned char)v[qv]] != m) qv++;
    int c = cmpWreath(u.substr(pu, qu - pu), v.substr(pv, qv - pv));
    if (c) return c;
    if (qu >= u.size()) return 0;
    pu = qu + 1;
    pv = qv + 1;
  }
}

static int cmpw(const string &u, const string &v) { return wreath ? cmpWreath(u, v) : cmpShortlex(u, v); }

struct RWS {
  vector<string> L, R;
  vector<char> act;
  unordered_map<string, int> idx;  // active lhs -> id
  vector<int> lens;                // sorted distinct active lhs lengths (approx; superset)
  set<int> lenset;

  string reduce(const string &w) {
    string out;
    string st(w.rbegin(), w.rend());
    while (!st.empty()) {
      out.push_back(st.back());
      st.pop_back();
      int n = out.size();
      for (int Ln : lens) {
        if (Ln > n) break;
        auto it = idx.find(out.substr(n - Ln));
        if (it != idx.end()) {
          const string &r = R[it->second];
          out.resize(n - Ln);
          st.append(r.rbegin(), r.rend());
          break;
        }
      }
    }
    return out;
  }
  void relens() { lens.assign(lenset.begin(), lenset.end()); }
};

int main() {
  string order, ord;
  long maxRules; size_t maxLen;
  getline(cin, order);
  getline(cin, ord);
  wreath = (ord == "wreath");
  { string l; getline(cin, l); stringstream ss(l); ss >> maxRules >> maxLen; }
  for (size_t i = 0; i < order.size(); i++) rnk[(unsigned char)order[i]] = i;
  vector<pair<string, string>> eq;
  for (char c : order) {
    char d = islower(c) ? toupper(c) : tolower(c);
    eq.push_back({string{c, d}, ""});
  }
  string rel;
  while (getline(cin, rel)) if (!rel.empty()) eq.push_back({rel, ""});

  RWS S;
  // pending equations, processed shortest first
  auto keyf = [](const pair<string, string> &e) { return e.first.size() + e.second.size(); };
  vector<vector<pair<string, string>>> buckets(4 * maxLen + 8);
  auto push = [&](string a, string b) {
    size_t k = a.size() + b.size();
    if (k >= buckets.size()) k = buckets.size() - 1;
    buckets[k].push_back({move(a), move(b)});
  };
  for (auto &e : eq) push(e.first, e.second);
  long deferred = 0;
  vector<pair<string, string>> deferredEq;
  size_t cur = 0;
  // critical pair pointer: rules are processed in order; pairs (i, j) with j<=i are generated when i is added
  deque<int> newRules;
  auto overlaps = [&](int i, int j) {
    const string &l1 = S.L[i], &l2 = S.L[j];
    for (size_t k = 1; k < min(l1.size(), l2.size()); k++)
      if (l1.compare(l1.size() - k, k, l2, 0, k) == 0)
        push(S.R[i] + l2.substr(k), l1.substr(0, l1.size() - k) + S.R[j]);
  };
  long active = 0;
  while (true) {
    while (cur < buckets.size() && buckets[cur].empty()) cur++;
    if (cur >= buckets.size()) {
      if (newRules.empty()) break;
      int i = newRules.front(); newRules.pop_front();
      if (!S.act[i]) continue;
      for (int j = 0; j <= i; j++) if (S.act[j]) { overlaps(i, j); if (j != i) overlaps(j, i); }
      cur = 0;
      continue;
    }
    auto e = move(buckets[cur].back()); buckets[cur].pop_back();
    string u = S.reduce(e.first), v = S.reduce(e.second);
    int c = cmpw(u, v);
    if (c == 0) continue;
    if (c < 0) swap(u, v);
    if (u.size() > maxLen || v.size() > maxLen) { deferredEq.push_back({u, v}); continue; }
    int id = S.L.size();
    S.L.push_back(u); S.R.push_back(v); S.act.push_back(1);
    // interreduce
    for (int j = 0; j < id; j++) {
      if (!S.act[j]) continue;
      if (S.L[j].find(u) != string::npos) {
        S.act[j] = 0; S.idx.erase(S.L[j]); active--;
        push(S.L[j], S.R[j]);
      }
    }
    S.idx[u] = id; active++;
    S.lenset.clear();
    for (auto &kv : S.idx) S.lenset.insert(kv.first.size());
    S.relens();
    for (int j = 0; j < id; j++) if (S.act[j]) { string r = S.reduce(S.R[j]); if (r != S.R[j]) S.R[j] = r; }
    newRules.push_back(id);
    if (S.L.size() % 500 == 0) fprintf(stderr, "total=%zu active=%ld lhs=%zu deferred=%zu\n", S.L.size(), active, u.size(), deferredEq.size());
    if (active > maxRules) { printf("OVERFLOW active=%ld total=%zu\n", active, S.L.size()); for (size_t q=0;q<S.L.size();q++) if (S.act[q]) printf("  %s -> %s\n", S.L[q].c_str(), S.R[q].empty()?"1":S.R[q].c_str()); return 0; }
  }
  long pend = 0;
  for (auto &e : deferredEq) if (S.reduce(e.first) != S.reduce(e.second)) pend++;
  // independent verification of local confluence
  vector<int> ids;
  for (size_t i = 0; i < S.L.size(); i++) if (S.act[i]) ids.push_back(i);
  bool ok = true;
  for (int i : ids) for (int j : ids) {
    const string &l1 = S.L[i], &l2 = S.L[j];
    if (i != j && l1.find(l2) != string::npos) {
      if (S.reduce(S.R[i]) != S.reduce(l1.substr(0, l1.find(l2)) + S.R[j] + l1.substr(l1.find(l2) + l2.size()))) ok = false;
    }
    for (size_t k = 1; k < min(l1.size(), l2.size()); k++)
      if (l1.compare(l1.size() - k, k, l2, 0, k) == 0)
        if (S.reduce(S.R[i] + l2.substr(k)) != S.reduce(l1.substr(0, l1.size() - k) + S.R[j])) ok = false;
  }
  printf("%s active=%zu deferred_unresolved=%ld verified_local_confluence=%d\n",
         (pend == 0 && ok) ? "COMPLETE" : "INCOMPLETE", ids.size(), pend, (int)ok);
  if (pend == 0 && ok)
    for (int i : ids) printf("  %s -> %s\n", S.L[i].c_str(), S.R[i].empty() ? "1" : S.R[i].c_str());
  return 0;
}
