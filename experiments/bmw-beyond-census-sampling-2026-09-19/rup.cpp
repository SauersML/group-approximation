// rup CNF LEMMAS : checks that every clause of LEMMAS (one DIMACS clause per line, "d ..." deletion lines
// are ignored, which is sound) is a reverse-unit-propagation (RUP) consequence of CNF plus the earlier
// lemmas, and that the empty clause is derived. Then trims backward to the lemmas actually used
// (conflict-analysis marking) and writes them to LEMMAS.core. Each RUP lemma is a cone lemma: a clause
// over the atoms "g in P" implied by the positive-cone axioms, so a derived empty clause proves that
// no positive cone of the parity kernel restricts to the ball. Prints "RUP-OK lemmas N core C" or FAIL.
#include <bits/stdc++.h>
using namespace std;
int nv; vector<vector<int>> cl; vector<vector<int>> W;  // watches indexed by literal code
vector<signed char> val; vector<int> reason, trail_, lvl;
static inline int code(int l) { return l > 0 ? 2 * l : -2 * l + 1; }
static inline int vl(int l) { int x = val[abs(l)]; return l > 0 ? x : -x; }
static void assign(int l, int r) { val[abs(l)] = l > 0 ? 1 : -1; reason[abs(l)] = r; trail_.push_back(l); }
size_t qhead = 0;
static int propagate() {   // returns conflicting clause or -1
    while (qhead < trail_.size()) {
        int l = -trail_[qhead++]; auto& ws = W[code(l)];   // clauses watching literal l, now false
        for (size_t i = 0; i < ws.size();) {
            int c = ws[i]; auto& C = cl[c];
            if (C[0] == l) swap(C[0], C[1]);
            if (vl(C[0]) == 1) { ++i; continue; }
            bool moved = false;
            for (size_t k = 2; k < C.size(); ++k) if (vl(C[k]) != -1) {
                swap(C[1], C[k]); W[code(C[1])].push_back(c); ws[i] = ws.back(); ws.pop_back(); moved = true; break; }
            if (moved) continue;
            if (vl(C[0]) == -1) return c;
            if (vl(C[0]) == 0) assign(C[0], c);
            ++i;
        }
    }
    return -1;
}
static int addc(vector<int> C) {   // add clause at top level; returns index, handles units
    int id = cl.size(); cl.push_back(C);
    if (C.size() >= 2) { W[code(C[0])].push_back(id); W[code(C[1])].push_back(id); }
    return id;
}
vector<int> units;  // unit clause ids (re-asserted on each check)
static void backtrack(size_t to) { while (trail_.size() > to) { val[abs(trail_.back())] = 0; reason[abs(trail_.back())] = -1; trail_.pop_back(); } qhead = min(qhead, to); }
vector<vector<int>> ante;   // for lemmas: clauses used in the conflict (for trimming)
static void collect(int confl, vector<int>& used) {   // all reasons in the implication graph of the conflict
    vector<char> seen(nv + 1, 0); vector<int> st{confl}; used.push_back(confl);
    while (!st.empty()) { int c = st.back(); st.pop_back();
        for (int l : cl[c]) { int v = abs(l); if (seen[v]) continue; seen[v] = 1;
            int r = reason[v]; if (r >= 0) { used.push_back(r); st.push_back(r); } } }
}
int main(int argc, char** argv) {
    FILE* f = fopen(argv[1], "r"); char buf[1 << 16]; int ncl0 = 0;
    vector<vector<int>> in;
    while (fgets(buf, sizeof buf, f)) { if (buf[0] == 'c') continue; if (buf[0] == 'p') { sscanf(buf, "p cnf %d %d", &nv, &ncl0); continue; }
        vector<int> C; char* p = buf; int x, k; while (sscanf(p, "%d%n", &x, &k) == 1) { p += k; if (!x) break; C.push_back(x); } if (!C.empty()) in.push_back(C); }
    fclose(f);
    W.assign(2 * nv + 2, {}); val.assign(nv + 1, 0); reason.assign(nv + 1, -1);
    int nin = in.size();
    for (auto& C : in) { sort(C.begin(), C.end()); C.erase(unique(C.begin(), C.end()), C.end()); int id = addc(C); if (C.size() == 1) units.push_back(id); if (C.empty()) { puts("FAIL empty input clause"); return 1; } }
    f = fopen(argv[2], "r"); vector<vector<int>> lem;
    while (fgets(buf, sizeof buf, f)) { if (buf[0] == 'd' || buf[0] == 'c') continue;
        vector<int> C; char* p = buf; int x, k; bool end = false; while (sscanf(p, "%d%n", &x, &k) == 1) { p += k; if (!x) { end = true; break; } C.push_back(x); }
        if (end) lem.push_back(C); }
    fclose(f);
    // level-0 trail kept persistently; z = its length. A level-0 conflict ends the proof.
    size_t z = 0; long nl = 0; int final_cf = -1;
    for (int u : units) { int l = cl[u][0]; if (vl(l) == -1) { final_cf = u; break; } if (vl(l) == 0) assign(l, u); }
    if (final_cf < 0) final_cf = propagate();
    z = trail_.size();
    vector<char> lneed; ante.clear();
    size_t i = 0;
    for (; final_cf < 0 && i < lem.size(); ++i) {
        auto& C = lem[i]; ++nl; ante.push_back({});
        int cf = -1; bool done = false;
        for (int l : C) if (vl(l) == 1) { vector<int> tmp{reason[abs(l)]}; /* implied at level 0 */
            vector<char> sn(nv + 1, 0); vector<int> st{tmp[0]}; ante.back().push_back(tmp[0]);
            while (!st.empty()) { int c = st.back(); st.pop_back(); for (int q : cl[c]) { int v = abs(q); if (sn[v]) continue; sn[v] = 1; int rr = reason[v]; if (rr >= 0) { ante.back().push_back(rr); st.push_back(rr); } } }
            done = true; break; }
        if (!done) { for (int l : C) if (vl(l) == 0) assign(-l, -1);
            cf = propagate(); if (cf < 0) { printf("FAIL lemma %zu not RUP\n", i); return 1; }
            collect(cf, ante.back()); }
        backtrack(z);
        if (C.empty()) { final_cf = -2; ++i; break; }
        stable_partition(C.begin(), C.end(), [&](int l) { return vl(l) != -1; });   // keep watches non-false
        int id = addc(C);
        if (C.size() == 1 || [&]{ int u = 0; for (int l : C) if (vl(l) != -1) ++u; return u <= 1; }()) {
            // unit (possibly after level-0 falsification): extend level 0 using this clause as reason
            int free = 0, fl = 0; for (int l : C) if (vl(l) != -1) { ++free; fl = l; }
            if (free == 0) { final_cf = id; ++i; ante.push_back({}); collect(id, ante.back()); break; }
            if (vl(fl) == 0) { assign(fl, id); int c2 = propagate(); z = trail_.size();
                if (c2 >= 0) { final_cf = c2; ++i; ante.push_back({}); collect(c2, ante.back()); break; } }
        }
    }
    if (final_cf == -1) { puts("FAIL no empty clause derived"); return 1; }
    if (final_cf >= 0 && ante.size() == i) { ante.push_back({}); collect(final_cf, ante.back()); }  // conflict among input units
    // backward trimming. ante has one entry per checked lemma plus one final entry (the empty clause)
    size_t L = ante.size(); if (L > i) { lem.resize(i); lem.push_back({}); } else lem.resize(i);
    lneed.assign(L, 0); lneed[L - 1] = 1; long ninput = 0; vector<char> need(nin, 0);
    for (long j = (long)L - 1; j >= 0; --j) if (lneed[j]) for (int c : ante[j]) { if (c >= nin) lneed[c - nin] = 1; else if (!need[c]) { need[c] = 1; ++ninput; } }
    string out = string(argv[2]) + ".core"; FILE* g = fopen(out.c_str(), "w"); long ncore = 0;
    for (size_t i = 0; i < L; ++i) if (lneed[i]) { ++ncore; for (int l : lem[i]) fprintf(g, "%d ", l); fprintf(g, "0\n"); }
    fclose(g);
    string oi = string(argv[2]) + ".inputs"; FILE* h = fopen(oi.c_str(), "w");   // 0-based indices of used input clauses
    for (long c = 0; c < nin; ++c) if (need[c]) fprintf(h, "%ld\n", c);
    fclose(h);
    printf("RUP-OK lemmas %ld core %ld input-clauses-used %ld\n", nl, ncore, ninput);
    return 0;
}
