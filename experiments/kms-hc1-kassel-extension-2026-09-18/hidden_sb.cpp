// hidden_sb.cpp -- standard basis of the relator ideal of Gamma^A2_p in F_p<Y_a,Y_b,Y_c>/F_{D+1}.
//
// Coordinates (default, eigen-coordinates): a = E(Y_a) = sum_{k<p} Y_a^k/k!, a^-1 = E(-Y_a); then
// a^p - 1 = Y_a^p * unit, and the torus (F_p^*)^3 (a -> a^l, b -> b^m, c -> c^n, automorphisms of Gamma)
// acts by Y_i -> l_i Y_i, so I is spanned by its multidegree-mod-(p-1) eigencomponents.  The generators
// used are Y_i^p and the eigencomponents of the six commutator relators (words with a run Y_i^p dropped).
// XCOORD=1: Magnus coordinates a = 1+X_a (relators a^p, b^p, c^p and the six commutators, unsplit).
// Truncation at total degree D is sound: the order below puts the lowest degree first, so every
// S-polynomial and reduction is exact modulo F_{D+1}.
// Relators: a^p, b^p, c^p, [[x,y],x], [[x,y],y] for (x,y) in {(a,b),(b,c),(a,c)}, [x,y]=x^-1y^-1xy.
// Order (local degree order): a lower total degree is larger; ties are broken by lex with a<b<c.
// The leading word is the lex-largest word of lowest degree.  Standard basis = Buchberger over
// overlap ambiguities (Mora); elements are inserted in nondecreasing leading degree.
//
// usage: hidden_sb D Tab Tbc Tac Z5 prefix [testvecs|-] [refleads]      (compile -DPP=p, default 5)
//   testvecs: file "n" then n blocks "m" + m lines "word coef" (homogeneous elements); each is reduced
//             modulo the LOWEST FORMS of the basis (a Groebner basis of gr I), written to prefix.nf, and the
//             coefficients with which each hidden basis element was used are printed.
//   refleads: a prefix.leads file of another run; basis elements whose lead is normal for those leads
//             are called hidden: listed, and their full polynomials written to prefix.hidden.
//   Txy = keep terms of degree <= Txy of the relator components on edge xy
//         (3 = initial forms only = ideal J; D = the true group relators)
//   Z5  = 1: also add the three homogeneous elements (X Y - Y X)^p (edge commutator p-th powers)
//   env: LOWONLY=1 keep only the lowest-degree part of each eigencomponent; SKIP=names omit components;
//        LISTCOMP=1 list components; DUMP=i,j,.. write basis polynomials to prefix.dump; PROF=1 profile.
// output: prefix.hilb  (Hilbert function of A/I per multidegree), prefix.leads (basis leads with
//         provenance), stdout summary, including every "jump": an S-pair of degree s whose
//         reduction has leading degree > s (a syzygy of initial forms broken by the tails).
#include <cstring>
#include <bits/stdc++.h>
using namespace std;
typedef uint32_t u32; typedef uint8_t u8;
#ifndef PP
#define PP 5
#endif
static const int P = PP;  // the prime (compile with -DPP=3 etc.)
int D = 15;
u32 P3[20], OFF[20];
struct T { u32 v; u8 l; u8 c; };
typedef vector<T> Poly;
vector<u8> acc, flag;
vector<uint64_t> bm;
int INV[P];
inline u32 idx(int l, u32 v) { return OFF[l] + v; }
inline bool bmget(u32 i) { return (bm[i >> 6] >> (i & 63)) & 1; }
inline void bmset(u32 i) { bm[i >> 6] |= 1ULL << (i & 63); }

vector<Poly> G;
vector<pair<int, u32>> LEAD;
unordered_map<u32, int> LID;
bool hasLen[20];
struct Prov { int type, a, b, k, sdeg; };  // type 0 relator (a = id), 1 overlap, 2 deferred
vector<Prov> PROV;

string word(int l, u32 v) {
    string s(l, '?');
    for (int i = l - 1; i >= 0; i--) { s[i] = "abc"[v % 3]; v /= 3; }
    return s;
}
array<int, 3> mdeg(int l, u32 v) {
    array<int, 3> m{0, 0, 0};
    for (int i = 0; i < l; i++) { m[v % 3]++; v /= 3; }
    return m;
}

// Aho-Corasick automaton over the current lead words (rebuilt after every insertion)
vector<array<int,3>> ACG; vector<int> ACF, ACO;  // goto, fail, output lead id (-1 none)
vector<pair<int,u32>> ACL;                          // the lead list the automaton was built from
void buildAC(const vector<pair<int,u32>> &leads) {
    ACL = leads; ACG.assign(1, {-1, -1, -1}); ACF.assign(1, 0); ACO.assign(1, -1);
    for (size_t n = 0; n < leads.size(); n++) {
        int l = leads[n].first; u32 v = leads[n].second; int st = 0;
        for (int i = 0; i < l; i++) {
            int ch = (v / P3[l - 1 - i]) % 3;
            if (ACG[st][ch] < 0) { ACG[st][ch] = ACG.size(); ACG.push_back({-1, -1, -1}); ACF.push_back(0); ACO.push_back(-1); }
            st = ACG[st][ch];
        }
        ACO[st] = n;
    }
    deque<int> q;
    for (int ch = 0; ch < 3; ch++) { if (ACG[0][ch] < 0) ACG[0][ch] = 0; else { ACF[ACG[0][ch]] = 0; q.push_back(ACG[0][ch]); } }
    while (!q.empty()) {
        int st = q.front(); q.pop_front();
        if (ACO[st] < 0) ACO[st] = ACO[ACF[st]];
        for (int ch = 0; ch < 3; ch++) {
            int nx = ACG[st][ch];
            if (nx < 0) ACG[st][ch] = ACG[ACF[st]][ch];
            else { ACF[nx] = ACG[ACF[st]][ch]; q.push_back(nx); }
        }
    }
}
inline bool divisor(int L, u32 v, int &pos, int &gi) {
    int dg[20]; u32 x = v;
    for (int i = L - 1; i >= 0; i--) { dg[i] = x % 3; x /= 3; }
    int st = 0;
    for (int j = 0; j < L; j++) {
        st = ACG[st][dg[j]];
        if (ACO[st] >= 0) { gi = ACO[st]; pos = j - ACL[gi].first + 1; return true; }
    }
    return false;
}

priority_queue<u32> PQ[20];
inline void addterm(int l, u32 v, int c) {
    u32 id = idx(l, v);
    int nc = (acc[id] + c) % P; if (nc < 0) nc += P;
    acc[id] = nc;
    if (!flag[id]) { flag[id] = 1; PQ[l].push(v); }
}
long long redops = 0;
vector<int> USE; bool TRACE = false;
Poly reduce_(const vector<pair<pair<int,u32>,int>> &f) {
    for (auto &t : f) addterm(t.first.first, t.first.second, t.second);
    Poly out;
    for (int L = 0; L <= D; L++) {
        while (!PQ[L].empty()) {
            u32 v = PQ[L].top(); PQ[L].pop();
            u32 id = idx(L, v); flag[id] = 0;
            int c = acc[id]; if (!c) continue;
            acc[id] = 0;
            int pos, gi;
            if (!divisor(L, v, pos, gi)) { out.push_back({v, (u8)L, (u8)c}); continue; }
            if (TRACE) USE[gi] = (USE[gi] + c) % P;
            const Poly &g = G[gi];
            int sl = LEAD[gi].first, vl = L - pos - sl;
            u32 uval = v / P3[L - pos], vval = v % P3[vl];
            for (size_t k = 1; k < g.size(); k++) {
                const T &t = g[k];
                int nl = pos + t.l + vl; if (nl > D) break;
                u32 nv = (uval * P3[t.l] + t.v) * P3[vl] + vval;
                addterm(nl, nv, -c * t.c); redops++;
            }
        }
    }
    return out;
}

// ---- sparse polynomials for building the relators ----
typedef unordered_map<u32, int> SP;  // key = l<<24 | v
inline u32 key(int l, u32 v) { return ((u32)l << 24) | v; }
SP mul(const SP &f, const SP &g) {
    SP h;
    for (auto &x : f) {
        int la = x.first >> 24; u32 va = x.first & 0xffffff;
        for (auto &y : g) {
            int lb = y.first >> 24; u32 vb = y.first & 0xffffff;
            if (la + lb > D) continue;
            u32 kk = key(la + lb, va * P3[lb] + vb);
            h[kk] = (h[kk] + x.second * y.second) % P;
        }
    }
    SP r; for (auto &x : h) { int c = (x.second % P + P) % P; if (c) r[x.first] = c; }
    return r;
}
// Coordinates. XCOORD=1: a = 1 + X_a (Magnus). Default (Y coordinates): a = E(Y_a) = sum_{k<=4} Y_a^k/k!,
// the truncated exponential, a^-1 -> E(-Y_a).  Y_a is the truncated logarithm of a; a^lam = E(lam Y_a) mod Y_a^5,
// so the torus (F_5^*)^3 (a -> a^lam, b -> b^mu, c -> c^nu, automorphisms of Gamma since every vertex group is
// Heisenberg) acts by Y_i -> lam_i Y_i and preserves I: the relator ideal is graded by multidegree mod 4.
bool XC = false;
int EC[P];  // 1/k! mod P, filled in main
SP gen(int x) {
    SP f; u32 v = 0;
    for (int k = 0; k <= (XC ? 1 : P - 1) && k <= D; k++) { f[key(k, v)] = XC ? 1 : EC[k]; v = v * 3 + x; }
    return f;
}
SP geninv(int x) {
    SP f; u32 v = 0;
    for (int k = 0; k <= (XC ? D : P - 1) && k <= D; k++) {
        int c = XC ? 1 : EC[k]; if (k % 2) c = (P - c) % P;
        f[key(k, v)] = c; v = v * 3 + x;
    }
    return f;
}
// drop words containing a run Y_i^5 (they lie in the ideal generated by the Y_i^5, which are generators)
bool hasrun5(int l, u32 v) {
    int run = 0, last = -1;
    for (int i = 0; i < l; i++) { int ch = v % 3; v /= 3; run = (ch == last) ? run + 1 : 1; last = ch; if (run >= P) return true; }
    return false;
}
SP killruns(const SP &f) { SP r; for (auto &x : f) if (!hasrun5(x.first >> 24, x.first & 0xffffff)) r.insert(x); return r; }
vector<pair<pair<int,u32>,int>> tolist(const SP &f, int cap) {
    vector<pair<pair<int,u32>,int>> r;
    for (auto &x : f) { int l = x.first >> 24; if (l <= cap && x.second) r.push_back({{l, x.first & 0xffffff}, x.second}); }
    return r;
}

struct Pend { int type, a, b, k, sdeg; vector<pair<pair<int,u32>,int>> f; };
vector<vector<Pend>> PEND;
vector<unordered_map<u32, vector<int>>> PRE, SUF;

void insert_(Poly r, Prov pv) {
    int inv = INV[r[0].c];
    for (auto &t : r) t.c = (u8)(t.c * inv % P);
    int n = G.size(); int ln = r[0].l; u32 vn = r[0].v;
    G.push_back(r); LEAD.push_back({ln, vn}); PROV.push_back(pv);
    LID[idx(ln, vn)] = n; bmset(idx(ln, vn)); hasLen[ln] = true; buildAC(LEAD);
    for (int k = 1; k < ln; k++) { PRE[k][vn / P3[ln - k]].push_back(n); SUF[k][vn % P3[k]].push_back(n); }
    for (int k = 1; k < ln; k++) {
        auto it = PRE[k].find(vn % P3[k]);
        if (it != PRE[k].end())
            for (int i : it->second) { int W = ln + LEAD[i].first - k; if (W <= D) PEND[W].push_back({1, n, i, k, W, {}}); }
        auto jt = SUF[k].find(vn / P3[ln - k]);
        if (jt != SUF[k].end())
            for (int i : jt->second) { if (i == n) continue; int W = LEAD[i].first + ln - k; if (W <= D) PEND[W].push_back({1, i, n, k, W, {}}); }
    }
}

vector<pair<pair<int,u32>,int>> spoly(int a, int b, int k) {
    int l1 = LEAD[a].first, l2 = LEAD[b].first; u32 v1 = LEAD[a].second, v2 = LEAD[b].second;
    int yl = l2 - k, xl = l1 - k; u32 yv = v2 % P3[yl], xv = v1 / P3[k];
    vector<pair<pair<int,u32>,int>> s;
    for (size_t q = 1; q < G[a].size(); q++) { auto &t = G[a][q]; if (t.l + yl > D) break; s.push_back({{t.l + yl, t.v * P3[yl] + yv}, t.c}); }
    for (size_t q = 1; q < G[b].size(); q++) { auto &t = G[b][q]; if (t.l + xl > D) break; s.push_back({{t.l + xl, xv * P3[t.l] + t.v}, P - t.c}); }
    return s;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: hidden_sb D Tab Tbc Tac Z5 prefix\n"); return 1; }
    D = atoi(argv[1]); int Tcap[3] = {atoi(argv[2]), atoi(argv[3]), atoi(argv[4])}; int Z5 = atoi(argv[5]);
    string prefix = argv[6];
    P3[0] = 1; for (int i = 1; i < 20; i++) P3[i] = P3[i - 1] * 3;
    OFF[0] = 0; for (int i = 1; i < 20; i++) OFF[i] = OFF[i - 1] + P3[i - 1];
    acc.assign(OFF[D + 1], 0); flag.assign(OFF[D + 1], 0); bm.assign(OFF[D + 1] / 64 + 1, 0);
    for (int i = 1; i < P; i++) for (int j = 1; j < P; j++) if (i * j % P == 1) INV[i] = j;
    EC[0] = 1; for (int k = 1; k < P; k++) EC[k] = EC[k - 1] * INV[k] % P;
    PEND.resize(D + 1); PRE.resize(D + 1); SUF.resize(D + 1); buildAC(LEAD);
    auto t0 = chrono::steady_clock::now();
    // relators
    vector<string> RN;
    XC = getenv("XCOORD") != nullptr;
    for (int x = 0; x < 3; x++) {
        SP f;
        if (XC) { f[key(0, 0)] = 1; for (int i = 0; i < P; i++) f = mul(f, gen(x)); f.erase(key(0, 0)); }
        else { u32 v = 0; for (int i = 0; i < P; i++) v = v * 3 + x; f[key(P, v)] = 1; }  // (E(Y)^5-1) = Y^5 * unit
        RN.push_back(string(1, "abc"[x]) + "^5");
        PEND[P].push_back({0, (int)RN.size() - 1, 0, 0, P, tolist(f, D)});
    }
    int E[3][2] = {{0, 1}, {1, 2}, {0, 2}};
    for (int e = 0; e < 3; e++) {
        int x = E[e][0], y = E[e][1];
        SP C = mul(mul(mul(geninv(x), geninv(y)), gen(x)), gen(y));
        SP Ci = mul(mul(mul(geninv(y), geninv(x)), gen(y)), gen(x));
        if (!XC) { C = killruns(C); Ci = killruns(Ci); }
        for (int z : {x, y}) {
            SP Dd = mul(mul(mul(Ci, geninv(z)), C), gen(z));
            Dd[key(0, 0)] = (Dd[key(0, 0)] + P - 1) % P; if (!Dd[key(0, 0)]) Dd.erase(key(0, 0));
            string nm = string("[") + "abc"[x] + "," + "abc"[y] + "," + "abc"[z] + "]";
            if (XC) { RN.push_back(nm); PEND[3].push_back({0, (int)RN.size() - 1, 0, 0, 3, tolist(Dd, Tcap[e])}); continue; }
            Dd = killruns(Dd);
            // split into torus-eigencomponents (multidegree mod 4); each lies in I
            map<int, SP> comp;
            for (auto &t : Dd) { auto m = mdeg(t.first >> 24, t.first & 0xffffff); comp[(m[0] % (P - 1)) * 16 + (m[1] % (P - 1)) * 4 + m[2] % (P - 1)].insert(t); }
            for (auto &cc : comp) {
                auto lst = tolist(cc.second, Tcap[e]); if (lst.empty()) continue;
                int lo = 99, hi = 0; for (auto &t : lst) { lo = min(lo, t.first.first); hi = max(hi, t.first.first); }
                char buf[64]; snprintf(buf, sizeof buf, "%s{%d%d%d}", nm.c_str(), cc.first / 16, cc.first / 4 % 4, cc.first % 4);
                // env SKIP: comma-separated component names to omit; env LOWONLY=1: keep only the lowest-degree part
                // (the homogeneous initial form) of every component; env LOWONLY_<name>... not used
                if (getenv("SKIP") && strstr(getenv("SKIP"), buf)) { fprintf(stderr, "skip %s\n", buf); continue; }
                if (getenv("LOWONLY")) { decltype(lst) l2; for (auto &t : lst) if (t.first.first == lo) l2.push_back(t); lst = l2; }
                if (getenv("LISTCOMP")) fprintf(stderr, "comp %s deg %d..%d terms %zu\n", buf, lo, hi, lst.size());
                RN.push_back(buf); PEND[lo].push_back({0, (int)RN.size() - 1, 0, 0, lo, lst});
            }
        }
        if (Z5 && 2 * P <= D) {
            SP Z; Z[key(2, x * 3 + y)] = 1; Z[key(2, y * 3 + x)] = P - 1;
            SP f; f[key(0, 0)] = 1; for (int i = 0; i < P; i++) f = mul(f, Z);
            RN.push_back(string("Z5_") + "abc"[x] + "abc"[y]);
            PEND[2 * P].push_back({0, (int)RN.size() - 1, 0, 0, 2 * P, tolist(f, D)});
        }
    }
    long long npairs = 0, nzero = 0;
    map<pair<int,int>, int> jumps;
    for (int d = 0; d <= D; d++) {
        for (size_t q = 0; q < PEND[d].size(); q++) {
            Pend pe = PEND[d][q];
            vector<pair<pair<int,u32>,int>> f = pe.type == 1 ? spoly(pe.a, pe.b, pe.k) : pe.f;
            if (pe.type == 1) npairs++;
            long long r0 = redops;
            Poly r = reduce_(f);
            if (getenv("PROF") && redops - r0 > 2000000) fprintf(stderr, "  item type %d sdeg %d a %d b %d k %d in %zu out %zu redops %lld lead %d\n", pe.type, pe.sdeg, pe.a, pe.b, pe.k, f.size(), r.size(), redops - r0, r.empty() ? -1 : (int)r[0].l);
            if (r.empty()) { nzero++; continue; }
            int ld = r[0].l;
            if (ld > d) {
                vector<pair<pair<int,u32>,int>> g; for (auto &t : r) g.push_back({{t.l, t.v}, t.c});
                PEND[ld].push_back({pe.type == 1 ? 2 : pe.type, pe.a, pe.b, pe.k, pe.sdeg, g});
                continue;
            }
            if (pe.sdeg < ld) jumps[{pe.sdeg, ld}]++;
            insert_(r, {pe.type, pe.a, pe.b, pe.k, pe.sdeg});
        }
        vector<Pend>().swap(PEND[d]);
        // interreduce: replace every tail by its normal form w.r.t. the current basis
        for (size_t n = 0; n < G.size(); n++) {
            vector<pair<pair<int,u32>,int>> tl;
            for (size_t q = 1; q < G[n].size(); q++) tl.push_back({{G[n][q].l, G[n][q].v}, G[n][q].c});
            long long r0 = redops;
            Poly r = reduce_(tl); Poly g{G[n][0]};
            if (getenv("PROF") && redops - r0 > 2000000) fprintf(stderr, "  interred #%zu in %zu out %zu redops %lld\n", n, tl.size(), r.size(), redops - r0); g.insert(g.end(), r.begin(), r.end()); G[n].swap(g);
        }
        double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
        fprintf(stderr, "deg %d basis %zu pairs %lld zero %lld redops %lld t=%.1fs\n", d, G.size(), npairs, nzero, redops, el);
    }
    // Hilbert function of A/I: normal words (closed under subwords), by multidegree
    static long long H[16][16][16]; memset(H, 0, sizeof H);
    vector<long long> Hd(D + 1, 0);
    vector<u32> layer{0}; H[0][0][0] = 1; Hd[0] = 1;
    for (int L = 1; L <= D; L++) {
        vector<u32> nl;
        for (u32 v : layer) for (int ch = 0; ch < 3; ch++) {
            u32 w = v * 3 + ch; int pos, gi;
            if (!divisor(L, w, pos, gi)) { nl.push_back(w); auto m = mdeg(L, w); H[m[0]][m[1]][m[2]]++; Hd[L]++; }
        }
        layer.swap(nl);
    }
    FILE *fh = fopen((prefix + ".hilb").c_str(), "w");
    for (int i = 0; i <= D; i++) for (int j = 0; j <= D; j++) for (int k = 0; k <= D; k++)
        if (H[i][j][k]) fprintf(fh, "%d %d %d %lld\n", i, j, k, H[i][j][k]);
    fclose(fh);
    FILE *fl = fopen((prefix + ".leads").c_str(), "w");
    for (size_t n = 0; n < G.size(); n++) {
        auto &pv = PROV[n]; auto m = mdeg(LEAD[n].first, LEAD[n].second);
        fprintf(fl, "%s %d %d %d %d type=%d", word(LEAD[n].first, LEAD[n].second).c_str(), LEAD[n].first, m[0], m[1], m[2], pv.type);
        if (pv.type == 0) fprintf(fl, " rel=%s", RN[pv.a].c_str());
        else fprintf(fl, " A1=%s A2=%s k=%d", word(LEAD[pv.a].first, LEAD[pv.a].second).c_str(), word(LEAD[pv.b].first, LEAD[pv.b].second).c_str(), pv.k);
        fprintf(fl, " sdeg=%d nterms=%zu\n", pv.sdeg, G[n].size());
    }
    fclose(fl);
    printf("D=%d Tab=%d Tbc=%d Tac=%d Z5=%d basis=%zu pairs=%lld\n", D, Tcap[0], Tcap[1], Tcap[2], Z5, G.size(), npairs);
    printf("hilb by degree:"); long long tot = 0; for (int L = 0; L <= D; L++) { printf(" %lld", Hd[L]); tot += Hd[L]; } printf("  total %lld\n", tot);
    if (D >= 3 * P) printf("H(%d,%d,%d)=%lld\n", P, P, P, H[P][P][P]);
    printf("jumps (sdeg->leaddeg:count):"); for (auto &j : jumps) printf(" %d->%d:%d", j.first.first, j.first.second, j.second); printf("\n");
    double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    printf("time %.1fs\n", el);
    // env DUMP=i,j,...: write the full polynomials of these basis elements to prefix.dump
    if (getenv("DUMP")) {
        FILE *fo = fopen((prefix + ".dump").c_str(), "w"); string s = getenv("DUMP"); size_t st = 0;
        while (st < s.size()) { size_t e = s.find(',', st); if (e == string::npos) e = s.size(); size_t n = stoul(s.substr(st, e - st)); st = e + 1;
            if (n >= G.size()) continue; fprintf(fo, "#%zu %zu\n", n, G[n].size());
            for (auto &t : G[n]) fprintf(fo, "%s %d\n", word(t.l, t.v).c_str(), t.c); }
        fclose(fo);
    }
    // ---- hidden elements relative to a reference lead set ----
    vector<char> hidden(G.size(), 0);
    if (argc >= 9) {
        vector<pair<int,u32>> REF;
        FILE *fr = fopen(argv[8], "r"); char buf[4096];
        while (fgets(buf, sizeof buf, fr)) {
            char w[64]; if (sscanf(buf, "%63s", w) != 1) continue;
            int l = strlen(w); u32 v = 0; for (int i = 0; i < l; i++) v = v * 3 + (w[i] - 'a');
            REF.push_back({l, v});
        }
        fclose(fr);
        buildAC(REF);
        for (size_t n = 0; n < G.size(); n++) { int pos, gi; if (!divisor(LEAD[n].first, LEAD[n].second, pos, gi)) hidden[n] = 1; }
        buildAC(LEAD);
        FILE *fo = fopen((prefix + ".hidden").c_str(), "w");
        for (size_t n = 0; n < G.size(); n++) if (hidden[n]) {
            auto &pv = PROV[n]; auto m = mdeg(LEAD[n].first, LEAD[n].second);
            printf("hidden #%zu lead %s md (%d,%d,%d) type %d", n, word(LEAD[n].first, LEAD[n].second).c_str(), m[0], m[1], m[2], pv.type);
            if (pv.type) printf(" from overlap %s|%s k=%d (#%d,#%d) sdeg %d", word(LEAD[pv.a].first, LEAD[pv.a].second).c_str(), word(LEAD[pv.b].first, LEAD[pv.b].second).c_str(), pv.k, pv.a, pv.b, pv.sdeg);
            printf(" nterms %zu\n", G[n].size());
            fprintf(fo, "#%zu %zu\n", n, G[n].size());
            for (auto &t : G[n]) fprintf(fo, "%s %d\n", word(t.l, t.v).c_str(), t.c);
        }
        fclose(fo);
    }
    // ---- test vectors reduced modulo the lowest forms ----
    if (argc >= 8 && string(argv[7]) != "-") {
        for (auto &g : G) { int l0 = g[0].l; size_t q = 0; while (q < g.size() && g[q].l == l0) q++; g.resize(q); }
        FILE *ft = fopen(argv[7], "r"); FILE *fo = fopen((prefix + ".nf").c_str(), "w");
        int nv; if (fscanf(ft, "%d", &nv) != 1) nv = 0;
        for (int q = 0; q < nv; q++) {
            int m; if (fscanf(ft, "%d", &m) != 1) break;
            vector<pair<pair<int,u32>,int>> f;
            for (int i = 0; i < m; i++) {
                char w[64]; int c; if (fscanf(ft, "%63s %d", w, &c) != 2) break;
                int l = strlen(w); u32 v = 0; for (int j = 0; j < l; j++) v = v * 3 + (w[j] - 'a');
                if (l <= D) f.push_back({{l, v}, ((c % P) + P) % P});
            }
            USE.assign(G.size(), 0); TRACE = true;
            Poly r = reduce_(f); TRACE = false;
            printf("test %d: %d terms -> normal form %zu terms; hidden uses:", q, m, r.size());
            for (size_t n = 0; n < G.size(); n++) if (USE[n] && hidden[n]) printf(" #%zu*%d", n, USE[n]);
            printf("\n");
            fprintf(fo, "%zu\n", r.size()); for (auto &t : r) fprintf(fo, "%s %d\n", word(t.l, t.v).c_str(), t.c);
        }
        fclose(ft); fclose(fo);
    }
    return 0;
}
