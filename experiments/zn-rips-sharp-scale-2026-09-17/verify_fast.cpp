// Second independent certificate checker (C++), written separately from uniform.cpp and verify.py.
// Same semantics as verify.py (see its docstring):
//   Lmax = { x in Z^n : |x|_1 <= r, last nonzero coordinate > 0 };  C := Lmax.
//   "D x | w"      : x,w in C, w != x, w in hull(0,x), every z in C with d(z,x) <= r has d(z,w) <= r; C -= x.
//   "K x | p m"    : S = {z in C : z != x, d(z,x) <= r}; p in S, p in hull(0,x); then m lines "y | w":
//                    y,w in S, y != w, w in hull(0,x,y), every z in S with d(z,y) <= r has d(z,w) <= r; S -= y.
//                    At the end S == {p}.  C -= x.
//   Accept iff every move checks and the final C == {e_1..e_n}.
// Build: g++ -O2 -o verify_fast verify_fast.cpp     Run: ./verify_fast n r certfile [statefile [budget_s]]
// With a statefile, the replay stops at a move boundary after budget_s seconds (default 1000), saves C, the byte
// offset and the counters, and a rerun resumes. The state records n, r and the certificate size.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <unordered_map>
#include <ctime>

static int n, r;
static std::vector<signed char> P;   // |Lmax| * n
static std::unordered_map<long long, int> idx;

static void fail(const char* what, long long line) {
    std::printf("REJECT: %s at certificate line %lld\n", what, line);
    std::exit(1);
}
static long long key(const int* v) {
    long long k = 0;
    for (int i = 0; i < n; i++) k = k * (2 * r + 1) + (v[i] + r);
    return k;
}
static int dist(int a, int b) {
    int s = 0;
    const signed char* pa = &P[(size_t)a * n]; const signed char* pb = &P[(size_t)b * n];
    for (int i = 0; i < n; i++) s += std::abs(pa[i] - pb[i]);
    return s;
}
static void gen(std::vector<int>& cur, int budget) {
    if ((int)cur.size() == n) {
        int last = 0;
        for (int i = n - 1; i >= 0; i--) if (cur[i]) { last = cur[i]; break; }
        if (last > 0) {
            idx[key(cur.data())] = (int)(P.size() / n);
            for (int v : cur) P.push_back((signed char)v);
        }
        return;
    }
    for (int v = -budget; v <= budget; v++) { cur.push_back(v); gen(cur, budget - std::abs(v)); cur.pop_back(); }
}
// in hull(0, a[, b]) coordinatewise
static bool inhull(int w, int a, int b) {
    for (int i = 0; i < n; i++) {
        int lo = 0, hi = 0, va = P[(size_t)a * n + i];
        lo = std::min(lo, va); hi = std::max(hi, va);
        if (b >= 0) { int vb = P[(size_t)b * n + i]; lo = std::min(lo, vb); hi = std::max(hi, vb); }
        int vw = P[(size_t)w * n + i];
        if (vw < lo || vw > hi) return false;
    }
    return true;
}
// parse "a1 .. an | b1 .. bk [extra]" ; returns number of ints after '|'
static int parse(const char* s, int* a, int* b, int maxb) {
    char* e;
    for (int i = 0; i < n; i++) { a[i] = (int)std::strtol(s, &e, 10); if (e == s) return -1; s = e; }
    while (*s == ' ') s++;
    if (*s != '|') return -1;
    s++;
    int k = 0;
    while (k < maxb) { long v = std::strtol(s, &e, 10); if (e == s) break; b[k++] = (int)v; s = e; }
    return k;
}
static int lookup(const int* v) {
    int s = 0;
    for (int i = 0; i < n; i++) s += std::abs(v[i]);
    if (s > r) return -1;
    auto it = idx.find(key(v));
    return it == idx.end() ? -1 : it->second;
}

int main(int argc, char** argv) {
    if (argc < 4) { std::fprintf(stderr, "usage: verify_fast n r cert\n"); return 2; }
    n = std::atoi(argv[1]); r = std::atoi(argv[2]);
    std::vector<int> cur; gen(cur, r);
    int M = (int)(P.size() / n);
    std::vector<char> alive(M, 1);
    FILE* f = std::fopen(argv[3], "r");
    if (!f) { std::perror("cert"); return 2; }
    const char* state = argc > 4 ? argv[4] : nullptr;
    double budget = argc > 5 ? std::atof(argv[5]) : 1000.0;
    std::fseek(f, 0, SEEK_END); long long fsize = std::ftell(f); std::fseek(f, 0, SEEK_SET);
    time_t t0 = std::time(nullptr);
    static char buf[1 << 16];
    long long line = 0, nD = 0, nK = 0, nsteps = 0;
    int a[64], b[64];
    std::vector<int> S; std::vector<char> inS(M, 0);
    long long pos0 = 0;
    if (state) {
        FILE* st = std::fopen(state, "rb");
        if (st) {
            long long hdr[7];
            if (std::fread(hdr, sizeof hdr, 1, st) != 1 || hdr[0] != n || hdr[1] != r || hdr[2] != fsize || hdr[3] != M)
                { std::printf("state does not match certificate\n"); return 2; }
            if (std::fread(alive.data(), 1, M, st) != (size_t)M) { std::printf("bad state\n"); return 2; }
            pos0 = hdr[4]; nD = hdr[5]; nK = hdr[6];
            if (std::fread(&nsteps, sizeof nsteps, 1, st) != 1 || std::fread(&line, sizeof line, 1, st) != 1)
                { std::printf("bad state\n"); return 2; }
            std::fclose(st);
            std::fseek(f, pos0, SEEK_SET);
        }
    }
    for (;;) {
        if (state && std::ftell(f) > pos0 && std::difftime(std::time(nullptr), t0) > budget) {
            long long pos = std::ftell(f);
            std::string tmp = std::string(state) + ".tmp";
            FILE* st = std::fopen(tmp.c_str(), "wb");
            long long hdr[7] = {n, r, fsize, M, pos, nD, nK};
            std::fwrite(hdr, sizeof hdr, 1, st); std::fwrite(alive.data(), 1, M, st);
            std::fwrite(&nsteps, sizeof nsteps, 1, st); std::fwrite(&line, sizeof line, 1, st);
            std::fclose(st); std::rename(tmp.c_str(), state);
            std::printf("checkpoint at byte %lld/%lld: D=%lld K=%lld linksteps=%lld; rerun to continue\n", pos, fsize, nD, nK, nsteps);
            return 3;
        }
        if (!std::fgets(buf, sizeof buf, f)) break;
        line++;
        char kind = buf[0];
        int k = parse(buf + 1, a, b, 64);
        int x = lookup(a);
        if (x < 0 || !alive[x]) fail("x not alive", line);
        if (kind == 'D') {
            if (k != n) fail("bad D line", line);
            int w = lookup(b);
            if (w < 0 || !alive[w] || w == x || !inhull(w, x, -1)) fail("bad D dominator", line);
            for (int z = 0; z < M; z++)
                if (alive[z] && dist(z, x) <= r && dist(z, w) > r) fail("D not dominated", line);
            nD++;
        } else if (kind == 'K') {
            if (k != n + 1) fail("bad K line", line);
            int p = lookup(b); long long m = b[n];
            S.clear();
            for (int z = 0; z < M; z++) if (alive[z] && z != x && dist(z, x) <= r) { S.push_back(z); inS[z] = 1; }
            if (p < 0 || !inS[p] || !inhull(p, x, -1)) fail("bad K survivor", line);
            for (long long j = 0; j < m; j++) {
                if (!std::fgets(buf, sizeof buf, f)) fail("truncated K", line);
                line++;
                if (parse(buf, a, b, 64) != n) fail("bad K step line", line);
                int y = lookup(a), w = lookup(b);
                if (y < 0 || w < 0 || !inS[y] || !inS[w] || y == w || !inhull(w, x, y)) fail("bad K step", line);
                for (int z : S) if (inS[z] && dist(z, y) <= r && dist(z, w) > r) fail("K step not dominated", line);
                inS[y] = 0; nsteps++;
            }
            int cnt = 0;
            for (int z : S) cnt += inS[z];
            if (cnt != 1 || !inS[p]) fail("K link not collapsed to p", line);
            for (int z : S) inS[z] = 0;
            nK++;
        } else fail("unknown move", line);
        alive[x] = 0;
    }
    std::vector<int> fin;
    for (int z = 0; z < M; z++) if (alive[z]) fin.push_back(z);
    bool basis = (int)fin.size() == n;
    if (basis) {
        std::vector<char> seen(n, 0);
        for (int z : fin) {
            int ones = 0, pos = -1, other = 0;
            for (int i = 0; i < n; i++) { int v = P[(size_t)z * n + i]; if (v == 1) { ones++; pos = i; } else if (v != 0) other++; }
            if (ones != 1 || other) basis = false; else seen[pos] = 1;
        }
        for (int i = 0; i < n; i++) if (!seen[i]) basis = false;
    }
    std::printf("n=%d r=%d |Lmax|=%d D=%lld K=%lld linksteps=%lld |K|=%zu basis=%s\n", n, r, M, nD, nK, nsteps,
                fin.size(), basis ? "True" : "False");
    if (!basis) { std::printf("REJECT: final set is not the basis\n"); return 1; }
    std::printf("ACCEPT\n");
    return 0;
}
