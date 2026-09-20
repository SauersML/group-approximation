// Exhaustive transversal search in W_p (Schroeppel-Shamir meet in the middle).
//
// Input (text): p m R, then m block ids (0..9), then m rows of R residues mod p.
// The rows are the images Phi_p(k_c) of the m twist classes in H_1(M'') (x) F_p,
// restricted to R coordinates that are independent on the span of the rows, so
// sum_c x_c Phi_p(k_c) = 0 on these coordinates iff it is 0 in F_p^corank.
// Output: every choice of one class per block (10 blocks) whose images sum to 0
// mod p, i.e. every transversal of W_p.  The search is exhaustive: the four
// lists are blocks {0,1}, {2,3,4}, {5,6}, {7,8,9}; for each value t of the
// projection pi to the first K coordinates we join {a in L1+L2 : pi(a) = t}
// with {b in L3+L4 : pi(b) = -t} on the full vector (hash, then exact compare).
//
// Usage: mitm input.txt K [max_print]
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <thread>
#include <vector>

static const int RMAX = 112;
typedef struct { uint8_t v[RMAX]; } Vec;

static int P, M, R, K;
static std::vector<int> blk;
static std::vector<Vec> rows;

static inline void addv(const Vec& a, const Vec& b, Vec& o) {
    for (int i = 0; i < RMAX; i++) {
        int s = a.v[i] + b.v[i];
        o.v[i] = (uint8_t)(s >= P ? s - P : s);
    }
}
static inline void negv(const Vec& a, Vec& o) {
    for (int i = 0; i < RMAX; i++) o.v[i] = (uint8_t)(a.v[i] ? P - a.v[i] : 0);
}
static inline uint64_t hashv(const Vec& a) {
    const uint64_t* w = (const uint64_t*)a.v;
    uint64_t h = 0x9e3779b97f4a7c15ULL;
    for (int i = 0; i < RMAX / 8; i++) {
        h ^= w[i] + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
        h *= 0xff51afd7ed558ccdULL;
    }
    return h ^ (h >> 33);
}
static inline uint32_t proj(const Vec& a) {
    uint32_t t = 0;
    for (int i = K - 1; i >= 0; i--) t = t * P + a.v[i];
    return t;
}

struct Item { Vec s; uint32_t pi; int idx[3]; };

static std::vector<Item> build(const std::vector<int>& bs) {
    std::vector<std::vector<int>> cls(bs.size());
    for (size_t j = 0; j < bs.size(); j++)
        for (int c = 0; c < M; c++) if (blk[c] == bs[j]) cls[j].push_back(c);
    std::vector<Item> out;
    std::vector<size_t> pos(bs.size(), 0);
    while (true) {
        Item it; memset(&it, 0, sizeof it);
        for (int j = 0; j < 3; j++) it.idx[j] = -1;
        for (size_t j = 0; j < bs.size(); j++) {
            int c = cls[j][pos[j]];
            it.idx[j] = c;
            Vec t; addv(it.s, rows[c], t); it.s = t;
        }
        it.pi = proj(it.s);
        out.push_back(it);
        size_t j = 0;
        while (j < bs.size() && ++pos[j] == cls[j].size()) { pos[j] = 0; j++; }
        if (j == bs.size()) break;
    }
    return out;
}

int main(int argc, char** argv) {
    FILE* f = fopen(argv[1], "r");
    K = atoi(argv[2]);
    long maxprint = argc > 3 ? atol(argv[3]) : 1000;
    if (fscanf(f, "%d %d %d", &P, &M, &R) != 3) return 1;
    if (R > RMAX) { fprintf(stderr, "R too big\n"); return 1; }
    blk.resize(M);
    for (int c = 0; c < M; c++) if (fscanf(f, "%d", &blk[c]) != 1) return 1;
    rows.resize(M);
    for (int c = 0; c < M; c++) {
        memset(rows[c].v, 0, RMAX);
        for (int i = 0; i < R; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; rows[c].v[i] = (uint8_t)(((x % P) + P) % P); }
    }
    fclose(f);
    uint32_t NT = 1; for (int i = 0; i < K; i++) NT *= P;
    std::vector<Item> L1 = build({0, 1}), L2 = build({2, 3, 4}), L3 = build({5, 6}), L4 = build({7, 8, 9});
    fprintf(stderr, "p=%d m=%d R=%d K=%d NT=%u lists %zu %zu %zu %zu\n", P, M, R, K, NT, L1.size(), L2.size(), L3.size(), L4.size());
    auto sortpi = [&](std::vector<Item>& L, std::vector<uint32_t>& off) {
        std::sort(L.begin(), L.end(), [](const Item& a, const Item& b) { return a.pi < b.pi; });
        off.assign(NT + 1, 0);
        for (auto& it : L) off[it.pi + 1]++;
        for (uint32_t t = 0; t < NT; t++) off[t + 1] += off[t];
    };
    std::vector<uint32_t> off2, off4;
    sortpi(L2, off2); sortpi(L4, off4);
    // digits of pi values, for t - pi(a1) computations
    auto digits = [&](uint32_t x, int* d) { for (int i = 0; i < K; i++) { d[i] = x % P; x /= P; } };
    auto undig = [&](const int* d) { uint32_t t = 0; for (int i = K - 1; i >= 0; i--) t = t * P + d[i]; return t; };
    std::vector<int> d1(L1.size() * K), d3(L3.size() * K);
    for (size_t i = 0; i < L1.size(); i++) digits(L1[i].pi, &d1[i * K]);
    for (size_t i = 0; i < L3.size(); i++) digits(L3[i].pi, &d3[i * K]);
    std::atomic<uint32_t> next(0);
    std::atomic<long> nsol(0), nhashhit(0);
    std::atomic<unsigned long long> work(0);
    std::mutex mu;
    int nth = std::max(1u, std::thread::hardware_concurrency());
    auto worker = [&]() {
        std::vector<std::pair<uint64_t, std::pair<int, int>>> A;
        std::vector<uint64_t> tab; std::vector<int> tabi;
        int td[16], e[16];
        unsigned long long w = 0;
        while (true) {
            uint32_t t = next++;
            if (t >= NT) break;
            digits(t, td);
            A.clear();
            for (size_t i = 0; i < L1.size(); i++) {
                for (int k = 0; k < K; k++) e[k] = (td[k] - d1[i * K + k] + P) % P;
                uint32_t u = undig(e);
                for (uint32_t j = off2[u]; j < off2[u + 1]; j++) {
                    Vec s; addv(L1[i].s, L2[j].s, s);
                    A.push_back({hashv(s), {(int)i, (int)j}});
                }
            }
            w += A.size();
            size_t cap = 1; while (cap < 2 * A.size() + 2) cap <<= 1;
            tab.assign(cap, 0); tabi.assign(cap, -1);
            for (size_t a = 0; a < A.size(); a++) {
                size_t h = A[a].first & (cap - 1);
                while (tabi[h] >= 0) h = (h + 1) & (cap - 1);
                tab[h] = A[a].first; tabi[h] = (int)a;
            }
            for (int k = 0; k < K; k++) td[k] = (P - td[k]) % P;   // -t
            for (size_t i = 0; i < L3.size(); i++) {
                for (int k = 0; k < K; k++) e[k] = (td[k] - d3[i * K + k] + P) % P;
                uint32_t u = undig(e);
                for (uint32_t j = off4[u]; j < off4[u + 1]; j++) {
                    Vec s, n; addv(L3[i].s, L4[j].s, s); negv(s, n);
                    uint64_t hv = hashv(n);
                    w++;
                    size_t h = hv & (cap - 1);
                    while (tabi[h] >= 0) {
                        if (tab[h] == hv) {
                            nhashhit++;
                            const auto& pr = A[tabi[h]].second;
                            Vec s2; addv(L1[pr.first].s, L2[pr.second].s, s2);
                            if (memcmp(s2.v, n.v, RMAX) == 0) {
                                long k = nsol++;
                                if (k < maxprint) {
                                    std::lock_guard<std::mutex> g(mu);
                                    int sol[10] = {L1[pr.first].idx[0], L1[pr.first].idx[1], L2[pr.second].idx[0], L2[pr.second].idx[1], L2[pr.second].idx[2],
                                                   L3[i].idx[0], L3[i].idx[1], L4[j].idx[0], L4[j].idx[1], L4[j].idx[2]};
                                    printf("SOL");
                                    for (int q = 0; q < 10; q++) printf(" %d", sol[q]);
                                    printf("\n");
                                    fflush(stdout);
                                }
                            }
                        }
                        h = (h + 1) & (cap - 1);
                    }
                }
            }
            for (int k = 0; k < K; k++) td[k] = (P - td[k]) % P;
            if ((t & 4095) == 0) fprintf(stderr, "t=%u/%u sols %ld\n", t, NT, (long)nsol);
        }
        work += w;
    };
    std::vector<std::thread> th;
    for (int i = 0; i < nth; i++) th.emplace_back(worker);
    for (auto& x : th) x.join();
    printf("DONE p=%d solutions %ld hashhits %ld pairs %llu\n", P, (long)nsol, (long)nhashhit, (unsigned long long)work);
    return 0;
}
