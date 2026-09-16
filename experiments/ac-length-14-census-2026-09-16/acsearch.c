/* acsearch.c -- best-first Andrews-Curtis search on two-generator balanced presentations.
 *
 * Lane: counterexample swarm on `andrews-curtis-conjecture` (2026-09-16).
 * This program only PROPOSES certificates; acverify.py (independent Python) replays them.
 *
 * Letters use the census convention X = x^-1, Y = y^-1, coded by ASCII order
 *   'X'=0 'Y'=1 'x'=2 'y'=3,  inverse(c) = c ^ 2,
 * so integer order of packed words equals Python string order of equal-length words.
 *
 * State: a pair of cyclically reduced relators, each replaced by its canonical form
 * (least rotation of w or w^-1), the pair sorted by (length, word).
 *
 * Move cyc(j, s, t, e), j in {0,1}, i = 1-j, e = +-1:
 *   R_j <- canon( cyclic_reduction( rot_s(R_j) . rot_t(R_i^e) ) ),  then re-sort,
 * where rot_s(w) = w[s:] + w[:s] and R_i^e is inverted before rotating when e = -1.
 * Every cyc move is a composite of the moves (AC1)-(AC3) (see the artifact).
 *
 * Usage:
 *   acsearch triv  CAPREL CAPTOT BUDGET < census_lines        (id L r1 r2 per line)
 *   acsearch meet  CAPREL CAPTOT BUDGET_SRC BUDGET targets_file < census_lines
 * Output per input line:
 *   triv: "<id> SOLVED <nstates> <k> j s t e j s t e ..."  or "<id> OPEN <nstates> <reason>"
 *   meet: "<id> MEET <target_index> <nstates> <k> moves...  | <m> moves-from-target..." or OPEN
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXW 64

typedef struct { uint64_t a, b; } Key;

static int capRel, capTot;

static int code_of(char c) {
    switch (c) { case 'X': return 0; case 'Y': return 1; case 'x': return 2; case 'y': return 3; }
    return -1;
}
static const char LET[4] = {'X', 'Y', 'x', 'y'};

/* pack: first letter most significant; length in bits 58..63 */
static uint64_t pack(const uint8_t *w, int n) {
    uint64_t v = 0;
    for (int k = 0; k < n; k++) v = (v << 2) | w[k];
    return ((uint64_t)n << 58) | v;
}
static int unpack(uint64_t key, uint8_t *w) {
    int n = (int)(key >> 58);
    uint64_t v = key & ((1ULL << 58) - 1);
    for (int k = n - 1; k >= 0; k--) { w[k] = v & 3; v >>= 2; }
    return n;
}

/* least rotation among rotations of w and of w^-1 (n <= 28) */
static uint64_t canon(const uint8_t *w, int n) {
    uint8_t inv[MAXW];
    for (int k = 0; k < n; k++) inv[k] = w[n - 1 - k] ^ 2;
    uint64_t mask = (n == 0) ? 0 : ((n >= 29) ? 0 : ((1ULL << (2 * n)) - 1));
    uint64_t best = UINT64_MAX;
    for (int pass = 0; pass < 2; pass++) {
        const uint8_t *u = pass ? inv : w;
        uint64_t v = 0;
        for (int k = 0; k < n; k++) v = (v << 2) | u[k];
        for (int s = 0; s < n; s++) {
            uint64_t r = (s == 0) ? v : (((v << (2 * s)) & mask) | (v >> (2 * (n - s))));
            if (r < best) best = r;
        }
    }
    if (n == 0) best = 0;
    return ((uint64_t)n << 58) | best;
}

static Key mkstate(uint64_t p, uint64_t q) {
    Key k;
    if (p <= q) { k.a = p; k.b = q; } else { k.a = q; k.b = p; }
    return k;
}

/* free reduction of a.b followed by cyclic reduction (general, used as fallback) */
static int product_cycred(const uint8_t *a, int na, const uint8_t *b, int nb, uint8_t *out) {
    uint8_t st[2 * MAXW];
    int n = 0;
    for (int k = 0; k < na; k++) { if (n && st[n - 1] == (a[k] ^ 2)) n--; else st[n++] = a[k]; }
    for (int k = 0; k < nb; k++) { if (n && st[n - 1] == (b[k] ^ 2)) n--; else st[n++] = b[k]; }
    if (n == 0) return 0;
    int lo = 0, hi = n - 1;
    while (hi > lo && st[lo] == (st[hi] ^ 2)) { lo++; hi--; }
    int m = hi - lo + 1;
    memcpy(out, st + lo, (size_t)m);
    return m;
}

/* ---------------- node store, hash table, bucket queue ---------------- */
static Key *NK;          /* state */
static int32_t *NP;      /* parent node, -1 for a root */
static uint32_t *NM;     /* move: j | e<<1 | s<<2 | t<<10 */
static int32_t *NT;      /* tree tag: meet: 0 = the input class, 1+ = target index + 1; part: root index */
static int32_t *NX;      /* next in bucket list */
static uint32_t *NS;     /* hash slot, for fast reset */
static int32_t *HT;      /* hash table of node indices, -1 = empty */
static uint64_t HMASK;
static int32_t nn;
static int32_t BH[MAXW + 2], BT[MAXW + 2];

static uint64_t hkey(Key k) {
    uint64_t h = k.a * 0x9E3779B97F4A7C15ULL;
    h ^= (h >> 31) ^ (k.b * 0xC2B2AE3D27D4EB4FULL);
    h ^= h >> 29; h *= 0x94D049BB133111EBULL; h ^= h >> 32;
    return h;
}
static uint64_t slot_of(Key k) {
    uint64_t h = hkey(k) & HMASK;
    while (HT[h] >= 0) {
        int32_t v = HT[h];
        if (NK[v].a == k.a && NK[v].b == k.b) return h;
        h = (h + 1) & HMASK;
    }
    return h;
}
static void reset_store(void) {
    for (int32_t v = 0; v < nn; v++) HT[NS[v]] = -1;
    nn = 0;
    for (int b = 0; b <= MAXW + 1; b++) BH[b] = BT[b] = -1;
}
static int tot_of(Key k) { return (int)(k.a >> 58) + (int)(k.b >> 58); }
static int32_t add_node(Key k, uint64_t slot, int32_t parent, uint32_t move, int32_t tag) {
    int32_t v = nn++;
    NK[v] = k; NP[v] = parent; NM[v] = move; NT[v] = tag; NS[v] = (uint32_t)slot; NX[v] = -1;
    HT[slot] = v;
    int b = tot_of(k);
    if (BT[b] < 0) BH[b] = v; else NX[BT[b]] = v;
    BT[b] = v;
    return v;
}
static int32_t pop_min(int *minb) {
    while (*minb <= MAXW + 1 && BH[*minb] < 0) (*minb)++;
    if (*minb > MAXW + 1) return -1;
    int32_t v = BH[*minb];
    BH[*minb] = NX[v];
    if (BH[*minb] < 0) BT[*minb] = -1;
    return v;
}

/* ---------------- signed permutations (part mode works modulo these) ----------------
 * p = 4*swap + 2*[sx = -1] + [sy = -1];  x -> (swap ? y : x)^sx,  y -> (swap ? x : y)^sy,
 * the same indexing as AUTS in census_balanced.py. */
static uint8_t AUTMAP[8][4];
static void init_auts(void) {
    for (int p = 0; p < 8; p++) {
        uint8_t ix = (p & 4) ? 3 : 2, iy = (p & 4) ? 2 : 3;
        if (p & 2) ix ^= 2;
        if (p & 1) iy ^= 2;
        AUTMAP[p][2] = ix; AUTMAP[p][0] = ix ^ 2; AUTMAP[p][3] = iy; AUTMAP[p][1] = iy ^ 2;
    }
}
static int keyless(Key c, Key d) { return c.a < d.a || (c.a == d.a && c.b < d.b); }
/* least image of a canonical state under the 8 signed permutations; *pbest = first minimizer */
static Key autcanon(Key k, int *pbest) {
    uint8_t w0[MAXW], w1[MAXW], u0[MAXW], u1[MAXW];
    int n0 = unpack(k.a, w0), n1 = unpack(k.b, w1);
    Key best = k;
    *pbest = 0;
    for (int p = 1; p < 8; p++) {
        for (int q = 0; q < n0; q++) u0[q] = AUTMAP[p][w0[q]];
        for (int q = 0; q < n1; q++) u1[q] = AUTMAP[p][w1[q]];
        Key c = mkstate(canon(u0, n0), canon(u1, n1));
        if (keyless(c, best)) { best = c; *pbest = p; }
    }
    return best;
}

/* ---------------- search ---------------- */
static int modePart;
static int32_t *UF;
static long *ROOTID;
static int32_t ufind(int32_t r) { while (UF[r] != r) { UF[r] = UF[UF[r]]; r = UF[r]; } return r; }
static void report_pair(int32_t v, uint32_t mv, int32_t u);
static int modeMeet;
static long budget;
static int32_t meetA, meetB;
static uint32_t meetMove;
#define NOMOVE 0xFFFFFFFFu

/* expand node v.  Returns 1 on a hit (triv: new state of total length 2; meet: a
 * neighbour lying in the other tree), -2 when the budget is full, 0 otherwise. */
static int expand(int32_t v, int *minb) {
    uint8_t w[2][MAXW], wi[2][MAXW], out[2 * MAXW];
    int n[2];
    Key k = NK[v];
    n[0] = unpack(k.a, w[0]);
    n[1] = unpack(k.b, w[1]);
    for (int r = 0; r < 2; r++)
        for (int q = 0; q < n[r]; q++) wi[r][q] = w[r][n[r] - 1 - q] ^ 2;
    int32_t tag = NT[v];
    for (int j = 0; j < 2; j++) {
        int i = 1 - j;
        const uint8_t *A = w[j];
        int na = n[j];
        uint64_t keyi = (i == 0) ? k.a : k.b;
        uint64_t imgi[8];          /* part mode: canonical images of R_i under the signed permutations */
        if (modePart) {
            uint8_t u[MAXW];
            for (int p = 0; p < 8; p++) {
                for (int q = 0; q < n[i]; q++) u[q] = AUTMAP[p][w[i][q]];
                imgi[p] = canon(u, n[i]);
            }
        }
        for (int ei = 0; ei < 2; ei++) {
            const uint8_t *B = ei ? wi[i] : w[i];
            int nb = n[i];
            for (int s = 0; s < na; s++) {
                for (int t = 0; t < nb; t++) {
                    int mn = na < nb ? na : nb, c1 = 0, c2 = 0, m, general = 0;
                    /* cancellation at the junction rot_s(A) | rot_t(B) */
                    while (c1 < mn && A[(s - 1 - c1 + 2 * na) % na] == (B[(t + c1) % nb] ^ 2)) c1++;
                    if (c1 == mn) general = 1;
                    else {
                        int la = na - c1, lb = nb - c1, mm = la < lb ? la : lb;
                        /* cyclic cancellation between the first and last letters */
                        while (c2 < mm && A[(s + c2) % na] == (B[(t - 1 - c2 + 2 * nb) % nb] ^ 2)) c2++;
                        if (c2 == mm) general = 1;
                    }
                    if (!general) {
                        m = na + nb - 2 * c1 - 2 * c2;
                        if (m > capRel || m + nb > capTot) continue;
                        int p = 0;
                        for (int q = c2; q < na - c1; q++) out[p++] = A[(s + q) % na];
                        for (int q = c1; q < nb - c2; q++) out[p++] = B[(t + q) % nb];
                    } else {
                        uint8_t ra[MAXW], rb[MAXW];
                        for (int q = 0; q < na; q++) ra[q] = A[(s + q) % na];
                        for (int q = 0; q < nb; q++) rb[q] = B[(t + q) % nb];
                        m = product_cycred(ra, na, rb, nb, out);
                        if (m == 0 || m > capRel || m + nb > capTot) continue;
                    }
                    Key nk = mkstate(canon(out, m), keyi);
                    uint32_t mv = (uint32_t)j | ((uint32_t)ei << 1) | ((uint32_t)s << 2) | ((uint32_t)t << 10);
                    if (modePart) {        /* least image under the 8 signed permutations (same as autcanon) */
                        uint8_t u[2 * MAXW];
                        int pbest = 0;
                        for (int p = 1; p < 8; p++) {
                            for (int q = 0; q < m; q++) u[q] = AUTMAP[p][out[q]];
                            Key c = mkstate(canon(u, m), imgi[p]);
                            if (keyless(c, nk)) { nk = c; pbest = p; }
                        }
                        mv |= (uint32_t)pbest << 18;
                    }
                    uint64_t sl = slot_of(nk);
                    int32_t u = HT[sl];
                    if (u >= 0) {
                        if (modeMeet && ((NT[u] == 0) != (tag == 0))) { meetA = v; meetB = u; meetMove = mv; return 1; }
                        if (modePart && ufind(NT[u]) != ufind(tag)) report_pair(v, mv, u);
                        continue;
                    }
                    if (nn >= budget) return -2;
                    u = add_node(nk, sl, v, mv, tag);
                    if (tot_of(nk) < *minb) *minb = tot_of(nk);
                    if (!modeMeet && !modePart && tot_of(nk) == 2) { meetA = u; return 1; }
                }
            }
        }
    }
    return 0;
}

/* returns 1 hit, 0 exhausted, -2 budget */
static int run_search(const Key *roots, const int32_t *tags, int nroots) {
    reset_store();
    int minb = MAXW + 1;
    for (int r = 0; r < nroots; r++) {
        uint64_t sl = slot_of(roots[r]);
        if (HT[sl] >= 0) {
            int32_t u = HT[sl];
            if (modeMeet && ((NT[u] == 0) != (tags[r] == 0))) {
                /* the class equals target root r (target index r-1): meetB = -(r+2) */
                meetA = u; meetMove = NOMOVE;
                meetB = -(r + 2);
                return 1;
            }
            continue;
        }
        int32_t v = add_node(roots[r], sl, -1, NOMOVE, tags[r]);
        if (tot_of(roots[r]) < minb) minb = tot_of(roots[r]);
        if (!modeMeet && tot_of(roots[r]) == 2) { meetA = v; return 1; }
    }
    for (;;) {
        int32_t v = pop_min(&minb);
        if (v < 0) return 0;
        int res = expand(v, &minb);
        if (res != 0) return res;
    }
}

static void print_move(uint32_t mv) {
    printf(" %u,%u,%u,%d", mv & 1u, (mv >> 2) & 0xFFu, (mv >> 10) & 0xFFu, ((mv >> 1) & 1u) ? -1 : 1);
    if (modePart) printf(",%u", (mv >> 18) & 7u);
}
/* print "<k> moves" for the path root -> v, then optionally one extra move */
static void print_path(int32_t v, uint32_t extra) {
    static uint32_t buf[1 << 22];
    int k = 0;
    for (int32_t u = v; u >= 0 && NP[u] >= 0 && k < (1 << 22); u = NP[u]) buf[k++] = NM[u];
    printf(" %d", k + (extra != NOMOVE));
    for (int q = k - 1; q >= 0; q--) print_move(buf[q]);
    if (extra != NOMOVE) print_move(extra);
}

static int *ROOTP;
/* part mode: roots ra = NT[v] and rb = NT[u] meet at state(u) = move mv applied to state(v) */
static void report_pair(int32_t v, uint32_t mv, int32_t u) {
    int32_t ra = NT[v], rb = NT[u];
    printf("PAIR %ld %d %ld %d %d", ROOTID[ra], ROOTP[ra], ROOTID[rb], ROOTP[rb], nn);
    print_path(v, mv);
    printf(" |");
    print_path(u, NOMOVE);
    printf("\n");
    fflush(stdout);
    UF[ufind(ra)] = ufind(rb);
}

static int parse_rel(const char *s, uint8_t *w) {
    int n = 0;
    for (; *s; s++) {
        int c = code_of(*s);
        if (c < 0 || n >= 28) return -1;
        w[n++] = (uint8_t)c;
    }
    return n;
}
static int rel_key(const char *s, uint64_t *key) {
    uint8_t w[MAXW];
    int n = parse_rel(s, w);
    if (n <= 0) return -1;
    for (int q = 0; q + 1 < n; q++) if (w[q] == (w[q + 1] ^ 2)) return -1;   /* not reduced */
    if (n > 1 && w[0] == (w[n - 1] ^ 2)) return -1;                        /* not cyclically reduced */
    *key = canon(w, n);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: acsearch triv|meet CAPREL CAPTOT BUDGET [targets]\n"); return 64; }
    modeMeet = (strcmp(argv[1], "meet") == 0);
    modePart = (strcmp(argv[1], "part") == 0);
    capRel = atoi(argv[2]); capTot = atoi(argv[3]); budget = atol(argv[4]);
    if (capRel < 1 || capRel > 28 || capTot < 2 || capTot > MAXW || budget < 1 || (modeMeet && argc < 6)) {
        fprintf(stderr, "bad arguments\n"); return 64;
    }
    long cap = budget + 16;
    uint64_t hs = 1;
    while (hs < 2 * (uint64_t)cap) hs <<= 1;
    HMASK = hs - 1;
    NK = malloc(sizeof(Key) * cap); NP = malloc(4 * cap); NM = malloc(4 * cap);
    NT = malloc(4 * cap); NX = malloc(4 * cap); NS = malloc(4 * cap); HT = malloc(4 * hs);
    if (!NK || !NP || !NM || !NT || !NX || !NS || !HT) { fprintf(stderr, "out of memory\n"); return 1; }
    for (uint64_t h = 0; h < hs; h++) HT[h] = -1;
    nn = 0;
    if (modePart) {
        enum { MAXROOTS = 4096 };
        static Key pr[MAXROOTS];
        char ln[256], s1[64], s2[64];
        long rid; int rl, np = 0;
        UF = malloc(4 * MAXROOTS); ROOTID = malloc(sizeof(long) * MAXROOTS); ROOTP = malloc(sizeof(int) * MAXROOTS);
        init_auts();
        while (np < MAXROOTS && fgets(ln, sizeof ln, stdin)) {
            uint64_t p, q;
            if (sscanf(ln, "%ld %d %63s %63s", &rid, &rl, s1, s2) != 4) continue;
            if (rel_key(s1, &p) || rel_key(s2, &q)) { printf("BADINPUT %ld\n", rid); continue; }
            pr[np] = autcanon(mkstate(p, q), &ROOTP[np]);
            ROOTID[np] = rid; UF[np] = np; np++;
        }
        reset_store();
        int minb = MAXW + 1, res = 0;
        for (int r = 0; r < np; r++) {
            uint64_t sl = slot_of(pr[r]);
            if (HT[sl] >= 0) {
                int32_t u = HT[sl];
                if (ufind(NT[u]) != ufind(r)) {
                    printf("PAIR %ld %d %ld %d %d 0 | 0\n", ROOTID[r], ROOTP[r], ROOTID[NT[u]], ROOTP[NT[u]], nn);
                    UF[ufind(r)] = ufind(NT[u]);
                }
                continue;
            }
            add_node(pr[r], sl, -1, NOMOVE, r);
            if (tot_of(pr[r]) < minb) minb = tot_of(pr[r]);
        }
        for (;;) {
            int32_t v = pop_min(&minb);
            if (v < 0) { res = 0; break; }
            if (expand(v, &minb) == -2) { res = -2; break; }
        }
        printf("END %d %s\n", nn, res == 0 ? "exhausted" : "budget");
        for (int r = 0; r < np; r++) printf("COMP %ld %ld\n", ROOTID[r], ROOTID[ufind(r)]);
        return 0;
    }
    Key roots[16]; int32_t tags[16]; int ntargets = 0;
    if (modeMeet) {
        FILE *f = fopen(argv[5], "r");
        char r1[64], r2[64];
        if (!f) { fprintf(stderr, "cannot open targets\n"); return 1; }
        while (ntargets < 15 && fscanf(f, "%63s %63s", r1, r2) == 2) {
            uint64_t p, q;
            if (rel_key(r1, &p) || rel_key(r2, &q)) { fprintf(stderr, "bad target\n"); return 1; }
            roots[1 + ntargets] = mkstate(p, q); tags[1 + ntargets] = ntargets + 1; ntargets++;
        }
        fclose(f);
    }
    char line[256], r1[64], r2[64];
    long id; int L;
    while (fgets(line, sizeof line, stdin)) {
        if (sscanf(line, "%ld %d %63s %63s", &id, &L, r1, r2) != 4) continue;
        uint64_t p, q;
        if (rel_key(r1, &p) || rel_key(r2, &q)) { printf("%ld BADINPUT\n", id); continue; }
        roots[0] = mkstate(p, q); tags[0] = 0;
        int res = run_search(roots, tags, 1 + (modeMeet ? ntargets : 0));
        if (res == 1 && !modeMeet) {
            printf("%ld SOLVED %d", id, nn);
            print_path(meetA, NOMOVE);
            printf("\n");
        } else if (res == 1) {
            printf("%ld MEET", id);
            if (meetB < -1) {                 /* the class is a target root */
                printf(" %d %d 0 | 0\n", -meetB - 3, nn);
            } else if (NT[meetA] == 0) {      /* class tree -> target tree */
                printf(" %d %d", NT[meetB] - 1, nn);
                print_path(meetA, meetMove); printf(" |"); print_path(meetB, NOMOVE); printf("\n");
            } else {                          /* target tree -> class tree */
                printf(" %d %d", NT[meetA] - 1, nn);
                print_path(meetB, NOMOVE); printf(" |"); print_path(meetA, meetMove); printf("\n");
            }
        } else {
            printf("%ld OPEN %d %s\n", id, nn, res == 0 ? "exhausted" : "budget");
        }
        fflush(stdout);
    }
    return 0;
}
