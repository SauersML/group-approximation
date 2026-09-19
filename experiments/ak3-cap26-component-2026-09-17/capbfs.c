/* capbfs.c -- resumable breadth-first exhaustion of the capped AC component S_CAP.
 *
 * Same move graph, canonical form and state store as `thzsearch RANK CAP MAX r1 r2 dump`
 * (experiments/ak3-thick-z-pair-search-2026-09-17/thzsearch.c, included verbatim):
 *   (M1) r_i -> cyclic reduction of U . g V g^-1 (U a rotation of r_i, V a rotation of
 *        r_j^{+-1}, g empty or one letter), total length <= CAP;
 *   (M2) Whitehead automorphisms of type 2 applied to both relators, total length <= CAP;
 *   states up to signed permutations of the generators, swap, rotation and inversion.
 * The only additions are (a) a time budget with a binary checkpoint, so that a run longer
 * than one 1200 s slot is split into slots, (b) a PRIM test (some relator primitive, greedy
 * Whitehead reduction to length 1) on every new state, and (c) a length histogram.
 *
 * usage: capbfs RANK CAP MAXSTATES r1 r2 CKPT        start (CKPT = checkpoint path)
 *        capbfs resume CKPT                           continue from CKPT
 * env BUDGET = seconds per slot (default 1100).  Exit 7: budget spent, checkpoint written;
 * exit 0: EXHAUSTED, text dump written to CKPT.txt; exit 1: state limit (checkpoint written;
 * resume with a larger env MAXST); exit 5: PRIM found.
 * Build: gcc -O2 -I ../ak3-thick-z-pair-search-2026-09-17 -o capbfs capbfs.c
 */
#define main thz_main_unused
#include "thzsearch.c"
#undef main
#include <time.h>

typedef struct { uint32_t magic, rank, cap, nstates, head, levelend, depth, maxst; uint64_t prim_tests; } Hdr;

static uint64_t prim_tests = 0;
static long consider2(Word *p, Word *q, uint32_t par) {
    if (p->n + q->n > CAP || p->n == 0 || q->n == 0) return -1;
    {
        Word a = *p, b = *q; canon_cyc(&a); canon_cyc(&b);
        if (wcmp(&b, &a) < 0) { Word t = a; a = b; b = t; }
        Key rk = pack(&a, &b); uint64_t h = hkey(rk) & CACHEMASK;
        if (cache[h].a == rk.a && cache[h].b == rk.b) return -1;
        cache[h] = rk;
    }
    Key k = canon_pair(p, q);
    long r = insert(k, par);
    if (r >= 0) {
        prim_tests++;
        if (is_primitive(p) || is_primitive(q)) {
            char s1[128], s2[128]; wstr(p, s1); wstr(q, s2);
            printf("GOAL PRIM at state %ld: %s %s\n", r, s1, s2); fflush(stdout); exit(5);
        }
    }
    return r;
}
static void save(const char *path, Hdr *h) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "wb"); if (!f) { perror("ckpt"); exit(3); }
    fwrite(h, sizeof *h, 1, f); fwrite(states, sizeof(Key), h->nstates, f);
    if (fclose(f)) { perror("ckpt"); exit(3); }
    rename(tmp, path);
}
static void alloc_store(uint32_t maxst) {
    maxstates = maxst;
    uint64_t ts = 1; while (ts < 2ULL * maxstates) ts <<= 1; tmask = ts - 1;
    states = malloc(sizeof(Key) * maxstates); parent = malloc(4ULL * maxstates); table = calloc(ts, 4);
    if (!states || !parent || !table) { fprintf(stderr, "oom\n"); exit(3); }
}

int main(int argc, char **argv) {
    Hdr h; const char *ck;
    time_t t0 = time(NULL); long budget = getenv("BUDGET") ? atol(getenv("BUDGET")) : 1100;
    if (argc == 3 && !strcmp(argv[1], "resume")) {
        ck = argv[2];
        FILE *f = fopen(ck, "rb"); if (!f || fread(&h, sizeof h, 1, f) != 1 || h.magic != 0xAC26) { fprintf(stderr, "bad ckpt\n"); return 2; }
        if (getenv("MAXST") && (uint32_t)atol(getenv("MAXST")) > h.maxst) h.maxst = (uint32_t)atol(getenv("MAXST"));
        RANK = h.rank; CAP = h.cap; init_perms(); init_was(); alloc_store(h.maxst);
        if (fread(states, sizeof(Key), h.nstates, f) != h.nstates) { fprintf(stderr, "short ckpt\n"); return 2; }
        fclose(f);
        for (uint32_t i = 0; i < h.nstates; i++) {       /* rebuild the hash table */
            uint64_t x = hkey(states[i]) & tmask; while (table[x]) x = (x + 1) & tmask; table[x] = i + 1;
        }
        nstates = h.nstates; prim_tests = h.prim_tests;
        printf("resumed %s: states %u head %u depth %u\n", ck, h.nstates, h.head, h.depth);
    } else if (argc == 7) {
        RANK = atoi(argv[1]); CAP = atoi(argv[2]); ck = argv[6];
        if (CAP > MAXL) { fprintf(stderr, "CAP too large\n"); return 2; }
        init_perms(); init_was(); alloc_store((uint32_t)atol(argv[3]));
        Word p, q; parse(argv[4], &p); parse(argv[5], &q);
        insert(canon_pair(&p, &q), 0);
        memset(&h, 0, sizeof h); h.magic = 0xAC26; h.rank = RANK; h.cap = CAP; h.maxst = maxstates;
        h.head = 0; h.levelend = 1; h.depth = 0;
        printf("RANK %d CAP %d NPERM %d NWA %d\n", RANK, CAP, NPERM, NWA);
    } else { fprintf(stderr, "usage: capbfs RANK CAP MAX r1 r2 CKPT | capbfs resume CKPT\n"); return 2; }
    uint32_t head = h.head, levelend = h.levelend; int depth = h.depth, full = 0;
    while (head < nstates) {
        if (head == levelend) { depth++; levelend = nstates; printf("depth %d states %u\n", depth, nstates); fflush(stdout); }
        if ((head & 1023) == 0 && time(NULL) - t0 > budget) {
            h.nstates = nstates; h.head = head; h.levelend = levelend; h.depth = depth; h.prim_tests = prim_tests;
            save(ck, &h); printf("SLOT END states %u head %u depth %d\n", nstates, head, depth); return 7;
        }
        Word r[2]; unpack(states[head], &r[0], &r[1]);
        for (int t = 0; t < NWA && !full; t++) {
            Word a, b;
            if (!apply_wa(&was[t], &r[0], &a) || !apply_wa(&was[t], &r[1], &b)) continue;
            if (consider2(&a, &b, head) == -2) full = 1;
        }
        for (int i = 0; i < 2 && !full; i++) {
            int j = 1 - i; Word U = r[i];
            for (int eps = -1; eps <= 1; eps += 2) {
                Word V = r[j];
                if (eps < 0) for (int m = 0; m < V.n; m++) V.w[m] = -r[j].w[V.n - 1 - m];
                for (int g = 0; g <= 2 * RANK; g++) {
                    signed char gl = 0;
                    if (g > 0) gl = (signed char)((g + 1) / 2 * ((g & 1) ? 1 : -1));
                    for (int ra = 0; ra < U.n; ra++) for (int rb = 0; rb < V.n; rb++) {
                        Word nw; int k = 0;
                        for (int m = 0; m < U.n; m++) nw.w[k++] = U.w[(ra + m) % U.n];
                        if (gl) nw.w[k++] = gl;
                        for (int m = 0; m < V.n; m++) nw.w[k++] = V.w[(rb + m) % V.n];
                        if (gl) nw.w[k++] = -gl;
                        nw.n = k; cycred(&nw);
                        Word other = r[j];
                        if (consider2(&nw, &other, head) == -2) { full = 1; goto done; }
                    }
                }
            }
        }
    done:
        if (full) break;
        head++;
    }
    if (full) {   /* checkpoint at the unfinished head: resuming redoes it, inserts are idempotent */
        h.nstates = nstates; h.head = head; h.levelend = levelend; h.depth = depth; h.prim_tests = prim_tests;
        save(ck, &h); printf("STATE LIMIT %u reached at head %u; checkpoint written (resume with MAXST=...)\n", maxstates, head); return 1;
    }
    printf("EXHAUSTED depth %d states %u processed %u; PRIM tests %lu, goals PRIM 0\n", depth, nstates, head, (unsigned long)prim_tests);
    unsigned long hist[2 * MAXL + 2] = {0};
    char path[4096]; snprintf(path, sizeof path, "%s.txt", ck);
    FILE *f = fopen(path, "w");
    for (uint32_t i = 0; i < nstates; i++) {
        Word p, q; char s1[128], s2[128]; unpack(states[i], &p, &q); wstr(&p, s1); wstr(&q, s2);
        fprintf(f, "%s %s\n", s1, s2); hist[p.n + q.n]++;
    }
    fclose(f);
    printf("lengths:"); for (int L = 0; L <= CAP; L++) if (hist[L]) printf(" %d:%lu", L, hist[L]); printf("\n");
    printf("dumped %u states to %s\n", nstates, path);
    return 0;
}
