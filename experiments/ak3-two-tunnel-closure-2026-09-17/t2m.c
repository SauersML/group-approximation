/* t2m.c -- 2-tunnels above the cap through a deduplicated set of Whitehead-minimal
 * intermediate states (lane w7-082, 2026-09-18).
 *
 * Let T = T_CAP be the tunnel-closed component (a union of dump files, e.g. S_24 plus the
 * tunnel-only states).  A 1-tunnel from s in T is an (M1) product of length > CAP followed by
 * greedy Whitehead reduction to a minimal pair m.  Let M = the set of such m with
 * CAP < |m| <= C2, up to swapping entries and signed permutations of generators.
 * A 2-tunnel is a 1-tunnel to m in M followed by any (M1) product from m and greedy Whitehead
 * reduction again.  It depends only on the class of m, so we enumerate M once (mode A) and then
 * apply every (M1) product to each m in M (mode B).
 *
 *   t2m A RANK CAP C2 base[,base2..] lo hi out
 *       states lo..hi-1 of the concatenated base: write the classes of m (CAP < |m| <= C2).
 *   t2m B RANK CAP C2 base[,base2..] mlist lo hi out
 *       entries lo..hi-1 of mlist: goal test of m (PRIM / THICK after planarity prefilter /
 *       PROJ in rank 3); then every (M1) product p from m:
 *         |p| <= CAP: NEW if p is not in T (a capped move from m, i.e. a 2-tunnel landing);
 *         else reduce p to m'; PRIM if m' has an entry of length 1;
 *              |m'| <= CAP: NEW if m' is not in T;
 *              CAP < |m'| <= C2 and m' not in mlist: written to out (the next level, 3-tunnels).
 *
 * Membership in T does not depend on which Whitehead-minimal representative the greedy
 * reduction picks: minimal representatives of one Aut-orbit are joined by length-preserving
 * Whitehead moves (Whitehead's theorem), and T is closed under capped (M2).
 * Build: gcc -O2 -I. -o t2m t2m.c   (with thzsearch.c, thick2.c, tunnel.c alongside)
 */
#define TUNNEL_NO_MAIN
#include "tunnel.c"

/* a second hash set for M */
static Key *ms; static uint32_t *mtab; static uint64_t mmask; static uint32_t nms = 0, maxms;
static void mset_init(uint32_t cap) {
    maxms = cap; uint64_t ts = 1; while (ts < 2ULL * cap) ts <<= 1; mmask = ts - 1;
    ms = malloc(sizeof(Key) * cap); mtab = calloc(ts, 4);
    if (!ms || !mtab) { fprintf(stderr, "oom mset\n"); exit(3); }
}
static int mset_insert(Key k) { /* 1 new, 0 present, -1 full */
    uint64_t h = hkey(k) & mmask;
    while (mtab[h]) { Key *s = &ms[mtab[h] - 1]; if (s->a == k.a && s->b == k.b) return 0; h = (h + 1) & mmask; }
    if (nms >= maxms) return -1;
    ms[nms] = k; mtab[h] = ++nms; return 1;
}
static int mset_has(Key k) {
    uint64_t h = hkey(k) & mmask;
    while (mtab[h]) { Key *s = &ms[mtab[h] - 1]; if (s->a == k.a && s->b == k.b) return 1; h = (h + 1) & mmask; }
    return 0;
}
static int in_base(Key kk) {
    uint64_t h = hkey(kk) & tmask;
    while (table[h]) { Key *s = &states[table[h] - 1]; if (s->a == kk.a && s->b == kk.b) return 1; h = (h + 1) & tmask; }
    return 0;
}
static void load_base(const char *list) {
    char buf[4096]; strncpy(buf, list, sizeof buf - 1); buf[sizeof buf - 1] = 0;
    char s1[256], s2[256];
    for (char *tok = strtok(buf, ","); tok; tok = strtok(NULL, ",")) {
        FILE *f = fopen(tok, "r"); if (!f) { perror(tok); exit(3); }
        while (fscanf(f, "%255s %255s", s1, s2) == 2) { Word p, q; parse(s1, &p); parse(s2, &q); if (insert(canon_pair(&p, &q), 0) == -2) { fprintf(stderr, "base full\n"); exit(3); } }
        fclose(f);
    }
}

static int C2;
static unsigned long moves = 0, capped = 0, tunnels = 0, inrange = 0, newc = 0, prim = 0, nextlvl = 0, hist[128];
static FILE *out;
static char MODE;
static Key *outk; static uint32_t noutk = 0; /* mode B: next-level classes, deduplicated in mset */

/* all (M1) products from r; mode A collects m in range, mode B tests landings */
static void products(const Word *r, long idx) {
    for (int i = 0; i < 2; i++) {
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
                    nw.n = k; cycred(&nw); moves++;
                    if (nw.n == 0) continue;
                    Word a = nw, b = r[j];
                    if (a.n + b.n <= CAP) {
                        capped++;
                        if (MODE == 'B' && !in_base(canon_pair(&a, &b))) {
                            newc++; char t1[256], t2[256]; wstr(&a, t1); wstr(&b, t2);
                            printf("NEW capped from m %ld -> %s %s\n", idx, t1, t2); fflush(stdout);
                        }
                        continue;
                    }
                    tunnels++;
                    if (wminimize(&a, &b) < 0) { fprintf(stderr, "overflow\n"); continue; }
                    int Lm = a.n + b.n; hist[Lm < 127 ? Lm : 127]++;
                    if (a.n == 1 || b.n == 1) {
                        prim++; char t1[256], t2[256]; wstr(&a, t1); wstr(&b, t2);
                        printf("PRIM from %ld: %s %s\n", idx, t1, t2); fflush(stdout);
                    }
                    if (Lm <= CAP) {
                        if (MODE == 'B' && !in_base(canon_pair(&a, &b))) {
                            newc++; char t1[256], t2[256]; wstr(&a, t1); wstr(&b, t2);
                            printf("NEW tunnel from m %ld -> %s %s\n", idx, t1, t2); fflush(stdout);
                        }
                    } else if (Lm <= C2) {
                        inrange++;
                        Key kk = canon_pair(&a, &b);
                        if (MODE == 'A') { if (mset_insert(kk) < 0) { fprintf(stderr, "mset full\n"); exit(3); } }
                        else if (!mset_has(kk)) {
                            /* next level: dedup in a small local table appended to mset */
                            int r2 = mset_insert(kk);
                            if (r2 < 0) { fprintf(stderr, "mset full\n"); exit(3); }
                            if (r2 == 1) { outk[noutk++] = kk; nextlvl++; }
                        }
                    }
                }
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: t2m A RANK CAP C2 base lo hi out | t2m B RANK CAP C2 base mlist lo hi out\n"); return 2; }
    MODE = argv[1][0]; RANK = atoi(argv[2]); CAP = atoi(argv[3]); C2 = atoi(argv[4]); COUNT = 1;
    if (C2 > 2 * MAXL || C2 > 40) { fprintf(stderr, "C2 too large\n"); return 2; }
    init_perms(); init_was(); init_amask(); init_planar();
    maxstates = 2000000; uint64_t ts = 1; while (ts < 2ULL * maxstates) ts <<= 1; tmask = ts - 1;
    states = malloc(sizeof(Key) * maxstates); parent = malloc(4ULL * maxstates); table = calloc(ts, 4);
    if (!states || !parent || !table) { fprintf(stderr, "oom\n"); return 3; }
    load_base(argv[5]);
    char s1[256], s2[256];
    long lo, hi; const char *outname;
    if (MODE == 'A') {
        lo = atol(argv[6]); hi = atol(argv[7]); outname = argv[8];
        if (hi > nstates) hi = nstates;
        mset_init(30000000);
        printf("A RANK %d CAP %d C2 %d base %u states %ld..%ld\n", RANK, CAP, C2, nstates, lo, hi); fflush(stdout);
        for (long idx = lo; idx < hi; idx++) { Word r[2]; unpack(states[idx], &r[0], &r[1]); products(r, idx); }
        out = fopen(outname, "w");
        for (uint32_t i = 0; i < nms; i++) { Word p, q; unpack(ms[i], &p, &q); wstr(&p, s1); wstr(&q, s2); fprintf(out, "%s %s\n", s1, s2); }
        fclose(out);
        printf("DONE A %ld..%ld moves %lu capped %lu tunnels %lu in-range %lu classes %u PRIM %lu\n", lo, hi, moves, capped, tunnels, inrange, nms, prim);
    } else {
        if (argc < 10) { fprintf(stderr, "usage B\n"); return 2; }
        lo = atol(argv[7]); hi = atol(argv[8]); outname = argv[9];
        mset_init(40000000); outk = malloc(sizeof(Key) * 20000000);
        FILE *f = fopen(argv[6], "r"); if (!f) { perror("mlist"); return 3; }
        Word *mw = NULL; long nm = 0, capm = 0;
        while (fscanf(f, "%255s %255s", s1, s2) == 2) {
            Word p, q; parse(s1, &p); parse(s2, &q);
            if (mset_insert(canon_pair(&p, &q)) < 0) { fprintf(stderr, "mset full\n"); return 3; }
            if (nm >= lo && nm < hi) {
                if (2 * (nm - lo + 1) > capm) { capm = capm ? 2 * capm : 1 << 16; mw = realloc(mw, sizeof(Word) * capm); }
                mw[2 * (nm - lo)] = p; mw[2 * (nm - lo) + 1] = q;
            }
            nm++;
        }
        fclose(f);
        if (hi > nm) hi = nm;
        printf("B RANK %d CAP %d C2 %d base %u mlist %ld (classes %u) entries %ld..%ld\n", RANK, CAP, C2, nstates, nm, nms, lo, hi); fflush(stdout);
        unsigned long gprim = 0, gthick = 0, gproj = 0, planar = 0;
        for (long idx = lo; idx < hi; idx++) {
            Word *r = &mw[2 * (idx - lo)];
            /* goal test of m itself */
            if (is_primitive(&r[0]) || is_primitive(&r[1])) { gprim++; wstr(&r[0], s1); wstr(&r[1], s2); printf("GOAL PRIM m %ld: %s %s\n", idx, s1, s2); }
            if (r[0].n + r[1].n <= 2 * MAXL) {
                if (planar_pair(&r[0], &r[1])) { planar++; if (thick_pair(&r[0], &r[1])) { gthick++; wstr(&r[0], s1); wstr(&r[1], s2); printf("GOAL THICK m %ld: %s %s\n", idx, s1, s2); } }
                if (RANK == 3) {
                    int saveNP = NOPRIM; NOPRIM = 1; int gp = 0; int gl = goal(&r[0], &r[1], &gp); NOPRIM = saveNP;
                    if (gl == 3) { gproj++; wstr(&r[0], s1); wstr(&r[1], s2); printf("GOAL PROJ m %ld: %s %s g=%d\n", idx, s1, s2, gp); }
                }
            }
            fflush(stdout);
            products(r, idx);
            if ((idx - lo + 1) % 5000 == 0) { printf("progress %ld moves %lu tunnels %lu next %lu\n", idx - lo + 1, moves, tunnels, nextlvl); fflush(stdout); }
        }
        out = fopen(outname, "w");
        for (uint32_t i = 0; i < noutk; i++) { Word p, q; unpack(outk[i], &p, &q); wstr(&p, s1); wstr(&q, s2); fprintf(out, "%s %s\n", s1, s2); }
        fclose(out);
        printf("DONE B %ld..%ld moves %lu capped %lu tunnels %lu NEW %lu PRIM %lu next-level %lu goals-of-m PRIM %lu planar %lu THICK %lu PROJ %lu thick-calls %lu undecided %lu\n",
               lo, hi, moves, capped, tunnels, newc, prim, nextlvl, gprim, planar, gthick, gproj, thick_calls, thick_undec);
    }
    printf("HIST |m'|:");
    for (int l = 0; l < 128; l++) if (hist[l]) printf(" %d:%lu", l, hist[l]);
    printf("\n");
    return 0;
}
