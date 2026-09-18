/* thzsearch.c -- pzsearch.c (experiments/ak3-stable-primitive-search-2026-09-17) with a
 * TOPOLOGICAL goal added.  Breadth-first search over relator pairs (r1, r2) in F_RANK under
 *   (M1) AC products  r_i -> cyclic reduction of  U . g V g^-1  (U a rotation of r_i,
 *        V a rotation of r_j^{+-1}, g empty or a single letter);
 *   (M2) Whitehead automorphisms of type 2 of F_RANK, applied to both relators;
 *   (M0) signed permutations, rotation, inversion (canonicalisation only).
 * Goals (the first one met is reported):
 *   PRIM   some relator is primitive in F_RANK (research/one-stabilization-ac-trivial-from-primitive-relator);
 *   THICK  the presentation complex of <F_RANK | r1, r2> is orientably thickenable
 *          (Neuwirth test thick2.c, copied from experiments/ac-thickenable-orbit-2026-09-17);
 *          RANK 3: research/one-stabilization-ac-trivial-from-thickenable-z-pair gives S+ AC-trivial;
 *          RANK 2: Lackenby Thm 1.3 gives the rank-2 presentation AC-trivial;
 *   PROJ   (RANK 3) some generator g has exponent-sum minor +-1 and the rank-2 projection P_g(r)
 *          (delete g) is thickenable; Step 5 of the primitive-criterion route + Lackenby.
 * usage: thzsearch RANK CAP MAXSTATES r1 r2 [count|noprim|count-noprim]   words over xyzXYZ (X = x^-1)
 * "count": do not stop at a goal, print per-goal counts at the end. "noprim": drop the PRIM goal.
 * "dump": run the BFS with no goal test and write every state of the component to $THZ_DUMP.
 * check mode:  thzsearch check RANK [noprim] < pairs.txt   tests the goals on each line "r1 r2".
 * Single-threaded; memory ~ 40 bytes * MAXSTATES + 128MB cache.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "thick2.c"

#define MAXL 38
typedef struct { signed char w[200]; int n; } Word;

static int RANK = 3, CAP = 16;

static void freered(Word *u) {
    int k = 0;
    for (int i = 0; i < u->n; i++) {
        if (k > 0 && u->w[k - 1] == -u->w[i]) k--;
        else u->w[k++] = u->w[i];
    }
    u->n = k;
}
static void cycred(Word *u) {
    freered(u);
    int a = 0, b = u->n - 1;
    while (b > a && u->w[a] == -u->w[b]) { a++; b--; }
    int n = b - a + 1;
    if (u->n == 0) n = 0;
    memmove(u->w, u->w + a, n);
    u->n = n;
}
static int code(signed char c) { return c > 0 ? 2 * c - 1 : -2 * c; } /* x=1 X=2 y=3 Y=4 z=5 Z=6 */

/* least rotation (Booth) of codes s[0..n-1]; returns start index */
static int booth(const unsigned char *s, int n) {
    int f[2 * 200 + 2]; for (int i = 0; i < 2 * n; i++) f[i] = -1;
    int k = 0;
    for (int j = 1; j < 2 * n; j++) {
        unsigned char sj = s[j % n]; int i = f[j - k - 1];
        while (i != -1 && sj != s[(k + i + 1) % n]) {
            if (sj < s[(k + i + 1) % n]) k = j - i - 1;
            i = f[i];
        }
        if (sj != s[(k + i + 1) % n]) {
            if (sj < s[k % n]) k = j;
            f[j - k] = -1;
        } else f[j - k] = i + 1;
    }
    return k % n;
}
/* lexicographically least rotation of w or w^-1 (w cyclically reduced) */
static void canon_cyc(Word *u) {
    int n = u->n;
    if (n == 0) return;
    unsigned char c1[200], c2[200];
    for (int i = 0; i < n; i++) { c1[i] = (unsigned char)code(u->w[i]); c2[i] = (unsigned char)code(-u->w[n - 1 - i]); }
    int k1 = booth(c1, n), k2 = booth(c2, n);
    int use2 = 0;
    for (int i = 0; i < n; i++) { unsigned char a = c1[(k1 + i) % n], b = c2[(k2 + i) % n]; if (a != b) { use2 = b < a; break; } }
    signed char out[200];
    if (!use2) for (int i = 0; i < n; i++) out[i] = u->w[(k1 + i) % n];
    else for (int i = 0; i < n; i++) out[i] = -u->w[n - 1 - ((k2 + i) % n)];
    memcpy(u->w, out, n);
}
static int wcmp(const Word *a, const Word *b) {
    if (a->n != b->n) return a->n < b->n ? -1 : 1;
    for (int i = 0; i < a->n; i++)
        if (code(a->w[i]) != code(b->w[i])) return code(a->w[i]) < code(b->w[i]) ? -1 : 1;
    return 0;
}
typedef struct { uint64_t a, b; } Key;

static Key pack(const Word *p, const Word *q) {
    Key k = {0, 0};
    /* 128 bits: n1 (6) n2 (6) then 3 bits per letter */
    unsigned __int128 v = 0;
    int bits = 0;
    v |= (unsigned __int128)p->n; bits += 6;
    v |= (unsigned __int128)q->n << bits; bits += 6;
    for (int i = 0; i < p->n; i++) { v |= (unsigned __int128)code(p->w[i]) << bits; bits += 3; }
    for (int i = 0; i < q->n; i++) { v |= (unsigned __int128)code(q->w[i]) << bits; bits += 3; }
    k.a = (uint64_t)v; k.b = (uint64_t)(v >> 64);
    return k;
}
static void unpack(Key k, Word *p, Word *q) {
    unsigned __int128 v = ((unsigned __int128)k.b << 64) | k.a;
    p->n = (int)(v & 63); v >>= 6;
    q->n = (int)(v & 63); v >>= 6;
    for (int i = 0; i < p->n; i++) { int c = (int)(v & 7); v >>= 3; p->w[i] = (c & 1) ? (c + 1) / 2 : -(c / 2); }
    for (int i = 0; i < q->n; i++) { int c = (int)(v & 7); v >>= 3; q->w[i] = (c & 1) ? (c + 1) / 2 : -(c / 2); }
}

/* signed permutations */
static int NPERM;
static int perm[48][4], sgn[48][4];
static void init_perms(void) {
    int ps3[6][3] = {{1,2,3},{1,3,2},{2,1,3},{2,3,1},{3,1,2},{3,2,1}};
    NPERM = 0;
    if (RANK == 2) {
        int ps2[2][2] = {{1,2},{2,1}};
        for (int p = 0; p < 2; p++) for (int s = 0; s < 4; s++) {
            perm[NPERM][1] = ps2[p][0]; perm[NPERM][2] = ps2[p][1];
            sgn[NPERM][1] = (s & 1) ? -1 : 1; sgn[NPERM][2] = (s & 2) ? -1 : 1; NPERM++;
        }
        return;
    }
    for (int p = 0; p < 6; p++) for (int s = 0; s < 8; s++) {
        for (int g = 1; g <= 3; g++) { perm[NPERM][g] = ps3[p][g - 1]; sgn[NPERM][g] = (s >> (g - 1) & 1) ? -1 : 1; }
        NPERM++;
    }
}
static Key canon_pair(const Word *p0, const Word *q0) {
    Key best = {~0ULL, ~0ULL};
    Word bp, bq; int have = 0;
    for (int t = 0; t < NPERM; t++) {
        Word p = *p0, q = *q0;
        for (int i = 0; i < p.n; i++) { int g = abs(p.w[i]); p.w[i] = (p.w[i] > 0 ? 1 : -1) * sgn[t][g] * perm[t][g]; }
        for (int i = 0; i < q.n; i++) { int g = abs(q.w[i]); q.w[i] = (q.w[i] > 0 ? 1 : -1) * sgn[t][g] * perm[t][g]; }
        canon_cyc(&p); canon_cyc(&q);
        if (wcmp(&q, &p) < 0) { Word tmp = p; p = q; q = tmp; }
        int better = !have;
        if (have) { int c = wcmp(&p, &bp); better = c < 0 || (c == 0 && wcmp(&q, &bq) < 0); }
        if (better) { bp = p; bq = q; have = 1; }
    }
    best = pack(&bp, &bq);
    return best;
}

/* ---- Whitehead automorphisms of type 2 ---- */
typedef struct { signed char a; signed char opt[4]; } WA;
static WA was[200];
static int NWA;
static void init_was(void) {
    NWA = 0;
    for (int g = 1; g <= RANK; g++) for (int s = -1; s <= 1; s += 2) {
        int others[2], no = 0;
        for (int h = 1; h <= RANK; h++) if (h != g) others[no++] = h;
        int combos = (no == 2) ? 16 : 4;
        for (int c = 1; c < combos; c++) {
            WA t; memset(&t, 0, sizeof t); t.a = (signed char)(s * g);
            t.opt[others[0]] = c & 3;
            if (no == 2) t.opt[others[1]] = (c >> 2) & 3;
            was[NWA++] = t;
        }
    }
}
/* h -> h (0), h a (1), a^-1 h (2), a^-1 h a (3) */
static int apply_wa(const WA *t, const Word *u, Word *out) {
    int k = 0; signed char a = t->a;
    for (int i = 0; i < u->n; i++) {
        signed char c = u->w[i]; int g = abs(c);
        if (g == abs(a) || t->opt[g] == 0) { out->w[k++] = c; }
        else {
            int o = t->opt[g];
            if (c > 0) { if (o & 2) out->w[k++] = -a; out->w[k++] = c; if (o & 1) out->w[k++] = a; }
            else { if (o & 1) out->w[k++] = -a; out->w[k++] = c; if (o & 2) out->w[k++] = a; }
        }
        if (k > 190) return 0;
    }
    out->n = k; cycred(out); return 1;
}
static int is_primitive(const Word *w0) {
    Word w = *w0; cycred(&w);
    for (;;) {
        if (w.n == 1) return 1;
        if (w.n == 0) return 0;
        int red = 0; Word img;
        for (int t = 0; t < NWA; t++) {
            if (apply_wa(&was[t], &w, &img) && img.n < w.n) { w = img; red = 1; break; }
        }
        if (!red) return 0;
    }
}

/* ---- state store ---- */
static Key *states; static uint32_t *parent; static uint32_t *table; static uint64_t tmask;
static uint32_t nstates = 0, maxstates;
static uint64_t hkey(Key k) { uint64_t h = k.a * 0x9E3779B97F4A7C15ULL ^ (k.b + 0x632BE59BD9B4E019ULL) * 0xC2B2AE3D27D4EB4FULL; return h ^ (h >> 29); }
/* returns index (>=0) if newly inserted, -1 if present, -2 if full */
static long insert(Key k, uint32_t par) {
    uint64_t h = hkey(k) & tmask;
    while (table[h]) {
        Key *s = &states[table[h] - 1];
        if (s->a == k.a && s->b == k.b) return -1;
        h = (h + 1) & tmask;
    }
    if (nstates >= maxstates) return -2;
    states[nstates] = k; parent[nstates] = par; table[h] = nstates + 1;
    return nstates++;
}
static void wstr(const Word *u, char *s) {
    for (int i = 0; i < u->n; i++) s[i] = "zyx?XYZ"[u->w[i] + 3];
    s[u->n] = 0;
}
static void parse(const char *s, Word *u) {
    u->n = 0;
    for (; *s; s++) { const char *p = strchr("zyx?XYZ", *s); if (!p || *p == '?') { fprintf(stderr, "bad letter\n"); exit(2); } u->w[u->n++] = (signed char)(p - "zyx?XYZ" - 3); }
    cycred(u);
}
static void print_chain(uint32_t idx) {
    uint32_t chain[4096]; int len = 0;
    for (uint32_t i = idx;; i = parent[i]) { chain[len++] = i; if (i == 0 || len >= 4096) break; }
    printf("CHAIN %d\n", len);
    for (int k = len - 1; k >= 0; k--) {
        Word p, q; char s1[128], s2[128]; unpack(states[chain[k]], &p, &q); wstr(&p, s1); wstr(&q, s2);
        printf("  %s %s\n", s1, s2);
    }
}
#define CACHEMASK ((1ULL << 23) - 1)
static Key cache[1ULL << 23];
static long NODECAP = 5000000;
static unsigned long thick_calls = 0, thick_undec = 0, ngoal[4];
static int COUNT = 0, NOPRIM = 0, DUMP = 0;
static int thick_pair(const Word *p, const Word *q) {
    int lens[2] = {p->n, q->n}, letters[2 * MAXL + 4], k = 0;
    for (int i = 0; i < p->n; i++) letters[k++] = p->w[i];
    for (int i = 0; i < q->n; i++) letters[k++] = q->w[i];
    int r = thick2(2, lens, letters, NODECAP);
    thick_calls++;
    if (r == -2) thick_undec++;
    if (r == -1) { fprintf(stderr, "thick2: not cyclically reduced\n"); exit(5); }
    return r == 1;
}
/* 0 none, 1 PRIM, 2 THICK, 3 PROJ; *gproj = projected generator */
static int goal(const Word *p, const Word *q, int *gproj) {
    if (!NOPRIM && (is_primitive(p) || is_primitive(q))) return 1;
    if (thick_pair(p, q)) return 2;
    if (RANK == 3) {
        int e[2][4] = {{0}};
        const Word *rr[2] = {p, q};
        for (int i = 0; i < 2; i++) for (int m = 0; m < rr[i]->n; m++) e[i][abs(rr[i]->w[m])] += rr[i]->w[m] > 0 ? 1 : -1;
        for (int g = 1; g <= 3; g++) {
            int h = g == 1 ? 2 : 1, kk = g == 3 ? 2 : 3;
            int minor = e[0][h] * e[1][kk] - e[0][kk] * e[1][h];
            if (minor != 1 && minor != -1) continue;
            Word a, b; a.n = b.n = 0;
            for (int m = 0; m < p->n; m++) if (abs(p->w[m]) != g) a.w[a.n++] = p->w[m];
            for (int m = 0; m < q->n; m++) if (abs(q->w[m]) != g) b.w[b.n++] = q->w[m];
            cycred(&a); cycred(&b);
            if (a.n == 0 || b.n == 0) { fprintf(stderr, "empty projection: impossible for a Z-pair\n"); exit(6); }
            if (thick_pair(&a, &b)) { *gproj = g; return 3; }
        }
    }
    return 0;
}
static const char *GNAME[4] = {"NONE", "PRIM", "THICK", "PROJ"};

static long consider(Word *p, Word *q, uint32_t par) {
    if (p->n + q->n > CAP || p->n == 0 || q->n == 0) return -1;
    { /* lossy direct-mapped cache of rotation/inversion-canonical pairs (no generator symmetry) */
        Word a = *p, b = *q; canon_cyc(&a); canon_cyc(&b);
        if (wcmp(&b, &a) < 0) { Word t = a; a = b; b = t; }
        Key rk = pack(&a, &b); uint64_t h = hkey(rk) & CACHEMASK;
        if (cache[h].a == rk.a && cache[h].b == rk.b) return -1;
        cache[h] = rk;
    }
    Key k = canon_pair(p, q);
    long r = insert(k, par);
    if (r >= 0 && !DUMP) {
        int gp = 0, gl = goal(p, q, &gp);
        if (gl) {
            ngoal[gl]++;
            if (!COUNT || ngoal[gl] == 1) {
                char s1[128], s2[128]; wstr(p, s1); wstr(q, s2);
                printf("GOAL %s%s%c at state %ld (parent %u): %s %s\n", GNAME[gl], gl == 3 ? " g=" : "", gl == 3 ? "zyx?XYZ"[gp + 3] : ' ', r, par, s1, s2);
                print_chain((uint32_t)r); fflush(stdout);
            }
            if (!COUNT) { printf("thick calls %lu undecided %lu\n", thick_calls, thick_undec); exit(0); }
        }
    }
    if (r == -2) { printf("STATE LIMIT %u reached\n", maxstates); return -2; }
    return r;
}

/* check mode: test the goals on each stdin line "r1 r2" */
static int check_main(int argc, char **argv) {
    RANK = atoi(argv[2]);
    NOPRIM = argc > 3 && strstr(argv[3], "noprim") != NULL;
    init_perms(); init_was();
    char a[256], b[256]; unsigned long n = 0;
    while (scanf("%255s %255s", a, b) == 2) {
        Word p, q; parse(a, &p); parse(b, &q); n++;
        int gp = 0, gl = goal(&p, &q, &gp);
        if (gl) { ngoal[gl]++; printf("GOAL %s %s %s g=%d\n", GNAME[gl], a, b, gp); fflush(stdout); }
    }
    printf("CHECKED %lu pairs; goals PRIM %lu THICK %lu PROJ %lu; thick calls %lu undecided %lu\n", n, ngoal[1], ngoal[2], ngoal[3], thick_calls, thick_undec);
    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 3 && !strcmp(argv[1], "check")) return check_main(argc, argv);
    if (argc < 6) { fprintf(stderr, "usage: thzsearch RANK CAP MAXSTATES r1 r2 [count]\n"); return 2; }
    COUNT = argc > 6 && strstr(argv[6], "count") != NULL;
    NOPRIM = argc > 6 && strstr(argv[6], "noprim") != NULL;
    DUMP = argc > 6 && strstr(argv[6], "dump") != NULL;
    RANK = atoi(argv[1]); CAP = atoi(argv[2]); maxstates = (uint32_t)atol(argv[3]);
    if (CAP > MAXL) { fprintf(stderr, "CAP too large\n"); return 2; }
    init_perms(); init_was();
    uint64_t ts = 1; while (ts < 2ULL * maxstates) ts <<= 1; tmask = ts - 1;
    states = malloc(sizeof(Key) * maxstates); parent = malloc(4ULL * maxstates); table = calloc(ts, 4);
    if (!states || !parent || !table) { fprintf(stderr, "oom\n"); return 3; }
    Word p, q; parse(argv[4], &p); parse(argv[5], &q);
    printf("RANK %d CAP %d NPERM %d NWA %d\n", RANK, CAP, NPERM, NWA);
    Key k0 = canon_pair(&p, &q); insert(k0, 0);
    { int gp = 0, gl = goal(&p, &q, &gp); if (gl) { printf("GOAL %s at start\n", GNAME[gl]); print_chain(0); ngoal[gl]++; if (!COUNT) return 0; } }
    uint32_t head = 0, levelend = 1; int depth = 0; int full = 0;
    while (head < nstates) {
        if (head == levelend) { depth++; levelend = nstates; printf("depth %d states %u\n", depth, nstates); fflush(stdout); }
        Word r[2]; unpack(states[head], &r[0], &r[1]);
        /* M2: Whitehead automorphisms */
        for (int t = 0; t < NWA && !full; t++) {
            Word a, b;
            if (!apply_wa(&was[t], &r[0], &a) || !apply_wa(&was[t], &r[1], &b)) continue;
            if (consider(&a, &b, head) == -2) full = 1;
        }
        /* M1: AC products */
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
                        if (consider(&nw, &other, head) == -2) { full = 1; goto done; }
                    }
                }
            }
        }
    done:
        if (full) break;
        head++;
    }
    printf("%s depth %d states %u processed %u\n", full ? "INCOMPLETE" : "EXHAUSTED", depth, nstates, head);
    printf("goals PRIM %lu THICK %lu PROJ %lu; thick calls %lu undecided %lu\n", ngoal[1], ngoal[2], ngoal[3], thick_calls, thick_undec);
    if (DUMP) {
        FILE *f = fopen(getenv("THZ_DUMP") ? getenv("THZ_DUMP") : "states.txt", "w");
        for (uint32_t i = 0; i < nstates; i++) { Word p, q; char s1[128], s2[128]; unpack(states[i], &p, &q); wstr(&p, s1); wstr(&q, s2); fprintf(f, "%s %s\n", s1, s2); }
        fclose(f); printf("dumped %u states\n", nstates);
    }
    return full ? 1 : 0;
}
