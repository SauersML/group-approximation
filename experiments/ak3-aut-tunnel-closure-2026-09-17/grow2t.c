/* grow2t.c -- closure under capped moves, tunnels and 2-tunnels (lane w6-082).
 *
 * usage: grow2t RANK CAP C2 base_dump seeds_file out_file
 *
 * Like grow.c, plus one more level. A 2-tunnel is:
 *   an (M1) product above CAP, Whitehead-reduced to a minimal pair m;
 *   if CAP < |m| <= C2, every (M1) product from m, Whitehead-reduced again;
 * and it lands if the result has length <= CAP.  Products from m that are already within CAP
 * land directly.  Endpoints with an entry of length 1 are reported as PRIM at either level.
 * Each 2-tunnel is a path of (M1) moves and automorphisms whose excursion above CAP holds two
 * AC products: exactly the paths the tunnel corollary leaves open.
 */
#define TUNNEL_NO_MAIN
#include "tunnel.c"

static unsigned long tprim = 0, ttun = 0, ttun2 = 0, tland2 = 0;
static int C2 = 0, full = 0;

static void m1_level(const Word *r, uint32_t head, int level) {
    for (int i = 0; i < 2 && !full; i++) {
        int j = 1 - i; Word U = r[i];
        for (int eps = -1; eps <= 1 && !full; eps += 2) {
            Word V = r[j];
            if (eps < 0) for (int m = 0; m < V.n; m++) V.w[m] = -r[j].w[V.n - 1 - m];
            for (int g = 0; g <= 2 * RANK && !full; g++) {
                signed char gl = 0;
                if (g > 0) gl = (signed char)((g + 1) / 2 * ((g & 1) ? 1 : -1));
                for (int ra = 0; ra < U.n && !full; ra++) for (int rb = 0; rb < V.n && !full; rb++) {
                    Word nw; int k = 0;
                    for (int m = 0; m < U.n; m++) nw.w[k++] = U.w[(ra + m) % U.n];
                    if (gl) nw.w[k++] = gl;
                    for (int m = 0; m < V.n; m++) nw.w[k++] = V.w[(rb + m) % V.n];
                    if (gl) nw.w[k++] = -gl;
                    nw.n = k; cycred(&nw);
                    if (nw.n == 0) continue;
                    Word a = nw, b = r[j];
                    if (a.n + b.n <= CAP) {
                        if (level == 1) tland2++;
                        if (consider(&a, &b, head) == -2) full = 1;
                        continue;
                    }
                    if (level == 0) ttun++; else ttun2++;
                    if (wminimize(&a, &b) < 0) { fprintf(stderr, "overflow\n"); continue; }
                    if (a.n == 1 || b.n == 1) {
                        tprim++; char t1[256], t2[256]; wstr(&a, t1); wstr(&b, t2);
                        printf("TUNNEL%s PRIM from state %u: %s %s\n", level ? "2" : "", head, t1, t2); fflush(stdout);
                    }
                    if (a.n + b.n <= CAP) {
                        if (level == 1) tland2++;
                        if (consider(&a, &b, head) == -2) full = 1;
                    } else if (level == 0 && a.n + b.n <= C2) {
                        Word rr[2] = {a, b};
                        m1_level(rr, head, 1);
                    }
                }
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: grow2t RANK CAP C2 base seeds out\n"); return 2; }
    RANK = atoi(argv[1]); CAP = atoi(argv[2]); C2 = atoi(argv[3]); COUNT = 1;
    if (C2 > 90) { fprintf(stderr, "C2 too large\n"); return 2; }
    init_perms(); init_was(); init_amask(); init_planar();
    maxstates = 6000000; uint64_t ts = 1; while (ts < 2ULL * maxstates) ts <<= 1; tmask = ts - 1;
    states = malloc(sizeof(Key) * maxstates); parent = malloc(4ULL * maxstates); table = calloc(ts, 4);
    if (!states || !parent || !table) { fprintf(stderr, "oom\n"); return 3; }
    char s1[256], s2[256];
    FILE *f = fopen(argv[4], "r"); if (!f) { perror("base"); return 3; }
    while (fscanf(f, "%255s %255s", s1, s2) == 2) { Word p, q; parse(s1, &p); parse(s2, &q); insert(canon_pair(&p, &q), 0); }
    fclose(f);
    uint32_t nbase = nstates;
    f = fopen(argv[5], "r"); if (!f) { perror("seeds"); return 3; }
    unsigned long nseed = 0;
    while (fscanf(f, "%255s %255s", s1, s2) == 2) {
        Word p, q; parse(s1, &p); parse(s2, &q); nseed++;
        if (p.n + q.n > CAP) { fprintf(stderr, "seed above cap\n"); return 4; }
        consider(&p, &q, 0);
    }
    fclose(f);
    printf("RANK %d CAP %d C2 %d base %u seeds %lu new after seeding %u\n", RANK, CAP, C2, nbase, nseed, nstates - nbase);
    fflush(stdout);
    uint32_t head = nbase;
    while (head < nstates && !full) {
        Word r[2]; unpack(states[head], &r[0], &r[1]);
        for (int t = 0; t < NWA && !full; t++) {
            Word a, b;
            if (!apply_wa(&was[t], &r[0], &a) || !apply_wa(&was[t], &r[1], &b)) continue;
            if (consider(&a, &b, head) == -2) full = 1;
        }
        m1_level(r, head, 0);
        head++;
        if ((head - nbase) % 200 == 0) { printf("processed %u, total new %u, 2-tunnels %lu\n", head - nbase, nstates - nbase, ttun2); fflush(stdout); }
    }
    printf("%s new states %u processed %u tunnels %lu 2-tunnels %lu level-2 landings %lu tunnel-PRIM %lu\n",
           full ? "INCOMPLETE" : "EXHAUSTED", nstates - nbase, head - nbase, ttun, ttun2, tland2, tprim);
    printf("goals PRIM %lu THICK %lu PROJ %lu; thick calls %lu undecided %lu\n", ngoal[1], ngoal[2], ngoal[3], thick_calls, thick_undec);
    f = fopen(argv[6], "w");
    for (uint32_t i = nbase; i < nstates; i++) { Word p, q; unpack(states[i], &p, &q); wstr(&p, s1); wstr(&q, s2); fprintf(f, "%s %s\n", s1, s2); }
    fclose(f);
    return full ? 1 : 0;
}
