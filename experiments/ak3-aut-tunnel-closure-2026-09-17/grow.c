/* grow.c -- tunnel closure of a known component, grown from seeds (lane w6-082).
 *
 * usage: grow RANK CAP base_dump seeds_file out_file
 *
 * Loads base_dump (states already known, e.g. the capped component S_CAP of AK(3), which
 * `tunnel` has checked is closed under capped (M1) and whose one-step tunnel endpoints are
 * the seeds).  Inserts the seeds and runs a BFS over NEW states only, with
 *   - capped (M2) Whitehead automorphisms and capped (M1) products, exactly as thzsearch.c;
 *   - tunnels: every (M1) product of length > CAP is Whitehead-reduced (wminimize, from
 *     tunnel.c); the endpoint is PRIM if an entry has length 1, and is inserted as a state if
 *     its length is <= CAP.
 * Every new state gets the goal test of thzsearch.c (PRIM, THICK, and PROJ in rank 3).
 * Ends EXHAUSTED when no new state remains: base + new states are then closed under capped
 * moves and tunnels.  Writes the new states to out_file.
 */
#define TUNNEL_NO_MAIN
#include "tunnel.c"

static unsigned long tprim = 0, ttun = 0;

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: grow RANK CAP base seeds out\n"); return 2; }
    RANK = atoi(argv[1]); CAP = atoi(argv[2]); COUNT = 1;
    init_perms(); init_was(); init_amask(); init_planar();
    maxstates = 6000000; uint64_t ts = 1; while (ts < 2ULL * maxstates) ts <<= 1; tmask = ts - 1;
    states = malloc(sizeof(Key) * maxstates); parent = malloc(4ULL * maxstates); table = calloc(ts, 4);
    if (!states || !parent || !table) { fprintf(stderr, "oom\n"); return 3; }
    char s1[256], s2[256];
    FILE *f = fopen(argv[3], "r"); if (!f) { perror("base"); return 3; }
    while (fscanf(f, "%255s %255s", s1, s2) == 2) { Word p, q; parse(s1, &p); parse(s2, &q); insert(canon_pair(&p, &q), 0); }
    fclose(f);
    uint32_t nbase = nstates;
    f = fopen(argv[4], "r"); if (!f) { perror("seeds"); return 3; }
    unsigned long nseed = 0, seedin = 0;
    while (fscanf(f, "%255s %255s", s1, s2) == 2) {
        Word p, q; parse(s1, &p); parse(s2, &q); nseed++;
        if (p.n + q.n > CAP) { fprintf(stderr, "seed above cap\n"); return 4; }
        if (consider(&p, &q, 0) < 0) seedin++;
    }
    fclose(f);
    printf("RANK %d CAP %d base %u seeds %lu (already known %lu) new after seeding %u\n", RANK, CAP, nbase, nseed, seedin, nstates - nbase);
    fflush(stdout);
    uint32_t head = nbase; int full = 0;
    while (head < nstates && !full) {
        Word r[2]; unpack(states[head], &r[0], &r[1]);
        for (int t = 0; t < NWA && !full; t++) {
            Word a, b;
            if (!apply_wa(&was[t], &r[0], &a) || !apply_wa(&was[t], &r[1], &b)) continue;
            if (consider(&a, &b, head) == -2) full = 1;
        }
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
                        if (a.n + b.n <= CAP) { if (consider(&a, &b, head) == -2) full = 1; continue; }
                        ttun++;
                        if (wminimize(&a, &b) < 0) { fprintf(stderr, "overflow\n"); continue; }
                        if (a.n == 1 || b.n == 1) {
                            tprim++; char t1[256], t2[256]; wstr(&a, t1); wstr(&b, t2);
                            printf("TUNNEL PRIM from state %u: %s %s\n", head, t1, t2); fflush(stdout);
                        }
                        if (a.n + b.n <= CAP && consider(&a, &b, head) == -2) full = 1;
                    }
                }
            }
        }
        head++;
        if ((head - nbase) % 20000 == 0) { printf("processed %u new states, total new %u\n", head - nbase, nstates - nbase); fflush(stdout); }
    }
    printf("%s new states %u processed %u tunnels %lu tunnel-PRIM %lu\n", full ? "INCOMPLETE" : "EXHAUSTED", nstates - nbase, head - nbase, ttun, tprim);
    printf("goals PRIM %lu THICK %lu PROJ %lu; thick calls %lu undecided %lu\n", ngoal[1], ngoal[2], ngoal[3], thick_calls, thick_undec);
    f = fopen(argv[5], "w");
    for (uint32_t i = nbase; i < nstates; i++) { Word p, q; unpack(states[i], &p, &q); wstr(&p, s1); wstr(&q, s2); fprintf(f, "%s %s\n", s1, s2); }
    fclose(f);
    return full ? 1 : 0;
}
