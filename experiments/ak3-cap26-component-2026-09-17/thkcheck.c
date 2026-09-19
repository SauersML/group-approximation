/* thkcheck.c -- THICK goal test on states lo..hi-1 of a dump (lines "r1 r2").
 *
 * For each state: the planarity prefilter of tunnel.c (the simple Whitehead graph of the pair
 * on 2*RANK vertices must be planar -- a necessary condition for orientable thickenability,
 * since a thickening embeds the link graph in the boundary sphere), then, on planar states
 * only, thick2 (the Neuwirth orientable-thickenability decision) via thzsearch's thick_pair.
 * Also re-tests PRIM.  Prints counts and every goal found.
 * usage: thkcheck RANK dump lo hi
 * Build: gcc -O2 -I. -o thkcheck thkcheck.c   (thzsearch.c, thick2.c, tunnel.c alongside)
 */
#define TUNNEL_NO_MAIN
#include "tunnel.c"

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: thkcheck RANK dump lo hi\n"); return 2; }
    RANK = atoi(argv[1]); CAP = MAXL; init_perms(); init_was(); init_amask(); init_planar();
    long lo = atol(argv[3]), hi = atol(argv[4]);
    FILE *f = fopen(argv[2], "r"); if (!f) { perror("dump"); return 2; }
    char a[256], b[256]; long idx = 0, n = 0, planar = 0, gthick = 0, gprim = 0;
    while (fscanf(f, "%255s %255s", a, b) == 2) {
        if (idx >= hi) break;
        if (idx++ < lo) continue;
        Word p, q; parse(a, &p); parse(b, &q); n++;
        if (is_primitive(&p) || is_primitive(&q)) { gprim++; printf("GOAL PRIM %ld: %s %s\n", idx - 1, a, b); }
        if (planar_pair(&p, &q)) {
            planar++;
            if (thick_pair(&p, &q)) { gthick++; printf("GOAL THICK %ld: %s %s\n", idx - 1, a, b); }
        }
    }
    printf("range %ld..%ld: states %ld planar %ld thick2 calls %lu undecided %lu goals THICK %ld PRIM %ld\n",
           lo, hi, n, planar, thick_calls, thick_undec, gthick, gprim);
    return 0;
}
