/* tunnel.c -- Aut-tunnel closure test for a capped AC component.
 *
 * Input: a dump of a component S_CAP (lines "r1 r2", one state per line), as written by
 *   thzsearch RANK CAP MAX r1 r2 dump        (experiments/ak3-thick-z-pair-search-2026-09-17).
 * S_CAP is the connected component of the start pair in the graph whose vertices are relator
 * pairs of total length <= CAP and whose edges are the moves (M1) (AC products with rotations and
 * a one-letter conjugator) and (M2) (Whitehead automorphisms), up to signed permutations.
 *
 * A TUNNEL from s in S_CAP is: one move (M1) from s to a pair s' of total length > CAP (up to
 * |r_i| + 2|r_j| + 2, NO cap), followed by greedy Whitehead reduction of s' to a Whitehead-minimal
 * pair m.  (Automorphisms are free moves (P2), so s ~ m.)  For each tunnel we record:
 *   NEW    |m| <= CAP and m is not in S_CAP: the tunnel leaves the capped component (a new edge);
 *   PRIM   some entry of m has length 1, i.e. is primitive (certificate, rank 2 and 3);
 *   THICK  |m| <= TCAP and m (one Whitehead-minimal representative) is orientably thickenable;
 *   otherwise the histogram of |m|.
 * Also, as a sanity check of the input, every (M1) neighbour of length <= CAP must be in S_CAP
 * (count "closure violations"; must be 0).
 *
 * Whitehead reduction uses the exact cut formula |phi(w)| - |w| = cap(A) - deg(a) on the
 * Whitehead graph (verified against direct application: mode "selftest").
 * usage: tunnel RANK CAP TCAP dumpfile lo hi      (processes states lo..hi-1 of the dump)
 *        tunnel selftest RANK
 * Single-threaded. Build: gcc -O2 -I ../ak3-thick-z-pair-search-2026-09-17 -o tunnel tunnel.c
 */
#define main thz_main_unused
#include "thzsearch.c"
#undef main

static int li(signed char c) { return code(c) - 1; }           /* x0 X1 y2 Y3 z4 Z5 */
static int AMASK[200], AA[200];                                  /* WA t as (A bitmask, a index) */
static void init_amask(void) {
    for (int t = 0; t < NWA; t++) {
        int a = li(was[t].a), m = 1 << a;
        for (int g = 1; g <= RANK; g++) {
            if (g == abs(was[t].a)) continue;
            if (was[t].opt[g] & 1) m |= 1 << li((signed char)g);
            if (was[t].opt[g] & 2) m |= 1 << li((signed char)-g);
        }
        AMASK[t] = m; AA[t] = a;
    }
}
/* Whitehead graph counts E[u][v] of a cyclic word: edge {c_i, c_{i+1}^{-1}} */
static void wgraph(const Word *u, int E[6][6]) {
    int n = u->n;
    for (int i = 0; i < n; i++) {
        int p = li(u->w[i]), q = li(-u->w[(i + 1) % n]);
        E[p][q]++; E[q][p]++;
    }
}
static int delta(int E[6][6], int t) {
    int A = AMASK[t], a = AA[t], cap = 0, deg = 0;
    for (int u = 0; u < 2 * RANK; u++) {
        deg += E[a][u];
        if (!(A >> u & 1)) continue;
        for (int v = 0; v < 2 * RANK; v++) if (!(A >> v & 1)) cap += E[u][v];
    }
    return cap - deg; /* E[a][a] counted twice in deg is fine: a-a edges need |w|>=2 with aa^-1, impossible */
}
/* greedy Whitehead minimisation of the pair; returns number of steps, -1 on overflow */
static int wminimize(Word *p, Word *q) {
    int steps = 0;
    for (;;) {
        int E[6][6]; memset(E, 0, sizeof E);
        wgraph(p, E); wgraph(q, E);
        int best = 0, bt = -1;
        for (int t = 0; t < NWA; t++) { int d = delta(E, t); if (d < best) { best = d; bt = t; } }
        if (bt < 0) return steps;
        Word a, b;
        if (!apply_wa(&was[bt], p, &a) || !apply_wa(&was[bt], q, &b)) return -1;
        if (a.n + b.n != p->n + q->n + best) { fprintf(stderr, "cut formula mismatch\n"); exit(7); }
        *p = a; *q = b; steps++;
    }
}
/* planarity of the (simple) Whitehead graph on 2*RANK vertices: Kuratowski on <= 6 vertices */
static unsigned char nonplanar[1 << 15];
static int eidx[6][6];
static void init_planar(void) {
    int k = 0;
    for (int u = 0; u < 6; u++) for (int v = u + 1; v < 6; v++) { eidx[u][v] = eidx[v][u] = k++; }
    static int forb[4096]; int nf = 0;
    /* K5 on any 5 vertices */
    for (int out = 0; out < 6; out++) {
        int m = 0;
        for (int u = 0; u < 6; u++) for (int v = u + 1; v < 6; v++) if (u != out && v != out) m |= 1 << eidx[u][v];
        forb[nf++] = m;
        /* K5 with edge uv subdivided by 'out' */
        for (int u = 0; u < 6; u++) for (int v = u + 1; v < 6; v++) {
            if (u == out || v == out) continue;
            int m2 = (m & ~(1 << eidx[u][v])) | (1 << eidx[u][out]) | (1 << eidx[v][out]);
            forb[nf++] = m2;
        }
    }
    /* K33 on the 6 vertices */
    for (int s = 0; s < 64; s++) {
        if (__builtin_popcount(s) != 3 || !(s & 1)) continue;
        int m = 0;
        for (int u = 0; u < 6; u++) for (int v = 0; v < 6; v++) if ((s >> u & 1) && !(s >> v & 1)) m |= 1 << eidx[u][v];
        forb[nf++] = m;
    }
    for (int g = 0; g < (1 << 15); g++) {
        nonplanar[g] = 0;
        for (int f = 0; f < nf; f++) if ((g & forb[f]) == forb[f]) { nonplanar[g] = 1; break; }
    }
}
static int planar_pair(const Word *p, const Word *q) {
    int E[6][6]; memset(E, 0, sizeof E); wgraph(p, E); wgraph(q, E);
    int g = 0;
    for (int u = 0; u < 6; u++) for (int v = u + 1; v < 6; v++) if (E[u][v]) g |= 1 << eidx[u][v];
    return !nonplanar[g];
}

static int selftest(int rank) {
    RANK = rank; init_perms(); init_was(); init_amask();
    srand(12345); long bad = 0, tot = 0;
    for (int it = 0; it < 200000; it++) {
        Word w; w.n = 1 + rand() % 30;
        for (int i = 0; i < w.n; i++) { int g = 1 + rand() % RANK; w.w[i] = (signed char)((rand() & 1) ? g : -g); }
        cycred(&w); if (w.n == 0) continue;
        int E[6][6]; memset(E, 0, sizeof E); wgraph(&w, E);
        for (int t = 0; t < NWA; t++) {
            Word o; apply_wa(&was[t], &w, &o); tot++;
            if (o.n - w.n != delta(E, t)) bad++;
        }
    }
    init_planar(); int np = 0; for (int g = 0; g < (1 << 15); g++) np += nonplanar[g];
    printf("selftest rank %d: %ld WA applications, %ld cut-formula mismatches; %d nonplanar simple graphs on 6 labelled vertices\n", rank, tot, bad, np);
    return bad != 0;
}

#ifndef TUNNEL_NO_MAIN
int main(int argc, char **argv) {
    if (argc >= 3 && !strcmp(argv[1], "selftest")) return selftest(atoi(argv[2]));
    if (argc < 7) { fprintf(stderr, "usage: tunnel RANK CAP TCAP dump lo hi\n"); return 2; }
    RANK = atoi(argv[1]); CAP = atoi(argv[2]); int TCAP = atoi(argv[3]);
    long lo = atol(argv[5]), hi = atol(argv[6]);
    init_perms(); init_was(); init_amask(); init_planar();
    maxstates = 4000000; uint64_t ts = 1; while (ts < 2ULL * maxstates) ts <<= 1; tmask = ts - 1;
    states = malloc(sizeof(Key) * maxstates); parent = malloc(4ULL * maxstates); table = calloc(ts, 4);
    FILE *f = fopen(argv[4], "r"); if (!f) { perror("dump"); return 3; }
    char s1[256], s2[256];
    while (fscanf(f, "%255s %255s", s1, s2) == 2) { Word p, q; parse(s1, &p); parse(s2, &q); insert(canon_pair(&p, &q), 0); }
    fclose(f);
    if (hi > nstates) hi = nstates;
    printf("RANK %d CAP %d TCAP %d loaded %u states; processing %ld..%ld\n", RANK, CAP, TCAP, nstates, lo, hi);
    unsigned long moves = 0, inside = 0, viol = 0, tunnels = 0, newc = 0, prim = 0, thickc = 0, planar = 0, thick = 0, back = 0;
    unsigned long hist[128] = {0}, maxsteps = 0;
    for (long idx = lo; idx < hi; idx++) {
        Word r[2]; unpack(states[idx], &r[0], &r[1]);
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
                        int L = a.n + b.n;
                        if (L <= CAP) {
                            inside++;
                            Key kk = canon_pair(&a, &b);
                            uint64_t h = hkey(kk) & tmask; int found = 0;
                            while (table[h]) { Key *s = &states[table[h] - 1]; if (s->a == kk.a && s->b == kk.b) { found = 1; break; } h = (h + 1) & tmask; }
                            if (!found) viol++;
                            continue;
                        }
                        tunnels++;
                        int st = wminimize(&a, &b);
                        if (st < 0) { fprintf(stderr, "overflow\n"); continue; }
                        if ((unsigned long)st > maxsteps) maxsteps = st;
                        int Lm = a.n + b.n;
                        hist[Lm < 127 ? Lm : 127]++;
                        if (a.n == 1 || b.n == 1) {
                            prim++; char t1[256], t2[256]; wstr(&a, t1); wstr(&b, t2);
                            printf("PRIM from state %ld: %s %s\n", idx, t1, t2); fflush(stdout);
                        }
                        if (Lm <= CAP) {
                            back++;
                            Key kk = canon_pair(&a, &b);
                            uint64_t h = hkey(kk) & tmask; int found = 0;
                            while (table[h]) { Key *s = &states[table[h] - 1]; if (s->a == kk.a && s->b == kk.b) { found = 1; break; } h = (h + 1) & tmask; }
                            if (!found) {
                                newc++; char t1[256], t2[256], u1[256], u2[256]; wstr(&a, t1); wstr(&b, t2); wstr(&r[0], u1); wstr(&r[1], u2);
                                printf("NEW from state %ld (%s %s) move i=%d eps=%d g=%d ra=%d rb=%d -> %s %s\n", idx, u1, u2, i, eps, g, ra, rb, t1, t2); fflush(stdout);
                            }
                        } else if (Lm <= TCAP && Lm <= 2 * MAXL) {
                            thickc++;
                            if (planar_pair(&a, &b)) {
                                planar++;
                                if (thick_pair(&a, &b)) {
                                    thick++; char t1[256], t2[256]; wstr(&a, t1); wstr(&b, t2);
                                    printf("THICK from state %ld: %s %s\n", idx, t1, t2); fflush(stdout);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    printf("DONE states %ld..%ld moves %lu inside %lu closure-violations %lu tunnels %lu back<=CAP %lu NEW %lu PRIM %lu thick-tested(|m|<=TCAP) %lu planar %lu THICK %lu undecided %lu maxsteps %lu\n",
           lo, hi, moves, inside, viol, tunnels, back, newc, prim, thickc, planar, thick, thick_undec, maxsteps);
    printf("HIST |m|:");
    for (int l = 0; l < 128; l++) if (hist[l]) printf(" %d:%lu", l, hist[l]);
    printf("\n");
    return 0;
}
#endif
