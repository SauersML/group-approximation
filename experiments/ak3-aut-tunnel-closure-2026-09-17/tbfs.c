/* tbfs.c -- breadth-first search of the TUNNEL-CLOSED component of a relator pair.
 *
 * Vertices: relator pairs of total length <= CAP (up to signed permutations, rotation,
 * inversion, swap), as in thzsearch.c.  Edges:
 *   (M2) Whitehead automorphisms whose image has length <= CAP;
 *   (M1) AC products r_i -> cyc.red.(U g V g^-1) (U a rotation of r_i, V of r_j^{+-1}, g empty
 *        or one letter) whose result has length <= CAP;
 *   (T)  TUNNELS: an (M1) product of ANY length (up to |r_i|+2|r_j|+2), followed by greedy
 *        Whitehead reduction to a Whitehead-minimal pair m, kept if |m| <= CAP.
 * All three are compositions of moves (P1) and (P2), so every vertex found is (P1)/(P2)-equivalent
 * to the start pair.
 * Goals tested on every new vertex (and, for PRIM, on every tunnel endpoint of any length):
 *   PRIM   an entry is primitive (for Whitehead-minimal endpoints: an entry of length 1);
 *   THICK  the pair is orientably thickenable (Neuwirth test thick2.c, after a Kuratowski
 *          planarity prefilter on the Whitehead graph, which is a necessary condition);
 *   PROJ   (rank 3) as in thzsearch.c.
 * Options (argv[6]): "count" do not stop at a goal; "notun" disable tunnels (reproduces thzsearch);
 *   "dump" write the component to $THZ_DUMP.
 * usage: tbfs RANK CAP MAXSTATES r1 r2 [opts]
 * Build: gcc -O2 -I ../ak3-thick-z-pair-search-2026-09-17 -o tbfs tbfs.c
 */
#define main thz_main_unused
#include "thzsearch.c"
#undef main

static int li(signed char c) { return code(c) - 1; }
static int AMASK[200], AA[200];
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
static void wgraph(const Word *u, int E[6][6]) {
    int n = u->n;
    for (int i = 0; i < n; i++) { int p = li(u->w[i]), q = li(-u->w[(i + 1) % n]); E[p][q]++; E[q][p]++; }
}
static int delta(int E[6][6], int t) {
    int A = AMASK[t], a = AA[t], cap = 0, deg = 0;
    for (int u = 0; u < 2 * RANK; u++) {
        deg += E[a][u];
        if (!(A >> u & 1)) continue;
        for (int v = 0; v < 2 * RANK; v++) if (!(A >> v & 1)) cap += E[u][v];
    }
    return cap - deg;
}
static int wminimize(Word *p, Word *q) {
    int steps = 0;
    for (;;) {
        int E[6][6]; memset(E, 0, sizeof E); wgraph(p, E); wgraph(q, E);
        int best = 0, bt = -1;
        for (int t = 0; t < NWA; t++) { int d = delta(E, t); if (d < best) { best = d; bt = t; } }
        if (bt < 0) return steps;
        Word a, b;
        if (!apply_wa(&was[bt], p, &a) || !apply_wa(&was[bt], q, &b)) return -1;
        if (a.n + b.n != p->n + q->n + best) { fprintf(stderr, "cut formula mismatch\n"); exit(7); }
        *p = a; *q = b; steps++;
    }
}
static unsigned char nonplanar[1 << 15];
static int eidx[6][6];
static void init_planar(void) {
    int k = 0;
    for (int u = 0; u < 6; u++) for (int v = u + 1; v < 6; v++) { eidx[u][v] = eidx[v][u] = k++; }
    static int forb[4096]; int nf = 0;
    for (int out = 0; out < 6; out++) {
        int m = 0;
        for (int u = 0; u < 6; u++) for (int v = u + 1; v < 6; v++) if (u != out && v != out) m |= 1 << eidx[u][v];
        forb[nf++] = m;
        for (int u = 0; u < 6; u++) for (int v = u + 1; v < 6; v++) {
            if (u == out || v == out) continue;
            forb[nf++] = (m & ~(1 << eidx[u][v])) | (1 << eidx[u][out]) | (1 << eidx[v][out]);
        }
    }
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
static unsigned long nplanar_rej = 0, ntunnel = 0, ntunnel_new = 0, nprim_tunnel = 0;
/* goal with planarity prefilter for THICK (necessary condition) */
static int goal2(const Word *p, const Word *q, int *gproj) {
    if (!NOPRIM && (is_primitive(p) || is_primitive(q))) return 1;
    if (planar_pair(p, q)) { if (thick_pair(p, q)) return 2; } else nplanar_rej++;
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
            if (a.n == 0 || b.n == 0) { fprintf(stderr, "empty projection\n"); exit(6); }
            if (planar_pair(&a, &b) && thick_pair(&a, &b)) { *gproj = g; return 3; }
        }
    }
    return 0;
}
static unsigned char *viatun;   /* 1 if the state was first reached through a tunnel */
static long consider2(Word *p, Word *q, uint32_t par, int tun) {
    if (p->n + q->n > CAP || p->n == 0 || q->n == 0) return -1;
    if (!tun) { /* lossy cache, as in thzsearch */
        Word a = *p, b = *q; canon_cyc(&a); canon_cyc(&b);
        if (wcmp(&b, &a) < 0) { Word t = a; a = b; b = t; }
        Key rk = pack(&a, &b); uint64_t h = hkey(rk) & CACHEMASK;
        if (cache[h].a == rk.a && cache[h].b == rk.b) return -1;
        cache[h] = rk;
    }
    Key k = canon_pair(p, q);
    long r = insert(k, par);
    if (r >= 0) {
        viatun[r] = (unsigned char)tun; if (tun) ntunnel_new++;
        if (!DUMP) {
            int gp = 0, gl = goal2(p, q, &gp);
            if (gl) {
                ngoal[gl]++;
                if (!COUNT || ngoal[gl] == 1) {
                    char s1[128], s2[128]; wstr(p, s1); wstr(q, s2);
                    printf("GOAL %s%s%c at state %ld (parent %u, via %s): %s %s\n", GNAME[gl], gl == 3 ? " g=" : "", gl == 3 ? "zyx?XYZ"[gp + 3] : ' ', r, par, tun ? "tunnel" : "move", s1, s2);
                    print_chain((uint32_t)r); fflush(stdout);
                }
                if (!COUNT) { printf("thick calls %lu undecided %lu\n", thick_calls, thick_undec); exit(0); }
            }
        }
    }
    if (r == -2) { printf("STATE LIMIT %u reached\n", maxstates); return -2; }
    return r;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: tbfs RANK CAP MAXSTATES r1 r2 [count|notun|dump]\n"); return 2; }
    const char *opt = argc > 6 ? argv[6] : "";
    COUNT = strstr(opt, "count") != NULL; DUMP = strstr(opt, "dump") != NULL;
    int NOTUN = strstr(opt, "notun") != NULL; NOPRIM = strstr(opt, "noprim") != NULL;
    RANK = atoi(argv[1]); CAP = atoi(argv[2]); maxstates = (uint32_t)atol(argv[3]);
    if (CAP > MAXL) { fprintf(stderr, "CAP too large\n"); return 2; }
    init_perms(); init_was(); init_amask(); init_planar();
    uint64_t ts = 1; while (ts < 2ULL * maxstates) ts <<= 1; tmask = ts - 1;
    states = malloc(sizeof(Key) * maxstates); parent = malloc(4ULL * maxstates); table = calloc(ts, 4);
    viatun = calloc(maxstates, 1);
    if (!states || !parent || !table || !viatun) { fprintf(stderr, "oom\n"); return 3; }
    Word p, q; parse(argv[4], &p); parse(argv[5], &q);
    printf("TBFS RANK %d CAP %d NPERM %d NWA %d tunnels %s\n", RANK, CAP, NPERM, NWA, NOTUN ? "off" : "on");
    Key k0 = canon_pair(&p, &q); insert(k0, 0);
    { int gp = 0, gl = goal2(&p, &q, &gp); if (gl) { printf("GOAL %s at start\n", GNAME[gl]); ngoal[gl]++; if (!COUNT) return 0; } }
    uint32_t head = 0, levelend = 1; int depth = 0, full = 0;
    while (head < nstates) {
        if (head == levelend) { depth++; levelend = nstates; printf("depth %d states %u (via tunnel %lu)\n", depth, nstates, ntunnel_new); fflush(stdout); }
        Word r[2]; unpack(states[head], &r[0], &r[1]);
        for (int t = 0; t < NWA && !full; t++) {
            Word a, b;
            if (!apply_wa(&was[t], &r[0], &a) || !apply_wa(&was[t], &r[1], &b)) continue;
            if (consider2(&a, &b, head, 0) == -2) full = 1;
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
                        if (nw.n == 0) continue;
                        Word other = r[j];
                        if (nw.n + other.n <= CAP) { if (consider2(&nw, &other, head, 0) == -2) { full = 1; goto done; } continue; }
                        if (NOTUN) continue;
                        ntunnel++;
                        Word a = nw, b = other;
                        if (wminimize(&a, &b) < 0) continue;
                        if (!NOPRIM && (a.n == 1 || b.n == 1)) {
                            nprim_tunnel++; char s1[256], s2[256]; wstr(&a, s1); wstr(&b, s2);
                            printf("GOAL PRIM (tunnel endpoint) from state %u: %s %s\n", head, s1, s2); print_chain(head); fflush(stdout);
                            if (!COUNT) exit(0);
                        }
                        if (consider2(&a, &b, head, 1) == -2) { full = 1; goto done; }
                    }
                }
            }
        }
    done:
        if (full) break;
        head++;
    }
    printf("%s depth %d states %u processed %u; via tunnel %lu; tunnels tried %lu\n", full ? "INCOMPLETE" : "EXHAUSTED", depth, nstates, head, ntunnel_new, ntunnel);
    printf("goals PRIM %lu THICK %lu PROJ %lu PRIM-tunnel-endpoints %lu; thick calls %lu undecided %lu; planar-prefilter rejections %lu\n",
           ngoal[1], ngoal[2], ngoal[3], nprim_tunnel, thick_calls, thick_undec, nplanar_rej);
    if (DUMP) {
        FILE *f = fopen(getenv("THZ_DUMP") ? getenv("THZ_DUMP") : "states.txt", "w");
        for (uint32_t i = 0; i < nstates; i++) { Word a, b; char s1[128], s2[128]; unpack(states[i], &a, &b); wstr(&a, s1); wstr(&b, s2); fprintf(f, "%s %s %u %d\n", s1, s2, parent[i], viatun[i]); }
        fclose(f); printf("dumped %u states\n", nstates);
    }
    return full ? 1 : 0;
}
