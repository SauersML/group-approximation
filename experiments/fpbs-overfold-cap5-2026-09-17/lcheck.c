/* Exact test of (O-rel) and (O-step) of fpbs-mal-overfold-merges-never-help
 * (w17-follow decomposition) on the subsets of a given seed set.
 *
 * For a finite seed set P (pairs of vertices of Gamma_{j+1}(Q)):
 *   ell(P) = least number of lawful seeds whose fold-closure contains
 *            cl(P) \cap ker m, i.e. merges every pair u,v with m(u) = m(v)
 *            that cl(P) merges.
 *   (O-rel):  ell(P) <= |P|.
 *   (O-step): P nonempty  =>  some s in P has ell(P) <= ell(P - s) + 1.
 * ell is computed by an exhaustive breadth-first search over fold-closures
 * of lawful seeds (one per single-seed closure class, from the instance
 * file), with NO symmetry reduction, since the target is not invariant.
 *
 * Usage: ./lcheck inst.txt < pairs.txt      (pairs: "u v" per line, <= 16)
 * The shared part below is copied verbatim from deep5.c.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>

#define MAXV 256
static int V, n, S, NA;
static int nb[MAXV][4], mm[MAXV], firstm[MAXV];
static int su[4096], sv[4096], slaw[4096];
static int aut[64][MAXV], autinv[64][MAXV];
static int lawonly = 0;

typedef unsigned char lab_t;

typedef struct {
    int par[MAXV], sz[MAXV], adj[MAXV][4];
    int (*stk)[2];
} ws_t;

static int find(ws_t *w, int x) {
    while (w->par[x] != x) { w->par[x] = w->par[w->par[x]]; x = w->par[x]; }
    return x;
}

/* closure of the partition lab joined with the seed pairs (pu[i], pv[i]) */
static void closure_multi(ws_t *w, const lab_t *lab, int np, const int *pu,
                          const int *pv, lab_t *out) {
    int rep[MAXV];
    for (int i = 0; i < V; i++) rep[i] = -1;
    int top = 0;
    for (int v = 0; v < V; v++) {
        int l = lab[v];
        if (rep[l] < 0) {
            rep[l] = v; w->par[v] = v; w->sz[v] = 1;
            for (int k = 0; k < 4; k++) w->adj[v][k] = -1;
        } else { w->par[v] = rep[l]; w->sz[rep[l]]++; }
    }
    for (int v = 0; v < V; v++) {
        int r = w->par[v];
        for (int k = 0; k < 4; k++) if (nb[v][k] >= 0) {
            if (w->adj[r][k] < 0) w->adj[r][k] = nb[v][k];
            else { w->stk[top][0] = w->adj[r][k]; w->stk[top][1] = nb[v][k]; top++; }
        }
    }
    for (int i = 0; i < np; i++) { w->stk[top][0] = pu[i]; w->stk[top][1] = pv[i]; top++; }
    while (top > 0) {
        top--;
        int x = find(w, w->stk[top][0]), y = find(w, w->stk[top][1]);
        if (x == y) continue;
        if (w->sz[x] < w->sz[y]) { int t = x; x = y; y = t; }
        w->par[y] = x; w->sz[x] += w->sz[y];
        for (int k = 0; k < 4; k++) if (w->adj[y][k] >= 0) {
            if (w->adj[x][k] < 0) w->adj[x][k] = w->adj[y][k];
            else { w->stk[top][0] = w->adj[x][k]; w->stk[top][1] = w->adj[y][k]; top++; }
        }
    }
    int map[MAXV]; int c = 0;
    for (int i = 0; i < V; i++) map[i] = -1;
    for (int v = 0; v < V; v++) {
        int r = find(w, v);
        if (map[r] < 0) map[r] = c++;
        out[v] = (lab_t)map[r];
    }
}

static int goal(const lab_t *lab) {
    for (int v = 0; v < V; v++) if (lab[v] != lab[firstm[mm[v]]]) return 0;
    return 1;
}

/* canonical form modulo automorphisms; returns the automorphism used */
static int canon(const lab_t *lab, lab_t *best) {
    lab_t img[MAXV], cur[MAXV];
    int have = 0, ba = 0;
    for (int a = 0; a < NA; a++) {
        for (int v = 0; v < V; v++) img[aut[a][v]] = lab[v];
        int map[MAXV]; int c = 0;
        for (int i = 0; i < V; i++) map[i] = -1;
        for (int v = 0; v < V; v++) {
            if (map[img[v]] < 0) map[img[v]] = c++;
            cur[v] = (lab_t)map[img[v]];
        }
        if (!have || memcmp(cur, best, V) < 0) { memcpy(best, cur, V); have = 1; ba = a; }
    }
    return ba;
}

/* ---- hash set of states with provenance ---- */
typedef struct {
    lab_t *keys; uint8_t *used; int64_t *parent; int16_t *seed; int8_t *au;
    size_t cap, cnt;
} set_t;

static uint64_t hsh(const lab_t *k) {
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < V; i++) { h ^= k[i]; h *= 1099511628211ULL; }
    return h;
}
static void set_init(set_t *s, size_t cap) {
    s->cap = cap; s->cnt = 0;
    s->keys = malloc(cap * (size_t)V); s->used = calloc(cap, 1);
    s->parent = malloc(cap * sizeof(int64_t)); s->seed = malloc(cap * sizeof(int16_t));
    s->au = malloc(cap);
    if (!s->keys || !s->used || !s->parent || !s->seed || !s->au) { fprintf(stderr, "oom\n"); exit(1); }
}
static void set_free(set_t *s) { free(s->keys); free(s->used); free(s->parent); free(s->seed); free(s->au); }
static int set_add(set_t *s, const lab_t *k, int64_t parent, int seed, int au);
static void set_grow(set_t *s) {
    set_t t; set_init(&t, s->cap * 2);
    for (size_t i = 0; i < s->cap; i++) if (s->used[i])
        set_add(&t, s->keys + i * V, s->parent[i], s->seed[i], s->au[i]);
    set_free(s); *s = t;
}
static int set_add(set_t *s, const lab_t *k, int64_t parent, int seed, int au) {
    if (2 * (s->cnt + 1) > s->cap) set_grow(s);
    size_t i = hsh(k) & (s->cap - 1);
    while (s->used[i]) {
        if (!memcmp(s->keys + i * V, k, V)) return 0;
        i = (i + 1) & (s->cap - 1);
    }
    s->used[i] = 1; memcpy(s->keys + i * V, k, V); s->cnt++;
    s->parent[i] = parent; s->seed[i] = (int16_t)seed; s->au[i] = (int8_t)au;
    return 1;
}

/* levels kept for unwinding */
static set_t lev[16];

/* Unwind: state at level k, slot i, was canon = aut[au] applied to
 * closure(state(parent), seed).  With img[aut[a][v]] = lab[v], a vertex v of
 * the parent labelling corresponds to aut[a][v] in the stored labelling.
 * We carry a map g from stored-level-k vertices to original vertices. */
static void report(int k, size_t slot, int lastseed) {
    int g[MAXV];            /* g: vertex of level-k stored labelling -> original */
    for (int v = 0; v < V; v++) g[v] = v;
    int pu[64], pv[64], np = 0;
    /* last seed acts on stored level-k state directly */
    pu[np] = g[su[lastseed]]; pv[np] = g[sv[lastseed]]; np++;
    int kk = k; size_t sl = slot;
    while (kk > 0) {
        int a = lev[kk].au[sl], s = lev[kk].seed[sl];
        /* stored = aut_a(closure(parent, s)): parent vertex v <-> stored aut[a][v].
         * so stored vertex x corresponds to parent vertex autinv[a][x]. Compose. */
        int g2[MAXV];
        /* new g maps parent vertex -> original: original of stored aut[a][v] */
        for (int v = 0; v < V; v++) g2[v] = g[aut[a][v]];
        for (int v = 0; v < V; v++) g[v] = g2[v];
        pu[np] = g[su[s]]; pv[np] = g[sv[s]]; np++;
        sl = (size_t)lev[kk].parent[sl]; kk--;
    }
    printf("WITNESS %d seeds (original vertex pairs, lawful flag):\n", np);
    for (int i = 0; i < np; i++)
        printf("  %d %d %s\n", pu[i], pv[i], mm[pu[i]] == mm[pv[i]] ? "lawful" : "overfold");
    /* re-verify: discrete partition joined with all seeds */
    ws_t w; w.stk = malloc(sizeof(int[2]) * (1 << 16));
    lab_t id[MAXV], out[MAXV];
    for (int v = 0; v < V; v++) id[v] = (lab_t)v;
    closure_multi(&w, id, np, pu, pv, out);
    printf("RECHECK goal on literal seed set: %s\n", goal(out) ? "YES" : "NO");
    free(w.stk);
}

/* ---------------- lcheck-specific part ---------------- */
static int lu[4096], lv[4096], NL;   /* lawful seed representatives */
static int trep[MAXV];               /* target: v must share a block with trep[v] */

static int tgoal(const lab_t *lab) {
    for (int v = 0; v < V; v++) if (lab[v] != lab[trep[v]]) return 0;
    return 1;
}

/* exact ell for the current target, capped at cap (returns cap+1 if more) */
static int ell_search(ws_t *w, const lab_t *base, int cap) {
    if (tgoal(base)) return 0;
    set_t a, b; set_init(&a, 1024);
    set_add(&a, base, -1, -1, 0);
    lab_t out[MAXV];
    for (int k = 1; k <= cap; k++) {
        set_init(&b, 1024);
        for (size_t i = 0; i < a.cap; i++) if (a.used[i]) {
            const lab_t *st = a.keys + i * V;
            for (int s = 0; s < NL; s++) {
                closure_multi(w, st, 1, &lu[s], &lv[s], out);
                if (tgoal(out)) { set_free(&a); set_free(&b); return k; }
                if (k < cap) set_add(&b, out, -1, -1, 0);
            }
        }
        set_free(&a); a = b;
    }
    set_free(&a);
    return cap + 1;
}

/* ---------------- climb mode: adversarial search for ell(P) > |P| ----------
 * P = k overfold seed representatives.  Score = ell(P) (exact, cap k+3) and,
 * as a tie-break, the number of kernel merges V - #(fibre, block) classes of
 * cl(P).  Random single-seed replacements, accepted when the score does not
 * drop.  Prints the best ell(P) - |P| seen.  Usage: lcheck inst climb k iters rng
 */
static int ou[65536], ov[65536], NO;
static uint64_t rstate;
static uint64_t rnd(void) { rstate ^= rstate << 13; rstate ^= rstate >> 7; rstate ^= rstate << 17; return rstate; }

static int eval_set(ws_t *w, const lab_t *id, const lab_t *base, int k, const int *pick, int *kern) {
    int qu[64], qv[64];
    for (int i = 0; i < k; i++) { qu[i] = ou[pick[i]]; qv[i] = ov[pick[i]]; }
    lab_t clp[MAXV];
    closure_multi(w, id, k, qu, qv, clp);
    int cls = 0;
    for (int v = 0; v < V; v++) {
        trep[v] = v;
        for (int x = 0; x < V; x++) if (mm[x] == mm[v] && clp[x] == clp[v]) { trep[v] = x; break; }
        if (trep[v] == v) cls++;
    }
    *kern = V - cls;
    return ell_search(w, base, k + 3);
}

static int climb(int k, int iters, uint64_t seed) {
    rstate = seed * 0x9E3779B97F4A7C15ULL + 1;
    ws_t w; w.stk = malloc(sizeof(int[2]) * (1 << 16));
    lab_t id[MAXV], base[MAXV];
    for (int v = 0; v < V; v++) id[v] = (lab_t)v;
    closure_multi(&w, id, 0, NULL, NULL, base);
    int pick[64], kern, bestgap = -99;
    for (int i = 0; i < k; i++) pick[i] = (int)(rnd() % NO);
    int e = eval_set(&w, id, base, k, pick, &kern);
    long cur = (long)e * 100000 + kern;
    for (int it = 0; it < iters; it++) {
        int pos = (int)(rnd() % k), old = pick[pos];
        pick[pos] = (int)(rnd() % NO);
        int kk, ee = eval_set(&w, id, base, k, pick, &kk);
        long sc = (long)ee * 100000 + kk;
        if (sc >= cur) { cur = sc; e = ee; kern = kk; } else pick[pos] = old;
        if (e - k > bestgap) {
            bestgap = e - k;
            printf("  iter %d: ell %d |P| %d kernel merges %d; set:", it, e, k, kern);
            for (int i = 0; i < k; i++) printf(" %d-%d", ou[pick[i]], ov[pick[i]]);
            printf("\n"); fflush(stdout);
        }
    }
    printf("CLIMB k %d iters %d rng %llu: final ell %d kernel merges %d; best ell-|P| %d\n",
           k, iters, (unsigned long long)seed, e, kern, bestgap);
    return 0;
}

/* ---------------- pairs mode: exhaustive (O-rel) for |P| <= 2 -------------
 * Every single seed representative and every unordered pair of
 * representatives (lawful and overfold).  Histogram of ell by kind; any
 * ell(P) > |P| is printed.  Usage: lcheck inst pairs
 */
static int pairs_mode(void) {
    ws_t w; w.stk = malloc(sizeof(int[2]) * (1 << 16));
    lab_t id[MAXV], base[MAXV], clp[MAXV];
    for (int v = 0; v < V; v++) id[v] = (lab_t)v;
    closure_multi(&w, id, 0, NULL, NULL, base);
    int T = NL + NO;
    int *tu = malloc(T * sizeof(int)), *tv = malloc(T * sizeof(int));
    for (int i = 0; i < NL; i++) { tu[i] = lu[i]; tv[i] = lv[i]; }
    for (int i = 0; i < NO; i++) { tu[NL + i] = ou[i]; tv[NL + i] = ov[i]; }
    long hist[3][3][6]; memset(hist, 0, sizeof hist);   /* [#lawful][size][ell] */
    long viol = 0;
    for (int i = 0; i < T; i++) for (int j = i; j < T; j++) {
        int qu[2] = { tu[i], tu[j] }, qv[2] = { tv[i], tv[j] };
        int q = (i == j) ? 1 : 2;
        closure_multi(&w, id, q, qu, qv, clp);
        for (int v = 0; v < V; v++) {
            trep[v] = v;
            for (int x = 0; x < V; x++) if (mm[x] == mm[v] && clp[x] == clp[v]) { trep[v] = x; break; }
        }
        int e = ell_search(&w, base, 4);
        int nl = (i < NL) + (q == 2 && j < NL);
        hist[nl][q][e > 5 ? 5 : e]++;
        if (e > q) { viol++; printf("  O-REL VIOLATION %d-%d %d-%d ell %d\n", tu[i], tv[i], tu[j], tv[j], e); }
    }
    for (int q = 1; q <= 2; q++) for (int nl = 0; nl <= q; nl++) {
        printf("|P| %d, %d lawful: ell histogram", q, nl);
        for (int e = 0; e <= 5; e++) printf(" %d:%ld", e, hist[nl][q][e]);
        printf("\n");
    }
    printf("PAIRS lawful reps %d overfold reps %d; O-rel violations (|P|<=2) %ld\n", NL, NO, viol);
    return 0;
}

/* ---------------- triples mode: exhaustive over overfold triples -----------
 * All pairs of overfold representatives first (table L2), then every triple
 * {i, j, k} with i an orbit representative under the lifted automorphisms
 * (which preserve m, hence ell) and j < k arbitrary.  For each triple T:
 *   O-rel fails   iff ell(T) > 3;
 *   O-step fails  iff ell(T) > max over sub-pairs of ell + 1;
 *   O-pair fails  iff O-step fails and ell(T) > 0 + 2 (singletons have ell 0
 *                 by Lemma A, checked in pairs mode).
 * Usage: lcheck inst triples
 */
static int stampv[MAXV * MAXV], repv[MAXV * MAXV], gen;
static void set_trep(const lab_t *clp) {
    gen++;
    for (int v = 0; v < V; v++) {
        int key = mm[v] * V + clp[v];
        if (stampv[key] != gen) { stampv[key] = gen; repv[key] = v; }
        trep[v] = repv[key];
    }
}

static int triples_mode(void) {
    ws_t w; w.stk = malloc(sizeof(int[2]) * (1 << 16));
    lab_t id[MAXV], base[MAXV];
    for (int v = 0; v < V; v++) id[v] = (lab_t)v;
    closure_multi(&w, id, 0, NULL, NULL, base);
    /* single closures, canonical (closure_multi relabels by first occurrence) */
    lab_t *one = malloc((size_t)NO * V);
    for (int i = 0; i < NO; i++) closure_multi(&w, id, 1, &ou[i], &ov[i], one + (size_t)i * V);
    /* orbit representatives of the overfold classes */
    char *mark = calloc(NO, 1); int *orb = malloc(NO * sizeof(int)), norb = 0;
    for (int i = 0; i < NO; i++) if (!mark[i]) {
        orb[norb++] = i;
        for (int a = 0; a < NA; a++) {
            int u = aut[a][ou[i]], v = aut[a][ov[i]];
            lab_t c[MAXV]; closure_multi(&w, id, 1, &u, &v, c);
            for (int x = 0; x < NO; x++) if (!memcmp(c, one + (size_t)x * V, V)) { mark[x] = 1; break; }
        }
    }
    printf("TRIPLES overfold reps %d, orbit reps %d, automorphisms %d\n", NO, norb, NA);
    fflush(stdout);
    unsigned char *L2 = malloc((size_t)NO * NO);
    lab_t *pc = malloc((size_t)V);
    for (int i = 0; i < NO; i++) for (int j = i + 1; j < NO; j++) {
        int qu[2] = { ou[i], ou[j] }, qv[2] = { ov[i], ov[j] };
        closure_multi(&w, id, 2, qu, qv, pc);
        set_trep(pc);
        int e = ell_search(&w, base, 3);
        L2[(size_t)i * NO + j] = L2[(size_t)j * NO + i] = (unsigned char)e;
    }
    printf("pair table done\n"); fflush(stdout);
    long hist[6] = {0}, vrel = 0, vstep = 0, vpair = 0, cnt = 0;
    lab_t cij[MAXV], ct[MAXV];
    for (int oi = 0; oi < norb; oi++) {
        int i = orb[oi];
        for (int j = 0; j < NO; j++) if (j != i) {
            int qu[2] = { ou[i], ou[j] }, qv[2] = { ov[i], ov[j] };
            closure_multi(&w, id, 2, qu, qv, cij);
            for (int k = j + 1; k < NO; k++) if (k != i) {
                closure_multi(&w, cij, 1, &ou[k], &ov[k], ct);
                set_trep(ct);
                int e = ell_search(&w, base, 4);
                cnt++; hist[e > 5 ? 5 : e]++;
                int mp = L2[(size_t)i * NO + j];
                if (L2[(size_t)i * NO + k] > mp) mp = L2[(size_t)i * NO + k];
                if (L2[(size_t)j * NO + k] > mp) mp = L2[(size_t)j * NO + k];
                if (e > 3) { vrel++; printf("  O-REL VIOLATION %d-%d %d-%d %d-%d ell %d\n", ou[i], ov[i], ou[j], ov[j], ou[k], ov[k], e); }
                if (e > mp + 1) {
                    vstep++;
                    if (e > 2) { vpair++; printf("  O-PAIR VIOLATION %d-%d %d-%d %d-%d ell %d (pairs max %d)\n", ou[i], ov[i], ou[j], ov[j], ou[k], ov[k], e, mp); }
                }
            }
        }
        if (oi % 8 == 7) { printf("  orbit rep %d/%d done, triples %ld\n", oi + 1, norb, cnt); fflush(stdout); }
    }
    printf("triples (orbit-reduced on the first seed, each orbit class counted per ordered choice) %ld: ell histogram", cnt);
    for (int e = 0; e <= 5; e++) printf(" %d:%ld", e, hist[e]);
    printf("\nTRIPLES O-rel violations %ld; O-step violations %ld; O-pair violations %ld\n", vrel, vstep, vpair);
    return 0;
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d %d", &V, &n) != 2) return 1;
    for (int v = 0; v < V; v++) for (int k = 0; k < 4; k++) if (fscanf(f, "%d", &nb[v][k]) != 1) return 1;
    for (int v = 0; v < V; v++) if (fscanf(f, "%d", &mm[v]) != 1) return 1;
    int over; for (int v = 0; v < V; v++) if (fscanf(f, "%d", &over) != 1) return 1;
    if (fscanf(f, "%d", &S) != 1) return 1;
    NL = 0;
    for (int i = 0; i < S; i++) {
        int u, w, l;
        if (fscanf(f, "%d %d %d", &u, &w, &l) != 3) return 1;
        if (l) { lu[NL] = u; lv[NL] = w; NL++; }
        else { ou[NO] = u; ov[NO] = w; NO++; }
    }
    if (fscanf(f, "%d", &NA) != 1) NA = 0;
    for (int a = 0; a < NA; a++) for (int v = 0; v < V; v++) if (fscanf(f, "%d", &aut[a][v]) != 1) return 1;
    if (NA == 0) { NA = 1; for (int v = 0; v < V; v++) aut[0][v] = v; }
    fclose(f);
    if (argc > 2 && !strcmp(argv[2], "triples")) return triples_mode();
    if (argc > 5 && !strcmp(argv[2], "climb"))
        return climb(atoi(argv[3]), atoi(argv[4]), (uint64_t)atoll(argv[5]));
    if (argc > 2 && !strcmp(argv[2], "pairs")) return pairs_mode();
    int K = 0, pu[16], pv[16];
    while (K < 16 && scanf("%d %d", &pu[K], &pv[K]) == 2) K++;
    printf("LCHECK V %d n %d lawful seeds %d |P| %d\n", V, n, NL, K);
    for (int i = 0; i < K; i++)
        printf("  seed %d: %d %d %s\n", i, pu[i], pv[i], mm[pu[i]] == mm[pv[i]] ? "lawful" : "overfold");
    ws_t w; w.stk = malloc(sizeof(int[2]) * (1 << 16));
    lab_t id[MAXV], base[MAXV], clp[MAXV];
    for (int v = 0; v < V; v++) id[v] = (lab_t)v;
    closure_multi(&w, id, 0, NULL, NULL, base);
    int M = 1 << K;
    int *ell = malloc(M * sizeof(int));
    int viol_rel = 0, viol_step = 0, maxgap = -99;
    for (int mask = 0; mask < M; mask++) {
        int qu[16], qv[16], q = 0;
        for (int i = 0; i < K; i++) if (mask >> i & 1) { qu[q] = pu[i]; qv[q] = pv[i]; q++; }
        closure_multi(&w, id, q, qu, qv, clp);
        for (int v = 0; v < V; v++) {
            trep[v] = v;
            for (int x = 0; x < V; x++) if (mm[x] == mm[v] && clp[x] == clp[v]) { trep[v] = x; break; }
        }
        ell[mask] = ell_search(&w, base, K + 2);
        if (ell[mask] > q) {
            viol_rel++;
            printf("  O-REL VIOLATION mask %x |P| %d ell %d\n", mask, q, ell[mask]);
        }
        if (ell[mask] - q > maxgap) maxgap = ell[mask] - q;
    }
    for (int mask = 1; mask < M; mask++) {
        int ok = 0;
        for (int i = 0; i < K; i++) if (mask >> i & 1)
            if (ell[mask] <= ell[mask ^ (1 << i)] + 1) { ok = 1; break; }
        if (!ok) { viol_step++; printf("  O-STEP VIOLATION mask %x ell %d\n", mask, ell[mask]); }
    }
    /* (O-pair): some s with ell(P) <= ell(P-s)+1, or some pair {s,t} with
     * ell(P) <= ell(P-s-t)+2.  Also implies (O-rel) by induction on |P|.
     * jmax[a] = max over masks and a-subsets A of ell(P) - ell(P-A) - |A|. */
    int viol_pair = 0, jmax[17];
    for (int a = 0; a <= 16; a++) jmax[a] = -99;
    for (int mask = 1; mask < M; mask++) {
        int ok = 0;
        for (int i = 0; i < K && !ok; i++) if (mask >> i & 1) {
            if (ell[mask] <= ell[mask ^ (1 << i)] + 1) ok = 1;
            for (int j = i + 1; j < K && !ok; j++) if (mask >> j & 1)
                if (ell[mask] <= ell[mask ^ (1 << i) ^ (1 << j)] + 2) ok = 1;
        }
        if (!ok) { viol_pair++; printf("  O-PAIR VIOLATION mask %x ell %d\n", mask, ell[mask]); }
        for (int A = mask; A; A = (A - 1) & mask) {
            int a = __builtin_popcount(A);
            int g = ell[mask] - ell[mask ^ A] - a;
            if (g > jmax[a]) jmax[a] = g;
        }
    }
    printf("O-pair violations %d; max ell(P)-ell(P-A)-|A| by |A|:", viol_pair);
    for (int a = 1; a <= K; a++) printf(" %d:%d", a, jmax[a]);
    printf("\n");
    int allover = 0;
    for (int i = 0; i < K; i++) if (mm[pu[i]] != mm[pv[i]]) allover |= 1 << i;
    printf("ell(P) %d for |P| %d; ell(overfold part) %d for %d overfold seeds\n",
           ell[M - 1], K, ell[allover], __builtin_popcount(allover));
    printf("subsets %d; max ell(P)-|P| %d; O-rel violations %d; O-step violations %d\n",
           M, maxgap, viol_rel, viol_step);
    return 0;
}
