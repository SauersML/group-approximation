/* Beam search for SHORT witnesses of deep_j (a heuristic upper-bound search,
 * NOT exhaustive).  Same instance format, closure, goal test and canonical
 * form as deep5.c (the shared part below is copied verbatim from deep5.c).
 *
 * Usage: ./beam inst.txt maxlevel beamwidth rngseed [law|force]
 *   law   : lawful seeds only;
 *   force : level 1 uses overfold seeds only (every witness found then
 *           contains an overfold seed), later levels use all seeds.
 *
 * Level k keeps at most B distinct canonical states, chosen among all
 * one-seed extensions of level k-1 by smallest kernel defect
 *     defect(lab) = sum over m-fibres F of (#blocks meeting F - 1),
 * which is 0 exactly at the goal; ties are broken by a seeded random key.
 * A goal is unwound to a literal seed set and re-verified from scratch, so
 * any reported witness with fewer than law seeds is a certified
 * counterexample to deep_j = law_j, independent of the heuristic.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>

#ifdef WIDE
#define MAXV 512
#else
#define MAXV 256
#endif
static int V, n, S, NA;
static int nb[MAXV][4], mm[MAXV], firstm[MAXV];
static int su[4096], sv[4096], slaw[4096];
static int aut[64][MAXV], autinv[64][MAXV];
static int lawonly = 0, force = 0;

#ifdef WIDE
typedef uint16_t lab_t;
#else
typedef unsigned char lab_t;
#endif

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
        if (!have || memcmp(cur, best, V * sizeof(lab_t)) < 0) { memcpy(best, cur, V * sizeof(lab_t)); have = 1; ba = a; }
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
    s->keys = malloc(cap * (size_t)V * sizeof(lab_t)); s->used = calloc(cap, 1);
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
        if (!memcmp(s->keys + i * V, k, V * sizeof(lab_t))) return 0;
        i = (i + 1) & (s->cap - 1);
    }
    s->used[i] = 1; memcpy(s->keys + i * V, k, V * sizeof(lab_t)); s->cnt++;
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

/* ---------------- beam-specific part ---------------- */
static int nfib, fibstart[MAXV + 1], fibv[MAXV];

static int defect(const lab_t *lab) {
    int stamp[MAXV]; for (int i = 0; i < V; i++) stamp[i] = -1;
    int d = 0;
    for (int f = 0; f < nfib; f++) {
        int c = 0;
        for (int i = fibstart[f]; i < fibstart[f + 1]; i++) {
            int l = lab[fibv[i]];
            if (stamp[l] != f) { stamp[l] = f; c++; }
        }
        if (c > 0) d += c - 1;
    }
    return d;
}

static uint64_t mix(uint64_t x) {
    x += 0x9E3779B97F4A7C15ULL;
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
    return x ^ (x >> 31);
}

static int cmpu64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? -1 : x > y;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: beam inst maxlevel B rngseed [law|force]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    int maxlevel = atoi(argv[2]);
    size_t B = (size_t)atol(argv[3]);
    uint64_t rs = (uint64_t)atol(argv[4]);
    if (argc > 5 && !strcmp(argv[5], "law")) lawonly = 1;
    if (argc > 5 && !strcmp(argv[5], "force")) force = 1;
    if (maxlevel > 15) maxlevel = 15;
    if (fscanf(f, "%d %d", &V, &n) != 2) return 1;
    for (int v = 0; v < V; v++) for (int k = 0; k < 4; k++) if (fscanf(f, "%d", &nb[v][k]) != 1) return 1;
    for (int v = 0; v < V; v++) if (fscanf(f, "%d", &mm[v]) != 1) return 1;
    int over; for (int v = 0; v < V; v++) if (fscanf(f, "%d", &over) != 1) return 1;
    if (fscanf(f, "%d", &S) != 1) return 1;
    int T = 0;
    for (int i = 0; i < S; i++) {
        int u, w, l;
        if (fscanf(f, "%d %d %d", &u, &w, &l) != 3) return 1;
        if (lawonly && !l) continue;
        su[T] = u; sv[T] = w; slaw[T] = l; T++;
    }
    S = T;
    if (fscanf(f, "%d", &NA) != 1) NA = 0;
    for (int a = 0; a < NA; a++) for (int v = 0; v < V; v++) if (fscanf(f, "%d", &aut[a][v]) != 1) return 1;
    if (NA == 0) { NA = 1; for (int v = 0; v < V; v++) aut[0][v] = v; }
    for (int a = 0; a < NA; a++) for (int v = 0; v < V; v++) autinv[a][aut[a][v]] = v;
    for (int i = 0; i < MAXV; i++) firstm[i] = -1;
    for (int v = 0; v < V; v++) if (firstm[mm[v]] < 0) firstm[mm[v]] = v;
    /* fibre lists */
    int maxm = 0; for (int v = 0; v < V; v++) if (mm[v] > maxm) maxm = mm[v];
    nfib = maxm + 1; int pos = 0;
    for (int fb = 0; fb < nfib; fb++) {
        fibstart[fb] = pos;
        for (int v = 0; v < V; v++) if (mm[v] == fb) fibv[pos++] = v;
    }
    fibstart[nfib] = pos;
    printf("BEAM V %d n %d seeds %d auts %d B %zu rng %llu %s\n", V, n, S, NA, B,
           (unsigned long long)rs, lawonly ? "LAWFUL ONLY" : force ? "ALL SEEDS, LEVEL 1 OVERFOLD ONLY" : "ALL SEEDS");
    fflush(stdout);

    ws_t w0; w0.stk = malloc(sizeof(int[2]) * (1 << 16));
    lab_t id[MAXV], nxt[MAXV], cn[MAXV];
    for (int v = 0; v < V; v++) id[v] = (lab_t)v;
    closure_multi(&w0, id, 0, NULL, NULL, nxt);
    if (goal(nxt)) { printf("level 0 goal\n"); return 0; }
    set_init(&lev[0], 1024);
    int a0 = canon(nxt, cn); set_add(&lev[0], cn, -1, -1, a0);
    printf("level 0 defect %d\n", defect(nxt));

    for (int k = 1; k <= maxlevel; k++) {
        set_t *cur = &lev[k - 1];
        size_t ns = 0;
        size_t *slots = malloc(cur->cnt * sizeof(size_t));
        for (size_t i = 0; i < cur->cap; i++) if (cur->used[i]) slots[ns++] = i;
        size_t m = ns * (size_t)S;
        uint16_t *D = malloc(m * sizeof(uint16_t));
        volatile int found = 0; size_t fslot = 0; int fseed = -1;
        #pragma omp parallel
        {
            ws_t w; w.stk = malloc(sizeof(int[2]) * (1 << 16));
            lab_t out[MAXV];
            #pragma omp for schedule(dynamic, 16)
            for (size_t t = 0; t < ns; t++) {
                const lab_t *st = cur->keys + slots[t] * V;
                for (int s = 0; s < S; s++) {
                    closure_multi(&w, st, 1, &su[s], &sv[s], out);
                    int d = defect(out);
                    if (force && k == 1 && slaw[s]) d = MAXV * 4; /* excluded */
                    D[t * (size_t)S + s] = (uint16_t)d;
                    if (d == 0) {
                        #pragma omp critical
                        { if (!found) { found = 1; fslot = slots[t]; fseed = s; } }
                    }
                }
            }
            free(w.stk);
        }
        if (found) {
            printf("level %d GOAL reached (beam)\n", k);
            report(k - 1, fslot, fseed);
            fflush(stdout);
            return 0;
        }
        /* threshold: smallest Tt with #{D <= Tt} >= 4B */
        size_t hist[MAXV * 4 + 1]; memset(hist, 0, sizeof hist);
        for (size_t i = 0; i < m; i++) hist[D[i]]++;
        int dmin = 0; while (hist[dmin] == 0) dmin++;
        int Tt = dmin; size_t cum = hist[dmin];
        while (cum < 4 * B && Tt < MAXV * 4) { Tt++; cum += hist[Tt]; }
        Tt = MAXV * 4 - 1; /* keep going past the threshold until B distinct states;
                              MAXV*4 marks excluded candidates */
        /* selection: iterate defect values in increasing order; within one
         * defect value visit candidates in the order of a seeded random key;
         * keep the first B distinct canonical states */
        set_init(&lev[k], 1024);
        int dbest = -1, dlast = -1;
        for (int dv = dmin; dv <= Tt && lev[k].cnt < B; dv++) {
            if (hist[dv] == 0) continue;
            size_t cnt = 0;
            for (size_t i = 0; i < m; i++) if (D[i] == dv) cnt++;
            uint64_t *kk = malloc(cnt * sizeof(uint64_t) * 2);
            size_t c = 0;
            for (size_t i = 0; i < m; i++) if (D[i] == dv) {
                kk[2 * c] = mix(i ^ (rs * 0x100000001B3ULL) ^ ((uint64_t)k << 56));
                kk[2 * c + 1] = i; c++;
            }
            /* sort pairs by first word */
            qsort(kk, cnt, 2 * sizeof(uint64_t), cmpu64);
            for (size_t q = 0; q < cnt && lev[k].cnt < B; q++) {
                size_t i = (size_t)kk[2 * q + 1];
                size_t t = i / S; int s = (int)(i % S);
                lab_t out[MAXV], cc[MAXV];
                closure_multi(&w0, cur->keys + slots[t] * V, 1, &su[s], &sv[s], out);
                int au = canon(out, cc);
                if (set_add(&lev[k], cc, (int64_t)slots[t], s, au)) { if (dbest < 0) dbest = dv; dlast = dv; }
            }
            free(kk);
        }
        printf("level %d: %zu extensions; min defect %d; kept %zu states (defect %d..%d)\n",
               k, m, dmin, lev[k].cnt, dbest, dlast);
        fflush(stdout);
        free(D); free(slots);
    }
    printf("no goal within %d seeds (beam, not exhaustive)\n", maxlevel);
    return 0;
}
