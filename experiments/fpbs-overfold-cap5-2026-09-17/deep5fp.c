/* Parallel exact deep_j / law_j search, extending deep.c of
 * experiments/fpbs-overfold-exact-c-2026-09-17 (same input format, same
 * closure, same goal test, same canonical form modulo automorphisms).
 *
 * Usage: ./deep5 inst.txt maxlevel [law]
 *
 * Differences from deep.c:
 *  - closure uses a per-thread workspace, so levels are expanded with OpenMP;
 *  - every stored state records (parent slot, seed, automorphism index), so a
 *    goal can be unwound into a literal seed set on the original labelling;
 *  - on reaching the goal the literal seed set is printed and re-verified by
 *    applying all seeds at once to the discrete partition.
 * The last level is only tested, never stored.
 *
 * deep5fp.c (low-memory variant of deep5.c): the LAST STORED level
 * (maxlevel - 1) keeps only a 128-bit fingerprint of each canonical state
 * (two independent 64-bit hashes) plus its provenance (parent slot, seed,
 * automorphism).  When that level is expanded, each state is regenerated
 * exactly as closure(parent state, seed) followed by the same deterministic
 * canon(), so the expansion is identical to deep5.c's.  The only possible
 * deviation is a fingerprint collision between two distinct canonical states,
 * which would drop one of them; for N ~ 10^7 states its probability is about
 * N^2 / 2^129 < 10^-24.  Memory per last-level slot: 16 + 8 + 2 + 1 + 1 bytes
 * instead of V + 12.
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
    size_t cap, cnt; int kw;   /* key width: V (full) or 16 (fingerprint) */
} set_t;

static uint64_t hsh(const lab_t *k) {
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < V; i++) { h ^= k[i]; h *= 1099511628211ULL; }
    return h;
}
static uint64_t hsh2(const lab_t *k) {   /* independent second hash */
    uint64_t h = 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < V; i++) {
        h ^= (uint64_t)k[i] + 0x632BE59BD9B4E019ULL + (h << 6) + (h >> 2);
        h *= 0xBF58476D1CE4E5B9ULL; h ^= h >> 31;
    }
    return h;
}
/* 16-byte fingerprint key; its first 8 bytes are hsh(), used for the index */
static void fprint(const lab_t *k, lab_t *out) {
    uint64_t a = hsh(k), b = hsh2(k);
    memcpy(out, &a, 8); memcpy(out + 8, &b, 8);
}
static int newkw = 0;      /* key width for the next set_init */
static void set_init(set_t *s, size_t cap) {
    s->cap = cap; s->cnt = 0; s->kw = newkw ? newkw : V;
    s->keys = malloc(cap * (size_t)s->kw); s->used = calloc(cap, 1);
    s->parent = malloc(cap * sizeof(int64_t)); s->seed = malloc(cap * sizeof(int16_t));
    s->au = malloc(cap);
    if (!s->keys || !s->used || !s->parent || !s->seed || !s->au) { fprintf(stderr, "oom\n"); exit(1); }
}
static void set_free(set_t *s) { free(s->keys); free(s->used); free(s->parent); free(s->seed); free(s->au); }
static int set_add(set_t *s, const lab_t *k, int64_t parent, int seed, int au);
static void set_grow(set_t *s) {
    int save = newkw; newkw = s->kw;
    set_t t; set_init(&t, s->cap * 2);
    newkw = save;
    for (size_t i = 0; i < s->cap; i++) if (s->used[i])
        set_add(&t, s->keys + i * s->kw, s->parent[i], s->seed[i], s->au[i]);
    set_free(s); *s = t;
}
static int set_add(set_t *s, const lab_t *k, int64_t parent, int seed, int au) {
    /* load factor 3/4 (was 1/2): halves the peak memory of the level-4 set on
     * the V = 192 instances (the first inst24a cap-5 run was OOM-killed on a
     * shared machine at 87% of level 5) */
    if (4 * (s->cnt + 1) > 3 * s->cap) set_grow(s);
    /* k is already a kw-byte key (full state or fingerprint) */
    uint64_t h;
    if (s->kw == 16) memcpy(&h, k, 8); else h = hsh(k);
    size_t i = h & (s->cap - 1);
    while (s->used[i]) {
        if (!memcmp(s->keys + i * s->kw, k, s->kw)) return 0;
        i = (i + 1) & (s->cap - 1);
    }
    s->used[i] = 1; memcpy(s->keys + i * s->kw, k, s->kw); s->cnt++;
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

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    int maxlevel = atoi(argv[2]);
    if (argc > 3) lawonly = 1;
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
    printf("V %d n %d seeds %d auts %d threads %d %s\n", V, n, S, NA,
           omp_get_max_threads(), lawonly ? "LAWFUL ONLY" : "ALL SEEDS");
    fflush(stdout);

    ws_t w0; w0.stk = malloc(sizeof(int[2]) * (1 << 16));
    lab_t id[MAXV], nxt[MAXV], cn[MAXV];
    for (int v = 0; v < V; v++) id[v] = (lab_t)v;
    closure_multi(&w0, id, 0, NULL, NULL, nxt);
    if (goal(nxt)) { printf("level 0 goal\n"); return 0; }
    set_init(&lev[0], 1024);
    int a0 = canon(nxt, cn); set_add(&lev[0], cn, -1, -1, a0);

    for (int k = 1; k <= maxlevel; k++) {
        set_t *cur = &lev[k - 1];
        int store = (k < maxlevel);
        int fpl = (k == maxlevel - 1 && k >= 1);   /* fingerprint-only level */
        newkw = fpl ? 16 : 0;
        if (store) set_init(&lev[k], 1024);
        newkw = 0;
        int regen = (cur->kw == 16);                /* cur holds fingerprints */
        int kw = fpl ? 16 : V;
        /* collect occupied slots */
        size_t ns = 0;
        size_t *slots = malloc(cur->cnt * sizeof(size_t));
        for (size_t i = 0; i < cur->cap; i++) if (cur->used[i]) slots[ns++] = i;
        volatile int found = 0;
        size_t fslot = 0; int fseed = -1;
        size_t tested = 0;
        const size_t CH = 4096;
        for (size_t c0 = 0; c0 < ns && !found; c0 += CH) {
            size_t c1 = c0 + CH < ns ? c0 + CH : ns;
            size_t m = (c1 - c0) * (size_t)S;
            lab_t *buf = store ? malloc(m * (size_t)kw) : NULL;
            int8_t *bau = store ? malloc(m) : NULL;
            #pragma omp parallel
            {
                ws_t w; w.stk = malloc(sizeof(int[2]) * (1 << 16));
                lab_t out[MAXV], cfull[MAXV], tmp[MAXV];
                #pragma omp for schedule(dynamic, 16) reduction(+:tested)
                for (size_t t = c0; t < c1; t++) {
                    if (found) continue;
                    const lab_t *st;
                    lab_t stbuf[MAXV];
                    if (regen) {
                        /* regenerate the canonical state exactly as it was made */
                        const set_t *pr = &lev[k - 2];
                        int ps = cur->seed[slots[t]];
                        closure_multi(&w, pr->keys + (size_t)cur->parent[slots[t]] * V,
                                      1, &su[ps], &sv[ps], tmp);
                        canon(tmp, stbuf);
                        st = stbuf;
                    } else st = cur->keys + slots[t] * V;
                    for (int s = 0; s < S; s++) {
                        closure_multi(&w, st, 1, &su[s], &sv[s], out);
                        tested++;
                        if (goal(out)) {
                            #pragma omp critical
                            { if (!found) { found = 1; fslot = slots[t]; fseed = s; } }
                        }
                        if (store) {
                            size_t idx = (t - c0) * (size_t)S + s;
                            if (fpl) {
                                bau[idx] = (int8_t)canon(out, cfull);
                                fprint(cfull, buf + idx * 16);
                            } else
                                bau[idx] = (int8_t)canon(out, buf + idx * V);
                        }
                    }
                }
                free(w.stk);
            }
            if (store && !found) {
                for (size_t t = c0; t < c1; t++) for (int s = 0; s < S; s++) {
                    size_t idx = (t - c0) * (size_t)S + s;
                    set_add(&lev[k], buf + idx * kw, (int64_t)slots[t], s, bau[idx]);
                }
            }
            free(buf); free(bau);
            if (k == maxlevel && (c0 / CH) % 64 == 0) {
                printf("  level %d progress %zu/%zu states\n", k, c1, ns); fflush(stdout);
            }
        }
        free(slots);
        if (found) {
            printf("level %d GOAL reached\n", k);
            report(k - 1, fslot, fseed);
            fflush(stdout);
            return 0;
        }
        printf("level %d: no goal; %zu extensions tested; %zu new states stored\n",
               k, tested, store ? lev[k].cnt : (size_t)0);
        fflush(stdout);
        if (!store) break;
    }
    printf("no goal within %d seeds\n", maxlevel);
    return 0;
}
