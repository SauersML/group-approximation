/* Exact deep_j / law_j by breadth-first search over fold-closed partitions,
 * reduced modulo the automorphisms of the L-set Q.
 *
 * Usage: ./deep inst.txt maxlevel [lawonly]
 * Reads the format written by export.py.  Level k holds the distinct
 * closures (up to automorphism) of k seeds.  The last level is not stored:
 * each state of level maxlevel-1 is extended by every seed and only tested.
 * Prints, per level, the number of states and whether some state contains
 * ker(m).  Exit status 0 always; the verdict is on stdout.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXV 256
static int V, n, S, NA;
static int nb[MAXV][4], mm[MAXV], firstm[MAXV];
static int su[4096], sv[4096], slaw[4096];
static int aut[64][MAXV];
static int lawonly = 0;

typedef unsigned char lab_t;

/* ---- closure ---- */
static int par[MAXV], sz[MAXV], adj[MAXV][4];
static int stk[1 << 16][2];

static int find(int x) {
    while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; }
    return x;
}

static void closure(const lab_t *lab, int s, lab_t *out) {
    int rep[MAXV];
    for (int i = 0; i < V; i++) rep[i] = -1;
    int top = 0;
    for (int v = 0; v < V; v++) {
        int l = lab[v];
        if (rep[l] < 0) {
            rep[l] = v; par[v] = v; sz[v] = 1;
            for (int k = 0; k < 4; k++) adj[v][k] = -1;
        } else { par[v] = rep[l]; sz[rep[l]]++; }
    }
    for (int v = 0; v < V; v++) {
        int r = par[v];
        for (int k = 0; k < 4; k++) if (nb[v][k] >= 0) {
            if (adj[r][k] < 0) adj[r][k] = nb[v][k];
            else { stk[top][0] = adj[r][k]; stk[top][1] = nb[v][k]; top++; }
        }
    }
    if (s >= 0) { stk[top][0] = su[s]; stk[top][1] = sv[s]; top++; }
    while (top > 0) {
        top--;
        int x = find(stk[top][0]), y = find(stk[top][1]);
        if (x == y) continue;
        if (sz[x] < sz[y]) { int t = x; x = y; y = t; }
        par[y] = x; sz[x] += sz[y];
        for (int k = 0; k < 4; k++) if (adj[y][k] >= 0) {
            if (adj[x][k] < 0) adj[x][k] = adj[y][k];
            else { stk[top][0] = adj[x][k]; stk[top][1] = adj[y][k]; top++; }
        }
    }
    int map[MAXV]; int c = 0;
    for (int i = 0; i < V; i++) map[i] = -1;
    for (int v = 0; v < V; v++) {
        int r = find(v);
        if (map[r] < 0) map[r] = c++;
        out[v] = (lab_t)map[r];
    }
}

static int goal(const lab_t *lab) {
    for (int v = 0; v < V; v++) if (lab[v] != lab[firstm[mm[v]]]) return 0;
    return 1;
}

/* canonical form modulo automorphisms */
static void canon(const lab_t *lab, lab_t *best) {
    lab_t img[MAXV], cur[MAXV];
    int have = 0;
    for (int a = 0; a < NA; a++) {
        for (int v = 0; v < V; v++) img[aut[a][v]] = lab[v];
        int map[MAXV]; int c = 0;
        for (int i = 0; i < V; i++) map[i] = -1;
        for (int v = 0; v < V; v++) {
            if (map[img[v]] < 0) map[img[v]] = c++;
            cur[v] = (lab_t)map[img[v]];
        }
        if (!have || memcmp(cur, best, V) < 0) { memcpy(best, cur, V); have = 1; }
    }
}

/* ---- hash set of states ---- */
typedef struct { lab_t *keys; uint8_t *used; size_t cap, cnt; } set_t;

static uint64_t hsh(const lab_t *k) {
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < V; i++) { h ^= k[i]; h *= 1099511628211ULL; }
    return h;
}
static void set_init(set_t *s, size_t cap) {
    s->cap = cap; s->cnt = 0;
    s->keys = malloc(cap * (size_t)V); s->used = calloc(cap, 1);
    if (!s->keys || !s->used) { fprintf(stderr, "oom\n"); exit(1); }
}
static void set_free(set_t *s) { free(s->keys); free(s->used); }
static int set_add(set_t *s, const lab_t *k);
static void set_grow(set_t *s) {
    set_t t; set_init(&t, s->cap * 2);
    for (size_t i = 0; i < s->cap; i++) if (s->used[i]) set_add(&t, s->keys + i * V);
    set_free(s); *s = t;
}
static int set_add(set_t *s, const lab_t *k) {
    if (2 * (s->cnt + 1) > s->cap) set_grow(s);
    size_t i = hsh(k) & (s->cap - 1);
    while (s->used[i]) {
        if (!memcmp(s->keys + i * V, k, V)) return 0;
        i = (i + 1) & (s->cap - 1);
    }
    s->used[i] = 1; memcpy(s->keys + i * V, k, V); s->cnt++;
    return 1;
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
    for (int i = 0; i < MAXV; i++) firstm[i] = -1;
    for (int v = 0; v < V; v++) if (firstm[mm[v]] < 0) firstm[mm[v]] = v;
    printf("V %d n %d seeds %d auts %d %s\n", V, n, S, NA, lawonly ? "LAWFUL ONLY" : "ALL SEEDS");

    lab_t id[MAXV], nxt[MAXV], cn[MAXV];
    for (int v = 0; v < V; v++) id[v] = (lab_t)v;
    closure(id, -1, nxt);
    if (goal(nxt)) { printf("level 0 goal\n"); return 0; }
    set_t cur; set_init(&cur, 1024);
    canon(nxt, cn); set_add(&cur, cn);
    for (int k = 1; k <= maxlevel; k++) {
        set_t nx; int store = (k < maxlevel);
        if (store) set_init(&nx, 1024);
        size_t tested = 0;
        for (size_t i = 0; i < cur.cap; i++) {
            if (!cur.used[i]) continue;
            const lab_t *st = cur.keys + i * V;
            for (int s = 0; s < S; s++) {
                closure(st, s, nxt);
                tested++;
                if (goal(nxt)) {
                    printf("level %d GOAL reached (seed %d on a stored state)\n", k, s);
                    fflush(stdout);
                    return 0;
                }
                if (store) { canon(nxt, cn); set_add(&nx, cn); }
            }
        }
        printf("level %d: no goal; %zu extensions tested; %zu new states stored\n",
               k, tested, store ? nx.cnt : (size_t)0);
        fflush(stdout);
        set_free(&cur);
        if (!store) break;
        cur = nx;
    }
    printf("no goal within %d seeds\n", maxlevel);
    return 0;
}
