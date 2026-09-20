/* Exact test of the relative form of (O) on one level:
 *   for every set P of s <= smax overfold seeds,
 *   lawneed(cl(P)) >= law - s,
 * where lawneed(X) is the least number of lawful seeds whose closure together
 * with X contains ker(m).  A violation is a set of |P| + lawneed < law seeds
 * reaching the goal, i.e. an exact certified counterexample deep_j < law_j.
 *
 * Usage: ./rel inst.txt smax [maxP] [exact|fast] [part nparts]
 * (part/nparts: only the P[0] indices r with r % nparts == part, for
 *  splitting one level over several processes.)
 * (maxP <= 0: no cap.  'exact': search lawneed one step further, so that
 *  saving 0 (P exactly as efficient as |P| lawful seeds) is resolved.)
 * Input: the format of ../fpbs-overfold-exact-c-2026-09-17/export.py.
 * Output: law, and for each s the number of P tested and the histogram of
 * saving(P) = law - |P| - lawneed(cl(P))  (always <= 0 iff no violation;
 * lawneed is only searched up to law - |P| - 1, so savings < 0 are lumped).
 * The first element of P runs over one representative per automorphism
 * orbit of single-seed closures; the others over all overfold seeds (over
 * the later ones when the automorphism group is trivial).
 * Without 'exact' the histogram bin 0 means saving <= 0 (no violation).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXV 1024
typedef uint16_t lab_t;
static int V, n, S, NA;
static int nb[MAXV][4], mm[MAXV], firstm[MAXV];
static int su[8192], sv[8192], slaw[8192];
static int (*aut)[MAXV];
static int par[MAXV], sz[MAXV], adj[MAXV][4];
static int stk[1 << 18][2];

static int find(int x) {
    while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; }
    return x;
}

/* closure of state lab plus seeds list[0..k-1] */
static void closure(const lab_t *lab, const int *list, int k, lab_t *out) {
    static int rep[MAXV];
    for (int i = 0; i < V; i++) rep[i] = -1;
    int top = 0;
    for (int v = 0; v < V; v++) {
        int l = lab[v];
        if (rep[l] < 0) {
            rep[l] = v; par[v] = v; sz[v] = 1;
            for (int d = 0; d < 4; d++) adj[v][d] = -1;
        } else { par[v] = rep[l]; sz[rep[l]]++; }
    }
    for (int v = 0; v < V; v++) {
        int r = par[v];
        for (int d = 0; d < 4; d++) if (nb[v][d] >= 0) {
            if (adj[r][d] < 0) adj[r][d] = nb[v][d];
            else { stk[top][0] = adj[r][d]; stk[top][1] = nb[v][d]; top++; }
        }
    }
    for (int i = 0; i < k; i++) { stk[top][0] = su[list[i]]; stk[top][1] = sv[list[i]]; top++; }
    while (top > 0) {
        top--;
        int x = find(stk[top][0]), y = find(stk[top][1]);
        if (x == y) continue;
        if (sz[x] < sz[y]) { int t = x; x = y; y = t; }
        par[y] = x; sz[x] += sz[y];
        for (int d = 0; d < 4; d++) if (adj[y][d] >= 0) {
            if (adj[x][d] < 0) adj[x][d] = adj[y][d];
            else { stk[top][0] = adj[x][d]; stk[top][1] = adj[y][d]; top++; }
        }
    }
    static int map[MAXV]; int c = 0;
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

/* ---- hash set ---- */
typedef struct { lab_t *keys; uint8_t *used; size_t cap, cnt; } set_t;
static uint64_t hsh(const lab_t *k) {
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < V; i++) { h ^= k[i]; h *= 1099511628211ULL; }
    return h;
}
static void set_init(set_t *s, size_t cap) {
    s->cap = cap; s->cnt = 0;
    s->keys = malloc(cap * (size_t)V * sizeof(lab_t)); s->used = calloc(cap, 1);
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
        if (!memcmp(s->keys + i * V, k, V * sizeof(lab_t))) return 0;
        i = (i + 1) & (s->cap - 1);
    }
    s->used[i] = 1; memcpy(s->keys + i * V, k, V * sizeof(lab_t)); s->cnt++;
    return 1;
}

static int *LAW, NL, *OV, NO;

/* least number of lawful seeds taking X to the goal, searched to depth B;
 * returns B+1 if none within B.  BFS with state dedupe. */
static int lawneed(const lab_t *X, int B) {
    if (goal(X)) return 0;
    if (B <= 0) return B + 1;
    set_t cur; set_init(&cur, 64); set_add(&cur, X);
    lab_t nx[MAXV];
    for (int d = 1; d <= B; d++) {
        int store = d < B;
        set_t nxt; if (store) set_init(&nxt, 1024);
        for (size_t i = 0; i < cur.cap; i++) {
            if (!cur.used[i]) continue;
            const lab_t *st = cur.keys + i * V;
            for (int t = 0; t < NL; t++) {
                int s = LAW[t];
                if (st[su[s]] == st[sv[s]]) continue;
                closure(st, &s, 1, nx);
                if (goal(nx)) { set_free(&cur); if (store) set_free(&nxt); return d; }
                if (store) set_add(&nxt, nx);
            }
        }
        set_free(&cur);
        if (!store) break;
        cur = nxt;
    }
    return B + 1;
}

/* is there a set of at most B lawful seeds taking X to the goal?  Plain
 * enumeration of the B-subsets of the lawful seeds not yet merged in X
 * (monotone goal, so exactly-B subsets suffice). */
static int lawtest_comb(const lab_t *X, int B) {
    if (goal(X)) return 1;
    int L[8192], m = 0;
    for (int t = 0; t < NL; t++) if (X[su[LAW[t]]] != X[sv[LAW[t]]]) L[m++] = LAW[t];
    if (B > m) B = m;
    if (B <= 0) return 0;
    int c[64], sel[64];
    lab_t nx[MAXV];
    for (int i = 0; i < B; i++) c[i] = i;
    while (1) {
        for (int i = 0; i < B; i++) sel[i] = L[c[i]];
        closure(X, sel, B, nx);
        if (goal(nx)) return 1;
        int i = B - 1;
        while (i >= 0 && c[i] == m - B + i) i--;
        if (i < 0) return 0;
        c[i]++;
        for (int j = i + 1; j < B; j++) c[j] = c[j - 1] + 1;
    }
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    int smax = atoi(argv[2]);
    long maxP = argc > 3 ? atol(argv[3]) : -1;
    int exact = argc > 4 && !strcmp(argv[4], "exact");
    int part = argc > 6 ? atoi(argv[5]) : 0, nparts = argc > 6 ? atoi(argv[6]) : 1;
    if (!f || fscanf(f, "%d %d", &V, &n) != 2) return 1;
    if (V > MAXV) { printf("V too large\n"); return 1; }
    for (int v = 0; v < V; v++) for (int d = 0; d < 4; d++) if (fscanf(f, "%d", &nb[v][d]) != 1) return 1;
    for (int v = 0; v < V; v++) if (fscanf(f, "%d", &mm[v]) != 1) return 1;
    int over; for (int v = 0; v < V; v++) if (fscanf(f, "%d", &over) != 1) return 1;
    if (fscanf(f, "%d", &S) != 1) return 1;
    for (int i = 0; i < S; i++) if (fscanf(f, "%d %d %d", &su[i], &sv[i], &slaw[i]) != 3) return 1;
    if (fscanf(f, "%d", &NA) != 1) NA = 0;
    aut = malloc(sizeof(int[MAXV]) * (NA > 0 ? NA : 1));
    for (int a = 0; a < NA; a++) for (int v = 0; v < V; v++) if (fscanf(f, "%d", &aut[a][v]) != 1) return 1;
    if (NA == 0) { NA = 1; for (int v = 0; v < V; v++) aut[0][v] = v; }
    for (int i = 0; i < MAXV; i++) firstm[i] = -1;
    for (int v = 0; v < V; v++) if (firstm[mm[v]] < 0) firstm[mm[v]] = v;
    LAW = malloc(sizeof(int) * S); OV = malloc(sizeof(int) * S);
    NL = NO = 0;
    for (int i = 0; i < S; i++) { if (slaw[i]) LAW[NL++] = i; else OV[NO++] = i; }
    /* plain subset enumeration of lawful completions when the budget is <= combB */
    int combB = NL <= 14 ? 64 : 3;

    lab_t id[MAXV], base[MAXV], X[MAXV];
    for (int v = 0; v < V; v++) id[v] = (lab_t)v;
    closure(id, NULL, 0, base);
    int law = lawneed(base, 64);
    printf("V %d n %d seeds %d lawful %d overfold %d auts %d law %d\n", V, n, S, NL, NO, NA, law);
    fflush(stdout);
    if (law <= 1) { printf("trivial\n"); return 0; }

    /* orbit representatives of overfold seeds: canonical single-seed closures */
    int *isrep = calloc(S, sizeof(int));
    {
        set_t seen; set_init(&seen, 1024);
        lab_t cl[MAXV], img[MAXV], cur[MAXV], best[MAXV];
        for (int t = 0; t < NO; t++) {
            int s = OV[t];
            closure(base, &s, 1, cl);
            for (int a = 0; a < NA; a++) {
                for (int v = 0; v < V; v++) img[aut[a][v]] = cl[v];
                static int map[MAXV]; int c = 0;
                for (int i = 0; i < V; i++) map[i] = -1;
                for (int v = 0; v < V; v++) {
                    if (map[img[v]] < 0) map[img[v]] = c++;
                    cur[v] = (lab_t)map[img[v]];
                }
                if (a == 0 || memcmp(cur, best, V * sizeof(lab_t)) < 0) memcpy(best, cur, V * sizeof(lab_t));
            }
            if (set_add(&seen, best)) isrep[s] = 1;
        }
        set_free(&seen);
    }
    int nrep = 0; for (int t = 0; t < NO; t++) nrep += isrep[OV[t]];
    printf("overfold orbit reps %d\n", nrep);

    int P[16];
    for (int s = 1; s <= smax && s < law + 1; s++) {
        long hist[70] = {0}; long tested = 0; int viol = 0;
        int B = law - 1 - s;  /* lawful budget for a violation */
        /* P[0] rep; P[1] < P[2] < ... over overfold indices != P[0] */
        int idx[16];
        for (int r = 0; r < NO && !viol; r++) {
            if (!isrep[OV[r]]) continue;
            if (r % nparts != part) continue;
            idx[0] = r;
            /* combinations of s-1 from the other NO-1 indices */
            int k = s - 1;
            int c[16];
            for (int i = 0; i < k; i++) c[i] = i;
            /* trivial automorphism group: plain r < c[0] < c[1] < ... */
            int triv = (NA == 1);
            int others = triv ? NO - 1 - r : NO - 1;
            if (k > others) continue;
            while (1) {
                P[0] = OV[r];
                for (int i = 0; i < k; i++) { int o = triv ? r + 1 + c[i] : (c[i] >= r ? c[i] + 1 : c[i]); P[1 + i] = OV[o]; }
                closure(base, P, s, X);
                int bud = exact ? B + 1 : B;
                int need;
                if (!exact && bud <= combB) need = lawtest_comb(X, bud < 0 ? 0 : bud) ? (bud < 0 ? 0 : bud) : bud + 1;  /* "<= bud" */
                else need = lawneed(X, bud < 0 ? 0 : bud);
                int saving = law - s - need;  /* > 0 means violation */
                int hb = saving + 35; if (hb < 0) hb = 0; if (hb > 69) hb = 69;
                hist[hb]++; tested++;
                if (saving > 0 || (goal(X) && s < law)) {
                    viol = 1;
                    printf("VIOLATION s %d lawneed %d law %d P", s, need, law);
                    for (int i = 0; i < s; i++) printf(" %d(%d,%d)", P[i], su[P[i]], sv[P[i]]);
                    printf("\n"); fflush(stdout);
                    break;
                }
                if (maxP > 0 && tested >= maxP) break;
                int i = k - 1;
                while (i >= 0 && c[i] == others - k + i) i--;
                if (i < 0) break;
                c[i]++;
                for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1;
            }
            if (maxP > 0 && tested >= maxP) break;
        }
        printf("s %d tested %ld%s saving-hist:", s, tested, (maxP > 0 && tested >= maxP) ? " (TRUNCATED)" : "");
        for (int h = 0; h < 70; h++) if (hist[h]) printf(" %s%d:%ld", h == 0 ? "<=" : "", h - 35, hist[h]);
        printf("\n"); fflush(stdout);
        if (viol) break;
    }
    return 0;
}
