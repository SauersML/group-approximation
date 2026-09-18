/* Internal root search over Thompson's group V (untrusted search; verify with verify_roots.py).

   Input lines: "<id> <word> ..." with <word> in the census format of
   experiments/kl-thompson-v-census/census2.py: syllables g t^(+-1), g in {a,b,B,c} or empty.

   For each word w and each endomorphism phi in a fixed list, search t0 in V with
   w^phi(t0) = 1 (right action: a point passes g_0, t^(e_0), g_1, ...).  t0 ranges over all
   bijections between the leaves of two complete prefix codes with N <= NMAX leaves; for each
   code pair a depth-first search assigns the bijection lazily, driven by symbolic simulation
   of cones through the word (a cone is split only when a map needs more letters).

   Endomorphisms phi = (P, mask): P a complete prefix code, phi(g) acts as g on the cones p in P
   with mask bit 1 and as the identity on the others.  If some cone has mask 1, phi is injective
   (V is simple), so a hit certifies that V -> (V * <t>)/<<w>> is injective.

   Usage: rootsearch NMAX ENDOS IN OUT      ENDOS: comma list of endomorphism indices (see table)
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct { uint64_t v; int l; } Str;

static inline int is_prefix(Str p, Str s) { return s.l >= p.l && (p.l == 0 || (s.v >> (s.l - p.l)) == p.v); }
static inline Str replace(Str s, Str d, Str r) {
    int tl = s.l - d.l; Str o; uint64_t mask = tl ? ((((uint64_t)1) << tl) - 1) : 0;
    o.v = (r.v << tl) | (s.v & mask); o.l = r.l + tl; return o;
}
static Str mk(const char *c) { Str s = {0, 0}; for (; *c; c++) { s.v = (s.v << 1) | (uint64_t)(*c - '0'); s.l++; } return s; }
static void pr(FILE *f, Str s) { for (int i = s.l - 1; i >= 0; i--) fputc('0' + (int)((s.v >> i) & 1), f); }

#define MAXP 64
typedef struct { int n; Str d[MAXP], r[MAXP]; } Elt;

/* generators (census vgroup.py) */
static const char *GA[][2] = {{"00","01"},{"01","00"},{"1","1"}};
static const char *GB[][2] = {{"00","00"},{"01","10"},{"10","11"},{"11","01"}};
static const char *GC[][2] = {{"1","00"},{"00","1"},{"01","01"}};

/* endomorphism table: code and mask */
typedef struct { int k; const char *code[8]; int mask[8]; const char *name; } Endo;
static Endo ENDOS[] = {
    {1, {""}, {1}, "delta1"},
    {2, {"0","1"}, {1,1}, "delta2"},
    {3, {"0","10","11"}, {1,1,1}, "delta3"},
    {4, {"00","01","10","11"}, {1,1,1,1}, "delta4"},
    {2, {"0","1"}, {1,0}, "g+1"},
    {3, {"0","10","11"}, {1,1,0}, "g+g+1"},
    {3, {"0","10","11"}, {1,0,0}, "g+1+1"},
    {3, {"0","10","11"}, {0,1,1}, "1+g+g"},
    {5, {"0","100","101","110","111"}, {1,1,1,1,1}, "delta5"},
    {4, {"0","10","110","111"}, {1,1,1,0}, "g+g+g+1"},
    {3, {"00","01","1"}, {1,0,0}, "g+1q"},
};
#define NENDO (int)(sizeof(ENDOS)/sizeof(ENDOS[0]))

static Elt coef[4]; /* a b B c after phi */

static void build_coefs(int e) {
    Endo *E = &ENDOS[e];
    Elt base[4];
    memset(base, 0, sizeof base);
    for (int i = 0; i < 3; i++) { base[0].d[i] = mk(GA[i][0]); base[0].r[i] = mk(GA[i][1]); } base[0].n = 3;
    for (int i = 0; i < 4; i++) { base[1].d[i] = mk(GB[i][0]); base[1].r[i] = mk(GB[i][1]); } base[1].n = 4;
    for (int i = 0; i < 4; i++) { base[2].d[i] = mk(GB[i][1]); base[2].r[i] = mk(GB[i][0]); } base[2].n = 4;
    for (int i = 0; i < 3; i++) { base[3].d[i] = mk(GC[i][0]); base[3].r[i] = mk(GC[i][1]); } base[3].n = 3;
    for (int g = 0; g < 4; g++) {
        Elt *o = &coef[g]; o->n = 0;
        for (int p = 0; p < E->k; p++) {
            Str ps = mk(E->code[p]);
            if (!E->mask[p]) { o->d[o->n] = ps; o->r[o->n] = ps; o->n++; continue; }
            for (int i = 0; i < base[g].n; i++) {
                Str d = base[g].d[i], r = base[g].r[i];
                Str dd = {(ps.v << d.l) | d.v, ps.l + d.l}, rr = {(ps.v << r.l) | r.v, ps.l + r.l};
                o->d[o->n] = dd; o->r[o->n] = rr; o->n++;
            }
        }
    }
}

/* word */
static int W_n, W_sign[64], W_coef[64]; /* coef -1 = none, 0..3 */

static int parse(const char *w) {
    int cur = -1; W_n = 0;
    for (; *w; w++) {
        char ch = *w;
        if (ch == 't' || ch == 'T') { W_sign[W_n] = ch == 't' ? 1 : -1; W_coef[W_n] = cur; W_n++; cur = -1; }
        else if (ch == 'a') cur = 0; else if (ch == 'b') cur = 1; else if (ch == 'B') cur = 2; else if (ch == 'c') cur = 3;
        else return 0;
    }
    return cur == -1;
}

/* codes */
#define MAXN 8
typedef struct { int n; Str leaf[MAXN]; } Code;
static Code *codes[MAXN + 1]; static int ncodes[MAXN + 1];

static void gen_codes_rec(Str *leaves, int nl, Str *pending, int np, int target, int N) {
    if (nl + np > target) return;
    if (np == 0) {
        if (nl == target) {
            Code *c = &codes[N][ncodes[N]++];
            c->n = nl; for (int i = 0; i < nl; i++) c->leaf[i] = leaves[i];
        }
        return;
    }
    Str s = pending[np - 1];
    /* make s a leaf */
    leaves[nl] = s; gen_codes_rec(leaves, nl + 1, pending, np - 1, target, N);
    /* split s */
    if (s.l < 20) {
        Str s0 = {s.v << 1, s.l + 1}, s1 = {(s.v << 1) | 1, s.l + 1};
        pending[np - 1] = s1; pending[np] = s0;
        gen_codes_rec(leaves, nl, pending, np + 1, target, N);
        pending[np - 1] = s;
    }
}

static void gen_codes(int NMAX) {
    for (int N = 1; N <= NMAX; N++) {
        codes[N] = malloc(sizeof(Code) * 200000); ncodes[N] = 0;
        Str leaves[MAXN + 2], pending[MAXN + 4]; pending[0] = (Str){0, 0};
        gen_codes_rec(leaves, 0, pending, 1, N, N);
    }
}

/* t0 state */
static Code *TD, *TR; static int pi[MAXN], pinv[MAXN];

#define OK 0
#define FAIL 1
#define SPLIT 2
#define NEEDF 3
#define NEEDI 4

static int need_idx;
static long long nodes;

static int apply_elt(const Elt *e, Str *s) {
    for (int i = 0; i < e->n; i++) {
        if (is_prefix(e->d[i], *s)) { *s = replace(*s, e->d[i], e->r[i]); return OK; }
        if (e->d[i].l > s->l && is_prefix(*s, e->d[i])) return SPLIT;
    }
    return FAIL; /* not reached for complete codes */
}

static int simulate(Str p) {
    Str cur = p;
    for (int k = 0; k < W_n; k++) {
        if (W_coef[k] >= 0) { int r = apply_elt(&coef[W_coef[k]], &cur); if (r != OK) return r; }
        if (cur.l > 58) return FAIL;
        int hit = -1;
        if (W_sign[k] > 0) {
            for (int i = 0; i < TD->n; i++) {
                if (is_prefix(TD->leaf[i], cur)) { hit = i; break; }
                if (TD->leaf[i].l > cur.l && is_prefix(cur, TD->leaf[i])) return SPLIT;
            }
            if (pi[hit] < 0) { need_idx = hit; return NEEDF; }
            cur = replace(cur, TD->leaf[hit], TR->leaf[pi[hit]]);
        } else {
            for (int j = 0; j < TR->n; j++) {
                if (is_prefix(TR->leaf[j], cur)) { hit = j; break; }
                if (TR->leaf[j].l > cur.l && is_prefix(cur, TR->leaf[j])) return SPLIT;
            }
            if (pinv[hit] < 0) { need_idx = hit; return NEEDI; }
            cur = replace(cur, TR->leaf[hit], TD->leaf[pinv[hit]]);
        }
    }
    return (cur.l == p.l && cur.v == p.v) ? OK : FAIL;
}

#define MAXSTACK 4096
static long long node_limit;

static int dfs(Str *stack, int sp) {
    Str local[MAXSTACK];
    memcpy(local, stack, sizeof(Str) * sp);
    if (++nodes > node_limit) return 0;
    while (sp > 0) {
        Str p = local[--sp];
        if (p.l > 40) return 0;
        int r = simulate(p);
        if (r == OK) continue;
        if (r == FAIL) return 0;
        if (r == SPLIT) {
            if (sp + 2 >= MAXSTACK) return 0;
            local[sp++] = (Str){(p.v << 1) | 1, p.l + 1};
            local[sp++] = (Str){p.v << 1, p.l + 1};
            continue;
        }
        local[sp++] = p;
        int N = TD->n, idx = need_idx;
        if (r == NEEDF) {
            for (int j = 0; j < N; j++) if (pinv[j] < 0) {
                pi[idx] = j; pinv[j] = idx;
                if (dfs(local, sp)) return 1;
                pi[idx] = -1; pinv[j] = -1;
            }
        } else {
            for (int i = 0; i < N; i++) if (pi[i] < 0) {
                pi[i] = idx; pinv[idx] = i;
                if (dfs(local, sp)) return 1;
                pi[i] = -1; pinv[idx] = -1;
            }
        }
        return 0;
    }
    /* all start cones verified; complete any unassigned leaves is impossible to need:
       every leaf of TD is reached by some cone when a t-letter follows a surjective prefix.
       Still, assign remaining arbitrarily only if consistent: require full assignment. */
    for (int i = 0; i < TD->n; i++) if (pi[i] < 0) return 0;
    return 1;
}

static int search(int NMAX, int *outN) {
    Str st[1]; st[0] = (Str){0, 0};
    for (int N = 1; N <= NMAX; N++) {
        for (int a = 0; a < ncodes[N]; a++) for (int b = 0; b < ncodes[N]; b++) {
            TD = &codes[N][a]; TR = &codes[N][b];
            for (int i = 0; i < N; i++) { pi[i] = -1; pinv[i] = -1; }
            nodes = 0;
            if (dfs(st, 1)) { *outN = N; return 1; }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: rootsearch NMAX ENDOS IN OUT\n"); return 2; }
    int NMAX = atoi(argv[1]);
    int endos[32], ne = 0;
    { char buf[256]; strncpy(buf, argv[2], 255); buf[255] = 0; for (char *tok = strtok(buf, ","); tok; tok = strtok(NULL, ",")) endos[ne++] = atoi(tok); }
    node_limit = argc > 5 ? atoll(argv[5]) : 200000;
    gen_codes(NMAX);
    FILE *in = fopen(argv[3], "r"), *out = fopen(argv[4], "w");
    if (!in || !out) { perror("open"); return 2; }
    char line[512], id[64], word[128];
    long hits = 0, total = 0;
    while (fgets(line, sizeof line, in)) {
        if (sscanf(line, "%63s %127s", id, word) != 2) continue;
        if (!parse(word)) { fprintf(stderr, "bad word %s\n", word); return 2; }
        total++;
        int found = 0, N = 0;
        for (int e = 0; e < ne && !found; e++) {
            build_coefs(endos[e]);
            if (search(NMAX, &N)) {
                found = 1; hits++;
                fprintf(out, "%s %s ROOT endo=%s t0=", id, word, ENDOS[endos[e]].name);
                for (int i = 0; i < N; i++) { if (i) fputc(',', out); pr(out, TD->leaf[i]); fputc(':', out); pr(out, TR->leaf[pi[i]]); }
                fputc('\n', out);
            }
        }
        if (!found) fprintf(out, "%s %s NOROOT\n", id, word);
        fflush(out);
    }
    fprintf(stderr, "words %ld roots %ld\n", total, hits);
    return 0;
}
