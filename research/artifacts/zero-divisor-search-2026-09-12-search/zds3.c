/* zds.c -- F_2 zero divisors (1+x+y) beta = 0 with a prescribed cubic Kaplansky graph.
 * A labelling assigns the ports 1,x,y (0,1,2) bijectively to the three edges at each vertex, with
 * different ports at the two ends of every edge. The edge {u,v} with ports (p,q) encodes
 * g_u p = g_v q (the opposite group turns (1+x+y) beta = 0 into this form). Distinct edges are
 * distinct products, so they must stay distinct. A prune proves no torsion-free realization exists:
 *   coincidence: partial coset enumeration of <x,y | cycle words>, seeded by the product graph;
 *                two cosets tagged with different edges merge
 *   root:        a cycle word u^k (k >= 2) is replaced by u
 *   power:       (-pw L K) a reduced u with |u| <= L and u^e = 1 in the table, 2 <= e <= K, is added
 *   finite:      the enumeration closes, so the group is finite
 *   bs:          (-bs K) a b a^-1 = b^j in the table, |j| <= K, for a basis (a, b) of short words;
 *                the group is a quotient of BS(1, j), so a torsion-free image is solvable and its
 *                group algebra is a domain (Kropholler-Linnell-Moody)
 *   ab:          complete labelling, exponent-sum matrix of rank < 2 (orderable quotient theorem)
 * Vertex order: the root, then most assigned neighbours first (-bfs: breadth-first). The root's
 * ports are fixed (S_3 on port names). -root r: root r. -probe D: run the DFS from every root to
 * depth D and search fully from the root with the fewest depth-D nodes (probe work is counted in
 * TOTAL nodes and prunes; GRAPH lines give it separately).
 * Input: graph6 lines (search). -t: labelled structures "n m u v p q ..." realized in finite groups,
 * every prefix sieved. -t2: the same structures, normalized at vertex 0 and looked for along the
 * DFS. Root, power, finite, bs and ab are off in -t and -t2, so a prune there is a bug.
 * -c N / -cl N: coset limits at inner nodes / leaves. -pwd D / -bsd D: power / bs sieve at depth
 * >= n - D (defaults: leaves only / every depth).
 * -m N: node budget per item; an item that hits it is marked BUDGET and certifies nothing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 40
#define MAXE 60
#define MAXC (1 << 18)
#define MAXR 64
#define MAXL 256

static int n, m, inc[MAXN][3], deg[MAXN], ends[MAXE][2], eport[MAXE][2], assigned[MAXN];
static int ord[MAXN], bpar[MAXN], bedge[MAXN], knorm[MAXE][2];
static int T[MAXC][4], up[MAXC], tag[MAXC], nc, climit, climitNode = 0, climitLeaf = -1;
static int rel[MAXR][MAXL], rlen[MAXR], nr, ex_[MAXR], ey_[MAXR];
static int word[MAXN][MAXL], wlen[MAXN], gb[MAXN], gx[MAXN], gy[MAXN];
static int opt_root = 1, opt_ab = 1, opt_fin = 1, opt_bs = 0, opt_bfs = 0, bsK = 0, bsD = MAXN;
static int pwL = 0, pwK = 0, pwD = 0, ctrl = 0, found, budget_hit, rootv = 0, dlimit = MAXN + 1;
static long long maxnodes = 0, nodelimit;
static long long st_nodes, st_surv, st_coinc, st_ab, st_fin, st_pw, st_pwrel, st_bs, st_probe;
static char g6[256];
static const int PL[3] = {-1, 0, 2};   /* port -> letter; letters 0=x 1=X 2=y 3=Y, inverse l^1 */

static int find(int c) { while (up[c] != c) { up[c] = up[up[c]]; c = up[c]; } return c; }
static int qa[4 * MAXC + 8], qb[4 * MAXC + 8];
static int coincide(int a, int b) {           /* returns 0 iff two differently tagged cosets merge */
  int h = 0, t = 0; qa[t] = a; qb[t++] = b;
  while (h < t) {
    a = find(qa[h]); b = find(qb[h]); h++;
    if (a == b) continue;
    if (a > b) { int s = a; a = b; b = s; }
    if (tag[a] >= 0 && tag[b] >= 0 && tag[a] != tag[b]) return 0;
    if (tag[a] < 0) tag[a] = tag[b];
    up[b] = a;
    for (int l = 0; l < 4; l++) {
      if (T[b][l] < 0) continue;
      int tb = find(T[b][l]);
      if (T[a][l] < 0) T[a][l] = tb;
      else { int ta = find(T[a][l]); if (ta != tb) { qa[t] = ta; qb[t++] = tb; } }
    }
  }
  return 1;
}
static int newcoset(int tg) {
  if (nc >= MAXC) { fprintf(stderr, "MAXC exceeded\n"); exit(2); }
  int c = nc++; up[c] = c; tag[c] = tg; T[c][0] = T[c][1] = T[c][2] = T[c][3] = -1; return c;
}
static int portof(int v, int e) { return eport[e][ends[e][0] == v ? 0 : 1]; }
static int portcoset(int v, int p) { return p == 0 ? gb[v] : p == 1 ? gx[v] : gy[v]; }
static int other(int v, int e) { return ends[e][0] == v ? ends[e][1] : ends[e][0]; }

static int seed(int k) {                      /* product graph of the assigned vertices ord[0..k-1] */
  nc = 0;
  for (int i = 0; i < k; i++) {
    int v = ord[i], tg[3] = {-1, -1, -1};
    for (int j = 0; j < 3; j++) tg[portof(v, inc[v][j])] = inc[v][j];
    gb[v] = newcoset(tg[0]); gx[v] = newcoset(tg[1]); gy[v] = newcoset(tg[2]);
    T[gb[v]][0] = gx[v]; T[gx[v]][1] = gb[v]; T[gb[v]][2] = gy[v]; T[gy[v]][3] = gb[v];
  }
  for (int e = 0; e < m; e++) {
    int u = ends[e][0], v = ends[e][1];
    if (!assigned[u] || !assigned[v]) continue;
    if (!coincide(portcoset(u, eport[e][0]), portcoset(v, eport[e][1]))) return 0;
  }
  return 1;
}
static int freered(int *s, int L) {
  int k = 0;
  for (int i = 0; i < L; i++) { if (k && s[k - 1] == (s[i] ^ 1)) k--; else s[k++] = s[i]; }
  return k;
}
static void build_relators(int k) {           /* fundamental cycle words, as scan sequences */
  nr = 0; wlen[ord[0]] = 0;
  for (int i = 1; i < k; i++) {
    int v = ord[i], u = bpar[v], e = bedge[v], L = wlen[u], p = portof(u, e), q = portof(v, e);
    memcpy(word[v], word[u], L * sizeof(int));
    if (p) word[v][L++] = PL[p];
    if (q) word[v][L++] = PL[q] ^ 1;
    wlen[v] = freered(word[v], L);
  }
  for (int e = 0; e < m; e++) {
    int u = ends[e][0], v = ends[e][1];
    if (!assigned[u] || !assigned[v] || bedge[u] == e || bedge[v] == e) continue;
    int *s = rel[nr], L = wlen[u], p = eport[e][0], q = eport[e][1], a = 0;
    memcpy(s, word[u], L * sizeof(int));
    if (p) s[L++] = PL[p];
    if (q) s[L++] = PL[q] ^ 1;
    for (int j = wlen[v] - 1; j >= 0; j--) s[L++] = word[v][j] ^ 1;
    L = freered(s, L);
    while (L - 2 * a >= 2 && s[a] == (s[L - 1 - a] ^ 1)) a++;
    L -= 2 * a; memmove(s, s + a, L * sizeof(int));
    if (L == 0) continue;
    ex_[nr] = ey_[nr] = 0;
    for (int j = 0; j < L; j++) {
      if (s[j] == 0) ex_[nr]++; else if (s[j] == 1) ex_[nr]--; else if (s[j] == 2) ey_[nr]++; else ey_[nr]--;
    }
    if (opt_root)
      for (int d = 1; d < L; d++) {
        if (L % d) continue;
        int ok = 1;
        for (int j = d; j < L && ok; j++) if (s[j] != s[j - d]) ok = 0;
        if (ok) { L = d; break; }
      }
    rlen[nr++] = L;
  }
}
static int scan(int c, const int *s, int L, int *chg) {   /* HLT scan of one relator at coset c */
  int f = c, i = 0, b = c, j = L, t;
  while (i < L && (t = T[f][s[i]]) >= 0) { f = find(t); i++; }
  if (i == L) { if (f != c) { *chg = 1; return coincide(f, c); } return 1; }
  while (j > i && (t = T[b][s[j - 1] ^ 1]) >= 0) { b = find(t); j--; }
  if (j == i) { if (f != b) { *chg = 1; return coincide(f, b); } return 1; }
  while (j > i + 1) {
    if (nc >= climit) return 1;
    int d = newcoset(-1); T[f][s[i]] = d; T[d][s[i] ^ 1] = f; f = d; i++; *chg = 1;
  }
  T[f][s[i]] = b; T[b][s[i] ^ 1] = f; *chg = 1;
  return 1;
}
static int enumerate(void) {                  /* 0: contradiction, 1: pass limit, 2: stable */
  int chg = 1;
  for (int pass = 0; chg; pass++) {
    if (pass >= 400) return 1;
    chg = 0;
    for (int c = 0; c < nc; c++)
      for (int r = 0; r < nr && up[c] == c; r++)
        if (!scan(c, rel[r], rlen[r], &chg)) return 0;
  }
  return 2;
}
static int complete(void) {
  for (int c = 0; c < nc; c++)
    if (up[c] == c) for (int l = 0; l < 4; l++) if (T[c][l] < 0) return 0;
  return 1;
}
static int trace(int c, const int *s, int L) {   /* the coset c s, or -1 */
  for (int i = 0; i < L; i++) { int t = T[c][s[i]]; if (t < 0) return -1; c = find(t); }
  return c;
}
static int known(const int *u, int L) {
  for (int r = 0; r < nr; r++) if (rlen[r] == L && !memcmp(rel[r], u, L * sizeof(int))) return 1;
  return 0;
}
static int powersieve(int k) {                /* u^e = 1 in the group, so u = 1 when torsion-free */
  int added = 0, u[8];
  for (int L = 1; L <= pwL; L++)
    for (int code = 0; code < (1 << (2 * L)); code++) {
      int ok = 1;
      for (int i = 0, z = code; i < L; i++, z >>= 2) u[i] = z & 3;
      for (int i = 1; i < L && ok; i++) if (u[i] == (u[i - 1] ^ 1)) ok = 0;
      if (!ok || (L > 1 && u[0] == (u[L - 1] ^ 1)) || known(u, L)) continue;
      for (int i = 0; i < k && ok; i++) {
        int c = find(gb[ord[i]]), d = c;
        for (int e = 1; e <= pwK && ok && (d = trace(d, u, L)) >= 0; e++) {
          if (d != c) continue;
          if (e >= 2) {
            if (nr >= MAXR) return added;
            memcpy(rel[nr], u, L * sizeof(int)); rlen[nr++] = L; added++;
          }
          ok = 0;
        }
      }
    }
  return added;
}
static int bsw[72][2][2], bsl[72][2], nbs;    /* basis pairs: a letter with a letter or a mixed 2-letter word */
static void bs_add(const int *a, int La, const int *b, int Lb) {
  memcpy(bsw[nbs][0], a, La * sizeof(int)); memcpy(bsw[nbs][1], b, Lb * sizeof(int));
  bsl[nbs][0] = La; bsl[nbs][1] = Lb; nbs++;
}
static void bs_init(void) {
  int two[8][2], k = 0;
  for (int p = 0; p < 2; p++)
    for (int q = 2; q < 4; q++) { two[k][0] = p; two[k][1] = q; k++; two[k][0] = q; two[k][1] = p; k++; }
  for (int s = 0; s < 4; s++) {
    for (int t = 0; t < 4; t++) if ((s >> 1) != (t >> 1)) bs_add(&s, 1, &t, 1);
    for (int w = 0; w < 8; w++) { bs_add(&s, 1, two[w], 2); bs_add(two[w], 2, &s, 1); }
  }
}
static int bssieve(int k) {                   /* a b a^-1 = b^j for a basis (a, b) and |j| <= bsK */
  for (int p = 0; p < nbs; p++) {
    int La = bsl[p][0], Lb = bsl[p][1], L = 0, aba[6], binv[2];
    for (int i = 0; i < La; i++) aba[L++] = bsw[p][0][i];
    for (int i = 0; i < Lb; i++) aba[L++] = bsw[p][1][i];
    for (int i = La - 1; i >= 0; i--) aba[L++] = bsw[p][0][i] ^ 1;
    for (int i = 0; i < Lb; i++) binv[i] = bsw[p][1][Lb - 1 - i] ^ 1;
    for (int i = 0; i < k; i++) {
      int c = find(gb[ord[i]]), d = trace(c, aba, L), e;
      if (d < 0) continue;
      if (d == c) return 1;
      e = c;
      for (int j = 1; j <= bsK && (e = trace(e, bsw[p][1], Lb)) >= 0; j++) if (e == d) return 1;
      e = c;
      for (int j = 1; j <= bsK && (e = trace(e, binv, Lb)) >= 0; j++) if (e == d) return 1;
    }
  }
  return 0;
}
static int sieve(int k, int leaf) {
  climit = leaf ? climitLeaf : climitNode;
  if (!seed(k)) { st_coinc++; return 0; }
  build_relators(k);
  if (leaf && opt_ab) {
    int rk = 0;
    for (int a = 0; a < nr && !rk; a++)
      for (int b = a + 1; b < nr && !rk; b++) if (ex_[a] * ey_[b] - ex_[b] * ey_[a]) rk = 1;
    if (!rk) { st_ab++; return 0; }
  }
  int r = enumerate();
  if (!r) { st_coinc++; return 0; }
  for (int round = 0; pwL && k >= n - pwD && round < 4; round++) {
    int a = powersieve(k);
    if (!a) break;
    st_pwrel += a;
    if (!(r = enumerate())) { st_pw++; return 0; }
  }
  if (opt_bs && k >= n - bsD && bssieve(k)) { st_bs++; return 0; }
  if (opt_fin && r == 2 && complete()) { st_fin++; return 0; }
  return 1;
}
static void order(void) {                     /* ord[0] = rootv; each later vertex has an earlier neighbour */
  int in[MAXN] = {0}, h = 0, t = 1;
  ord[0] = rootv; in[rootv] = 1; bpar[rootv] = -1; bedge[rootv] = -1;
  while (t < n) {
    int best = -1, bc = 0;
    if (opt_bfs) {
      for (; h < t && best < 0; h++)
        for (int j = 0; j < 3 && best < 0; j++) if (!in[other(ord[h], inc[ord[h]][j])]) best = other(ord[h], inc[ord[h]][j]);
      if (best >= 0) h--;
    } else
      for (int v = 0; v < n; v++) {
        if (in[v]) continue;
        int c = 0;
        for (int j = 0; j < 3; j++) c += in[other(v, inc[v][j])];
        if (c > bc) { bc = c; best = v; }
      }
    if (best < 0) { fprintf(stderr, "disconnected input\n"); exit(2); }
    for (int j = 0; j < 3; j++)
      if (in[other(best, inc[best][j])]) { bpar[best] = other(best, inc[best][j]); bedge[best] = inc[best][j]; break; }
    ord[t++] = best; in[best] = 1;
  }
}
static void clear_labels(void) {
  for (int e = 0; e < m; e++) eport[e][0] = eport[e][1] = -1;
  for (int v = 0; v < n; v++) assigned[v] = 0;
}
static void report(void) {
  printf("SURV %s root %d ports", g6, rootv);
  for (int v = 0; v < n; v++) {
    putchar(' ');
    for (int j = 0; j < 3; j++) putchar('0' + portof(v, inc[v][j]));
  }
  printf(" rels");
  for (int r = 0; r < nr; r++) { putchar(' '); for (int j = 0; j < rlen[r]; j++) putchar("xXyY"[rel[r][j]]); }
  printf(" cosets %d\n", nc); fflush(stdout);
}
static const int PERM[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
static void dfs(int i) {                      /* the root fixed up to the S_3 on port names */
  int v = ord[i];
  if (maxnodes && st_nodes >= nodelimit) { budget_hit = 1; return; }
  for (int t = 0; t < (i ? 6 : 1); t++) {
    int ok = 1;
    for (int j = 0; j < 3 && ok; j++) {
      int e = inc[v][j], s = ends[e][0] == v ? 0 : 1;
      if (assigned[ends[e][1 - s]] && eport[e][1 - s] == PERM[t][j]) ok = 0;
      if (ctrl && knorm[e][s] != PERM[t][j]) ok = 0;
    }
    if (!ok) continue;
    for (int j = 0; j < 3; j++) { int e = inc[v][j]; eport[e][ends[e][0] == v ? 0 : 1] = PERM[t][j]; }
    assigned[v] = 1; st_nodes++;
    if (sieve(i + 1, i + 1 == n)) {
      if (i + 1 == dlimit) st_probe++;
      else if (i + 1 < n) dfs(i + 1);
      else if (ctrl) found = 1;
      else { st_surv++; report(); }
    }
    assigned[v] = 0;
    for (int j = 0; j < 3; j++) { int e = inc[v][j]; eport[e][ends[e][0] == v ? 0 : 1] = -1; }
  }
}
static int parse_g6(const char *s) {
  n = s[0] - 63; m = 0;
  if (n < 4 || n > MAXN) return 0;
  for (int v = 0; v < n; v++) deg[v] = 0;
  int k = 0, bit = 0, len = (int)strlen(s + 1);
  for (int j = 1; j < n; j++)
    for (int i = 0; i < j; i++) {
      if (k >= len) return 0;
      int x = ((s[1 + k] - 63) >> (5 - bit)) & 1;
      if (++bit == 6) { bit = 0; k++; }
      if (!x) continue;
      if (m >= MAXE || deg[i] >= 3 || deg[j] >= 3) return 0;
      ends[m][0] = i; ends[m][1] = j; inc[i][deg[i]++] = m; inc[j][deg[j]++] = m; m++;
    }
  for (int v = 0; v < n; v++) if (deg[v] != 3) return 0;
  return 1;
}
static int parse_test(char *p) {
  int off, u, v, a, b;
  if (sscanf(p, "%d %d%n", &n, &m, &off) != 2 || n < 2 || n > MAXN || m != 3 * n / 2) return 0;
  p += off;
  for (int x = 0; x < n; x++) deg[x] = 0;
  for (int e = 0; e < m; e++) {
    if (sscanf(p, "%d %d %d %d%n", &u, &v, &a, &b, &off) != 4) return 0;
    p += off;
    if (u == v || u < 0 || v < 0 || u >= n || v >= n || a == b || a < 0 || b < 0 || a > 2 || b > 2) return 0;
    if (deg[u] >= 3 || deg[v] >= 3) return 0;
    ends[e][0] = u; ends[e][1] = v; eport[e][0] = a; eport[e][1] = b;
    inc[u][deg[u]++] = e; inc[v][deg[v]++] = e;
  }
  for (int x = 0; x < n; x++) {
    if (deg[x] != 3) return 0;
    int seen = 0;
    for (int j = 0; j < 3; j++) seen |= 1 << portof(x, inc[x][j]);
    if (seen != 7) return 0;
  }
  return 1;
}
static void test_item(int test, const char *line, long long *fails) {
  order();
  if (test == 1) {
    for (int k = 1; k <= n; k++) {
      for (int v = 0; v < n; v++) assigned[v] = 0;
      for (int i = 0; i < k; i++) assigned[ord[i]] = 1;
      if (!sieve(k, k == n)) { (*fails)++; printf("FAIL prefix %d: %s\n", k, line); return; }
    }
    return;
  }
  int sig[3];
  for (int j = 0; j < 3; j++) sig[portof(0, inc[0][j])] = j;
  for (int e = 0; e < m; e++) {
    knorm[e][0] = sig[eport[e][0]]; knorm[e][1] = sig[eport[e][1]]; eport[e][0] = eport[e][1] = -1;
  }
  for (int v = 0; v < n; v++) assigned[v] = 0;
  found = 0; budget_hit = 0; nodelimit = st_nodes + maxnodes;
  dfs(0);
  if (!found) { (*fails)++; printf("CONTROL NOT FOUND: %s\n", line); }
}
int main(int argc, char **argv) {
  int test = 0, rootopt = 0, probeD = 0; static char line[1 << 16];
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-t")) test = 1;
    else if (!strcmp(argv[i], "-t2")) test = 2;
    else if (!strcmp(argv[i], "-c") && i + 1 < argc) climitNode = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-cl") && i + 1 < argc) climitLeaf = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-m") && i + 1 < argc) maxnodes = atoll(argv[++i]);
    else if (!strcmp(argv[i], "-pw") && i + 2 < argc) { pwL = atoi(argv[i + 1]); pwK = atoi(argv[i + 2]); i += 2; }
    else if (!strcmp(argv[i], "-pwd") && i + 1 < argc) pwD = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-bs") && i + 1 < argc) { opt_bs = 1; bsK = atoi(argv[++i]); }
    else if (!strcmp(argv[i], "-bsd") && i + 1 < argc) bsD = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-root") && i + 1 < argc) rootopt = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-probe") && i + 1 < argc) probeD = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-bfs")) opt_bfs = 1;
    else if (!strcmp(argv[i], "-noab")) opt_ab = 0;
    else { fprintf(stderr, "usage: zds [-t | -t2] [-c N] [-cl N] [-m N] [-pw L K] [-pwd D] [-bs K] [-bsd D] [-root r] [-probe D] [-bfs] [-noab]\n"); return 2; }
  }
  if (test) { opt_root = opt_ab = opt_fin = opt_bs = 0; pwL = 0; ctrl = test == 2; rootopt = probeD = 0; }
  if (climitLeaf < 0) climitLeaf = climitNode;
  if (climitNode > MAXC) climitNode = MAXC;
  if (climitLeaf > MAXC) climitLeaf = MAXC;
  if (pwL > 8) pwL = 8;
  bs_init();
  long long items = 0, fails = 0, budgets = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0] || line[0] == '>' || line[0] == '#') continue;
    items++;
    if (test) {
      if (!parse_test(line)) { fprintf(stderr, "bad structure: %s\n", line); return 2; }
      rootv = 0; test_item(test, line, &fails);
      continue;
    }
    if (!parse_g6(line)) { fprintf(stderr, "bad graph6: %s\n", line); return 2; }
    snprintf(g6, sizeof g6, "%.200s", line);
    long long s0 = st_surv, pn = 0, pbest = -1, mx = maxnodes;
    rootv = rootopt < n ? rootopt : 0;
    if (probeD > 0 && probeD < n) {
      int br = 0; long long ns = st_nodes;
      maxnodes = 0; dlimit = probeD;
      for (int r = 0; r < n; r++) {
        rootv = r; order(); clear_labels(); st_probe = 0;
        dfs(0);
        if (pbest < 0 || st_probe < pbest) { pbest = st_probe; br = r; }
      }
      pn = st_nodes - ns; rootv = br; dlimit = MAXN + 1; maxnodes = mx;
    }
    order(); clear_labels();
    long long n0 = st_nodes;
    budget_hit = 0; nodelimit = st_nodes + maxnodes;
    dfs(0);
    budgets += budget_hit;
    printf("GRAPH %lld %s nodes %lld surv %lld root %d probe %lld %lld%s\n", items, g6, st_nodes - n0,
           st_surv - s0, rootv, pn, pbest, budget_hit ? " BUDGET" : "");
    fflush(stdout);
  }
  printf("TOTAL items %lld nodes %lld surv %lld prunes coinc %lld ab %lld finite %lld power %lld"
         " (relators %lld) bs %lld fails %lld budget %lld climit %d leaf %d pw %d %d depth %d bs %d %d"
         " root %d probe %d %s\n",
         items, st_nodes, st_surv, st_coinc, st_ab, st_fin, st_pw, st_pwrel, st_bs, fails, budgets,
         climitNode, climitLeaf, pwL, pwK, pwD, opt_bs ? bsK : -1, bsD, rootopt, probeD,
         opt_bfs ? "bfs" : "greedy");
  return 0;
}
