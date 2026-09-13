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
 *   ab:          complete labelling, exponent-sum matrix of rank < 2 (orderable quotient theorem)
 * Input: graph6 lines (search). -t: labelled structures "n m u v p q ..." realized in finite groups,
 * every BFS prefix sieved. -t2: the same structures, normalized at vertex 0 and looked for along the
 * DFS. Root, power, finite and ab are off in -t and -t2, so a prune there is a bug.
 * -c N / -cl N: coset limits at inner nodes / leaves. -pwd D: power sieve at depth >= n - D.
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
static int opt_root = 1, opt_ab = 1, opt_fin = 1, pwL = 0, pwK = 0, pwD = 0, ctrl = 0, found, budget_hit;
static long long maxnodes = 0, nodelimit;
static long long st_nodes, st_surv, st_coinc, st_ab, st_fin, st_pw, st_pwrel;
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
static int trace(int c, const int *s, int L, int reps) {   /* the coset c s^reps, or -1 */
  for (int r = 0; r < reps; r++)
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
        int c = find(gb[ord[i]]);
        if (trace(c, u, L, 1) == c) break;
        for (int e = 2; e <= pwK && ok; e++)
          if (trace(c, u, L, e) == c) {
            if (nr >= MAXR) return added;
            memcpy(rel[nr], u, L * sizeof(int)); rlen[nr++] = L; added++; ok = 0;
          }
      }
    }
  return added;
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
  if (opt_fin && r == 2 && complete()) { st_fin++; return 0; }
  return 1;
}
static void bfs(void) {
  int seen[MAXN] = {0}, h = 0, t = 0;
  ord[t++] = 0; seen[0] = 1; bpar[0] = -1; bedge[0] = -1;
  while (h < t) {
    int u = ord[h++];
    for (int j = 0; j < 3; j++) {
      int e = inc[u][j], v = ends[e][0] == u ? ends[e][1] : ends[e][0];
      if (!seen[v]) { seen[v] = 1; bpar[v] = u; bedge[v] = e; ord[t++] = v; }
    }
  }
  if (t != n) { fprintf(stderr, "disconnected input\n"); exit(2); }
}
static void report(void) {
  printf("SURV %s ports", g6);
  for (int v = 0; v < n; v++) {
    putchar(' ');
    for (int j = 0; j < 3; j++) putchar('0' + portof(v, inc[v][j]));
  }
  printf(" rels");
  for (int r = 0; r < nr; r++) { putchar(' '); for (int j = 0; j < rlen[r]; j++) putchar("xXyY"[rel[r][j]]); }
  printf(" cosets %d\n", nc); fflush(stdout);
}
static const int PERM[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
static void dfs(int i) {                      /* vertex 0 fixed up to the S_3 on port names */
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
      if (i + 1 < n) dfs(i + 1);
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
int main(int argc, char **argv) {
  int test = 0; static char line[1 << 16];
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-t")) test = 1;
    else if (!strcmp(argv[i], "-t2")) test = 2;
    else if (!strcmp(argv[i], "-c") && i + 1 < argc) climitNode = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-cl") && i + 1 < argc) climitLeaf = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-m") && i + 1 < argc) maxnodes = atoll(argv[++i]);
    else if (!strcmp(argv[i], "-pw") && i + 2 < argc) { pwL = atoi(argv[i + 1]); pwK = atoi(argv[i + 2]); i += 2; }
    else if (!strcmp(argv[i], "-pwd") && i + 1 < argc) pwD = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-noab")) opt_ab = 0;
    else { fprintf(stderr, "usage: zds [-t | -t2] [-c N] [-cl N] [-m N] [-pw L K] [-pwd D] [-noab] < input\n"); return 2; }
  }
  if (test) { opt_root = opt_ab = opt_fin = 0; pwL = 0; ctrl = test == 2; }
  if (climitLeaf < 0) climitLeaf = climitNode;
  if (climitNode > MAXC) climitNode = MAXC;
  if (climitLeaf > MAXC) climitLeaf = MAXC;
  if (pwL > 8) pwL = 8;
  long long items = 0, fails = 0, budgets = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0] || line[0] == '>' || line[0] == '#') continue;
    items++;
    if (test) {
      if (!parse_test(line)) { fprintf(stderr, "bad structure: %s\n", line); return 2; }
      bfs();
      if (test == 1) {
        for (int k = 1; k <= n; k++) {
          for (int v = 0; v < n; v++) assigned[v] = 0;
          for (int i = 0; i < k; i++) assigned[ord[i]] = 1;
          if (!sieve(k, k == n)) { fails++; printf("FAIL prefix %d: %s\n", k, line); break; }
        }
        continue;
      }
      int sig[3];
      for (int j = 0; j < 3; j++) sig[portof(0, inc[0][j])] = j;
      for (int e = 0; e < m; e++) {
        knorm[e][0] = sig[eport[e][0]]; knorm[e][1] = sig[eport[e][1]]; eport[e][0] = eport[e][1] = -1;
      }
      for (int v = 0; v < n; v++) assigned[v] = 0;
      found = 0; budget_hit = 0; nodelimit = st_nodes + maxnodes;
      dfs(0);
      if (!found) { fails++; printf("CONTROL NOT FOUND: %s\n", line); }
      continue;
    }
    if (!parse_g6(line)) { fprintf(stderr, "bad graph6: %s\n", line); return 2; }
    snprintf(g6, sizeof g6, "%.200s", line);
    bfs();
    for (int e = 0; e < m; e++) eport[e][0] = eport[e][1] = -1;
    for (int v = 0; v < n; v++) assigned[v] = 0;
    long long s0 = st_surv, n0 = st_nodes;
    budget_hit = 0; nodelimit = st_nodes + maxnodes;
    dfs(0);
    budgets += budget_hit;
    printf("GRAPH %lld %s nodes %lld surv %lld%s\n", items, g6, st_nodes - n0, st_surv - s0,
           budget_hit ? " BUDGET" : "");
    fflush(stdout);
  }
  printf("TOTAL items %lld nodes %lld surv %lld prunes coinc %lld ab %lld finite %lld power %lld"
         " (relators %lld) fails %lld budget %lld climit %d leaf %d pw %d %d depth %d\n", items, st_nodes,
         st_surv, st_coinc, st_ab, st_fin, st_pw, st_pwrel, fails, budgets, climitNode, climitLeaf, pwL,
         pwK, pwD);
  return 0;
}
