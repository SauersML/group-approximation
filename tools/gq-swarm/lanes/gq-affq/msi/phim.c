/* Search for a brick-local height-m renormalization of S (first return to Y, rule a) for a SMART-format
 * machine.  Steps: (1) learn chi: radius-1 windows -> Z/m with chi(Sy) = chi(y)+1 (offset union-find);
 * (2) for each residue a, A = chi^{-1}(a); for A-points y collect the edit pairs (e,e') with
 *     S(e(y)) == e'(S^m y) (hash of state + tape within +-W of the head, W = 600);
 *     edit = (delete none or one cell at dir-relative offset -2..2) x (head shift -2..2) x (shape) x (dir flip);
 * (3) constraint-propagate a rule key(y) -> edit over radius-RK windows; (4) validate on fresh orbits.
 * usage: phim m RK NTRAIN NVAL tok...   */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define NL 3000
#define W 600
#define NE 120
typedef struct { unsigned char t[NL]; int h, sh, dir; } Cfg;
static int nsh_[2][16], nsym_[2][16], nf_[2][16], A = 0, M, RK;
static int inY(Cfg *c) { return (c->sh == 0 && c->t[c->h]) || (c->sh == 1 && c->t[c->h + c->dir]); }
static int S(Cfg *c) { /* phase-2 Y config -> next Y config; 0 if near edge */
  for (;;) { c->h += c->dir; if (c->h < W + 10 || c->h > NL - W - 10) return 0;
    int s = c->t[c->h]; c->t[c->h] = nsym_[c->sh][s]; if (nf_[c->sh][s]) c->dir = -c->dir; c->sh = nsh_[c->sh][s];
    if (inY(c)) return 1; } }
static uint64_t mix(uint64_t x) { x ^= x >> 31; x *= 0x9E3779B97F4A7C15ULL; x ^= x >> 29; return x; }
static uint64_t key(Cfg *c, int r) { uint64_t x = mix(1000 + c->sh*2 + (c->dir > 0));
  for (int d = -r; d <= r; d++) x = mix(x ^ (uint64_t)(c->t[c->h + d*c->dir] + 1) * 0x100000001B3ULL); return x; }
static int edit(Cfg *in, int e, Cfg *out) { /* returns 1 if valid and in Y */
  int del = e % 6, hs = (e / 6) % 5 - 2, nsh = (e / 30) % 2, fl = (e / 60) % 2;
  *out = *in; int h = in->h;
  if (del < 5) { int p = h + (del - 2) * in->dir; memmove(out->t + p, in->t + p + 1, NL - p - 1); out->t[NL-1] = 0; if (p < h) h--; }
  out->h = h + hs * in->dir; out->sh = nsh; out->dir = fl ? -in->dir : in->dir; return inY(out); }
/* hash map for union-find and rule tables */
#define HS (1<<20)
typedef struct { uint64_t k; int used, par, off; uint64_t c0, c1; int seen; unsigned char win[12]; } Ent;
static Ent *UF, *RT;
static int slot(Ent *T, uint64_t k) { uint64_t i = k & (HS-1); while (T[i].used && T[i].k != k) i = (i+1) & (HS-1);
  if (!T[i].used) { T[i].used = 1; T[i].k = k; T[i].par = (int)i; T[i].off = 0; T[i].c0 = ~0ULL; T[i].c1 = ~0ULL; T[i].seen = 0; } return (int)i; }
static int find(int x, int *o) { int a = 0; while (UF[x].par != x) { a += UF[x].off; x = UF[x].par; } *o = a % M; return x; }
static void rnd(Cfg *c, double p0) { for (int i = 0; i < NL; i++) c->t[i] = ((double)rand()/RAND_MAX < p0) ? 0 : 1 + rand() % (A-1);
  c->h = NL/2; c->sh = rand()%2; c->dir = rand()%2 ? 1 : -1; for (int k = 0; k < 400 && !inY(c); k++) { /* step once in phase 1/2 */
    c->h += c->dir; int s = c->t[c->h]; c->t[c->h] = nsym_[c->sh][s]; if (nf_[c->sh][s]) c->dir = -c->dir; c->sh = nsh_[c->sh][s]; } }
static int chi(Cfg *c) { int o; int i = slot(UF, key(c, 1)); find(i, &o); return o; }
typedef struct { uint64_t k1, k2; uint64_t ok[NE][2]; } Pt;   /* ok[e] = bitset of e' */
int main(int argc, char **argv) {
  M = atoi(argv[1]); RK = atoi(argv[2]); int NT = atoi(argv[3]), NV = atoi(argv[4]); srand(7);
  for (int a = 5; a < argc; a++) { char *t = argv[a]; int s = t[0]=='H', i = t[1]-'0'; nsh_[s][i] = t[3]=='H'; nsym_[s][i] = t[4]-'0'; nf_[s][i] = t[5]=='f'; if (i+1 > A) A = i+1; }
  UF = calloc(HS, sizeof(Ent)); RT = calloc(HS, sizeof(Ent)); static Cfg c, d, e1, e2, z;
  /* (1) chi */
  int NCH = getenv("NCH") ? atoi(getenv("NCH")) : 60;
  for (int n = 0; n < NCH; n++) { rnd(&c, n % 3 == 0 ? 0.4 : (n % 3 == 1 ? 0.7 : 0.9)); if (!inY(&c)) continue;
    for (int st = 0; st < 6000; st++) { int a = slot(UF, key(&c, 1)); if (!S(&c)) break; int b = slot(UF, key(&c, 1)); int oa, ob;
      int ra = find(a, &oa), rb = find(b, &ob); if (ra != rb) { UF[rb].par = ra; UF[rb].off = ((oa + 1 - ob) % M + M) % M; }
      else if (((ob - oa - 1) % M + M) % M) { printf("chi inconsistent at radius 1\n"); return 1; } } }
  int roots = 0; for (int i = 0; i < HS; i++) if (UF[i].used && UF[i].par == i) roots++;
  printf("chi learned; components %d\n", roots);
  Pt *P = malloc(sizeof(Pt) * NT);
  for (int res = 0; res < M; res++) {
    memset(RT, 0, sizeof(Ent) * HS); int np = 0;
    for (int n = 0; np < NT && n < 100000; n++) { rnd(&c, n % 3 == 0 ? 0.4 : (n % 3 == 1 ? 0.7 : 0.9)); if (!inY(&c)) continue;
      int alive = 1; for (int b = rand() % 500; b > 0 && alive; b--) alive = S(&c);
      while (alive && chi(&c) != res) alive = S(&c);
      for (int rep = 0; rep < 8 && alive && np < NT; rep++) {
        d = c; for (int k = 0; k < M && alive; k++) alive = S(&d); if (!alive) break;
        Pt *p = &P[np]; p->k1 = key(&c, RK); p->k2 = key(&d, RK);
        { Ent *q = &RT[slot(RT, p->k1)]; q->win[0] = c.sh*2 + (c.dir>0); for (int dd = -RK; dd <= RK; dd++) q->win[1+dd+RK] = c.t[c.h + dd*c.dir]; q->seen = 1; } memset(p->ok, 0, sizeof p->ok);
        uint64_t L[NE], R[NE]; int vL[NE], vR[NE];
        for (int e = 0; e < NE; e++) { vL[e] = edit(&c, e, &e1) && S(&e1); if (vL[e]) L[e] = key(&e1, W - 20);
          vR[e] = edit(&d, e, &e2); if (vR[e]) R[e] = key(&e2, W - 20); }
        int any = 0; for (int e = 0; e < NE; e++) if (vL[e]) for (int f = 0; f < NE; f++) if (vR[f] && L[e] == R[f]) { p->ok[e][f/64] |= 1ULL << (f%64); any = 1; }
        if (any) np++; else { np = -1; break; }
        c = d; }
      if (np < 0) break; }
    if (np < 0) { printf("res %d: some A-point has no matching edit pair -> no rule in the class\n", res); continue; }
    /* (3) propagate */
    for (int i = 0; i < np; i++) { slot(RT, P[i].k1); slot(RT, P[i].k2); }
    int changed = 1, rounds = 0;
    while (changed && rounds < 200) { changed = 0; rounds++;
      for (int i = 0; i < np; i++) { Ent *a = &RT[slot(RT, P[i].k1)], *b = &RT[slot(RT, P[i].k2)]; uint64_t ga0 = 0, ga1 = 0, gb0 = 0, gb1 = 0;
        for (int e = 0; e < NE; e++) if ((e < 64 ? a->c0 >> e : a->c1 >> (e-64)) & 1) {
          uint64_t m0 = P[i].ok[e][0] & b->c0, m1 = P[i].ok[e][1] & b->c1;
          if (m0 | m1) { if (e < 64) ga0 |= 1ULL << e; else ga1 |= 1ULL << (e-64); gb0 |= m0; gb1 |= m1; } }
        if ((a->c0 & ~ga0) | (a->c1 & ~ga1)) { a->c0 &= ga0; a->c1 &= ga1; changed = 1; }
        if ((b->c0 & ~gb0) | (b->c1 & ~gb1)) { b->c0 &= gb0; b->c1 &= gb1; changed = 1; } } }
    int keys = 0, empty = 0; for (int i = 0; i < HS; i++) if (RT[i].used) { keys++; if (!(RT[i].c0 | RT[i].c1)) empty++; }
    printf("res %d: %d pts, %d keys, %d empty after %d rounds", res, np, keys, empty, rounds);
    if (empty) { printf("\n"); continue; }
    /* (4) validate with rule = lowest edit */
    long ok = 0, bad = 0, unseen = 0;
    for (int n = 0; n < NV; n++) { rnd(&c, (n % 4) * 0.2 + 0.3); if (!inY(&c)) continue; int alive = 1;
      for (int b = rand() % 800; b > 0 && alive; b--) alive = S(&c); while (alive && chi(&c) != res) alive = S(&c);
      for (int rep = 0; rep < 30 && alive; rep++) { d = c; for (int k = 0; k < M && alive; k++) alive = S(&d); if (!alive) break;
        uint64_t k1 = key(&c, RK), k2 = key(&d, RK); uint64_t i1 = k1 & (HS-1), i2;
        while (RT[i1].used && RT[i1].k != k1) i1 = (i1+1) & (HS-1); i2 = k2 & (HS-1); while (RT[i2].used && RT[i2].k != k2) i2 = (i2+1) & (HS-1);
        if (!RT[i1].used || !RT[i2].used) { unseen++; c = d; continue; }
        int ea = RT[i1].c0 ? __builtin_ctzll(RT[i1].c0) : 64 + __builtin_ctzll(RT[i1].c1);
        int eb = RT[i2].c0 ? __builtin_ctzll(RT[i2].c0) : 64 + __builtin_ctzll(RT[i2].c1);
        if (edit(&c, ea, &e1) && S(&e1) && edit(&d, eb, &e2) && key(&e1, W-20) == key(&e2, W-20)) ok++; else bad++;
        c = d; } }
    printf(" | validation ok %ld bad %ld unseen %ld\n", ok, bad, unseen); fflush(stdout);
    if (getenv("DUMP") && res == atoi(getenv("DUMP"))) { int cnt[NE] = {0}; for (int i = 0; i < HS; i++) if (RT[i].used && RT[i].seen) { int e = RT[i].c0 ? __builtin_ctzll(RT[i].c0) : 64 + __builtin_ctzll(RT[i].c1); cnt[e]++; if (cnt[e] <= 3) { printf("  e=%d del=%d hs=%d sh=%c fl=%d  win %c%c ", e, e%6-2, (e/6)%5-2, (e/30)%2?'H':'F', (e/60)%2, RT[i].win[0]/2?'H':'F', RT[i].win[0]%2?'>':'<'); for (int dd = 0; dd < 2*RK+1; dd++) printf("%d", RT[i].win[1+dd]); printf("\n"); } } for (int e = 0; e < NE; e++) if (cnt[e]) printf("  edit %d used by %d A-windows\n", e, cnt[e]); }
  }
  return 0;
}
