/* Non-mirror machines: 4 states F,H,K,L = (shape0,left),(shape0,right),(shape1,left),(shape1,right);
 * tokens Xs:Tv[f] as in types.c; Y = set of phase-2 types "Xsd" (state, source symbol, target symbol).
 * (1) bounded return on random tapes: max number of phase-2 steps between consecutive Y-steps;
 * (2) locally readable eigenvalues exp(2 pi i/n) of S (first return to Y), radius 0..RMAX, direction-relative
 *     windows, offset union-find.   usage: eig2 N1,N2,.. RMAX NTAPES STEPS P0 "Ytypes" tok...   */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define LT 8000
#define HS (1<<21)
static int osh[4][8], osy[4][8], ofl[4][8], Ys[4][8][8], A = 2;
static unsigned char tp[LT]; static int h, st, ph;
static int dirof(int s) { return (s % 2) ? 1 : -1; }
static int step(void) { if (ph == 2) { h += dirof(st); ph = 1; return (h > 20 && h < LT - 20); }
  int s = tp[h], d = dirof(st); tp[h] = osy[st][s]; int nd = ofl[st][s] ? -d : d; st = osh[st][s]*2 + (nd > 0); ph = 2; return 1; }
static int inY(void) { return ph == 2 && Ys[st][tp[h]][tp[h + dirof(st)]]; }
typedef struct { uint64_t k; int used, par, off; } Node; static Node *tab[12][8]; static int bad[12][8];
static uint64_t mix(uint64_t x) { x ^= x >> 31; x *= 0x9E3779B97F4A7C15ULL; x ^= x >> 29; return x; }
static int getn(int r, int k, uint64_t key) { Node *T = tab[r][k]; uint64_t i = key & (HS-1); while (T[i].used && T[i].k != key) i = (i+1) & (HS-1);
  if (!T[i].used) { T[i].used = 1; T[i].k = key; T[i].par = (int)i; T[i].off = 0; } return (int)i; }
static int find(Node *T, int x, int n, int *o) { int a = 0; while (T[x].par != x) { a += T[x].off; x = T[x].par; } *o = a % n; return x; }
int main(int argc, char **argv) {
  int nl[8], nn = 0; char *p = strtok(argv[1], ","); while (p) { nl[nn++] = atoi(p); p = strtok(0, ","); }
  int R = atoi(argv[2]), NT = atoi(argv[3]); long ST = atol(argv[4]); double p0 = atof(argv[5]); char *ys = argv[6]; srand(3);
  for (char *q = ys; *q; ) { while (*q == ' ') q++; if (!*q) break; int s = strchr("FHKL", q[0]) - "FHKL"; Ys[s][q[1]-'0'][q[2]-'0'] = 1; q += 3; }
  for (int a = 7; a < argc; a++) { char *t = argv[a]; int s = strchr("FHKL", t[0]) - "FHKL", sy = t[1]-'0'; osh[s][sy] = t[3]=='H'; osy[s][sy] = t[4]-'0'; ofl[s][sy] = t[5]=='f'; if (sy+1 > A) A = sy+1; if (osy[s][sy]+1 > A) A = osy[s][sy]+1; }
  for (int r = 0; r <= R; r++) for (int k = 0; k < nn; k++) tab[r][k] = calloc(HS, sizeof(Node));
  long maxgap = 0, gapsum = 0, ny = 0;
  for (int tn = 0; tn < NT; tn++) {
    for (int i = 0; i < LT; i++) tp[i] = ((double)rand()/RAND_MAX < p0) ? 0 : 1 + rand() % (A-1);
    h = LT/2; st = rand() % 4; ph = 2; int alive = 1; long g = 0;
    while (alive && !inY()) { alive = step(); if (ph == 2 && ++g > 100000) { printf("no Y within 1e5 steps\n"); return 0; } }
    uint64_t prev[12]; int have = 0;
    for (long s2 = 0; alive && s2 < ST; s2++) {
      uint64_t cur[12]; int d = dirof(st);
      for (int r = 0; r <= R; r++) { uint64_t x = mix(100 + st); for (int dd = -r; dd <= r; dd++) x = mix(x ^ (uint64_t)(tp[h + dd*d] + 1) * 0x100000001B3ULL); cur[r] = x; }
      if (have) for (int r = 0; r <= R; r++) for (int k = 0; k < nn; k++) if (!bad[r][k]) { Node *T = tab[r][k]; int n = nl[k], oa, ob;
        int a = getn(r,k,prev[r]), b = getn(r,k,cur[r]); int ra = find(T,a,n,&oa), rb = find(T,b,n,&ob);
        if (ra == rb) { if (((ob - oa - 1) % n + n) % n) bad[r][k] = 1; } else { T[rb].par = ra; T[rb].off = ((oa + 1 - ob) % n + n) % n; } }
      memcpy(prev, cur, sizeof cur); have = 1;
      long gap = 0; do { alive = step(); if (ph == 2) gap++; } while (alive && !inY());
      if (alive) { if (gap > maxgap) maxgap = gap; gapsum += gap; ny++; }
    }
  }
  printf("Y-steps %ld, mean gap %.3f, max gap %ld (phase-2 steps)\n", ny, ny ? (double)gapsum/ny : 0, maxgap);
  for (int k = 0; k < nn; k++) { printf("n=%d:", nl[k]); for (int r = 0; r <= R; r++) printf(" r%d:%s", r, bad[r][k] ? "X" : "ok"); printf("\n"); }
  return 0;
}
