/* Locally readable eigenvalues exp(2 pi i/n) of S = first return of a SMART-format machine to Y (rule a:
 * shape F with nonzero source, or shape H with nonzero target, at phase 2).  For each radius r, test whether
 * some chi: {radius-r windows} -> Z/n has chi(Sy) = chi(y)+1 along sampled orbits (offset union-find over
 * hashed windows).  'X' = contradiction (no such chi at radius r); 'ok' = none found.
 * usage: eigm N1,N2,.. RMAX NTAPES STEPS P0 SEED tok...   (tokens like F0:H1f, as in ycount) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define L 8000
#define HS (1<<22)
static int def[2][16], ns[2][16], nsym[2][16], nf[2][16], A = 0;
static unsigned char tp[L]; static int h, sh, dir, ph;
static const int MOVE_ = 0;
static int step(void) { if (ph == 2) { h += dir; ph = 1; return (h > 20 && h < L - 20); }
  int s = tp[h]; tp[h] = nsym[sh][s]; if (nf[sh][s]) dir = -dir; sh = ns[sh][s]; ph = 2; return 1; }
static int inY(void) { if (ph != 2) return 0; return (sh == 0 && tp[h]) || (sh == 1 && tp[h+dir]); }
/* union-find over (radius, n) keyed by window hash */
typedef struct { uint64_t key; int par, off, used; } Node;
static Node *tab[16][8]; static int bad[16][8];
static int getn(int r, int k, uint64_t key) { Node *T = tab[r][k]; uint64_t i = key & (HS-1);
  while (T[i].used && T[i].key != key) i = (i+1) & (HS-1);
  if (!T[i].used) { T[i].used = 1; T[i].key = key; T[i].par = (int)i; T[i].off = 0; } return (int)i; }
static int find(Node *T, int x, int n, int *o) { int acc = 0; while (T[x].par != x) { acc += T[x].off; x = T[x].par; } *o = acc % n; return x; }
int main(int argc, char **argv) {
  int ns_list[8], nn = 0; char *p = strtok(argv[1], ","); while (p) { ns_list[nn++] = atoi(p); p = strtok(0, ","); }
  int R = atoi(argv[2]), NT = atoi(argv[3]); long ST = atol(argv[4]); double p0 = atof(argv[5]); srand(atoi(argv[6]));
  for (int a = 7; a < argc; a++) { char *t = argv[a]; int s = t[0]=='H', i = t[1]-'0'; def[s][i] = 1; ns[s][i] = t[3]=='H'; nsym[s][i] = t[4]-'0'; nf[s][i] = t[5]=='f'; if (i+1 > A) A = i+1; if (nsym[s][i]+1 > A) A = nsym[s][i]+1; }
  for (int r = 0; r <= R; r++) for (int k = 0; k < nn; k++) tab[r][k] = calloc(HS, sizeof(Node));
  for (int tn = 0; tn < NT; tn++) {
    for (int i = 0; i < L; i++) tp[i] = ((double)rand()/RAND_MAX < p0) ? 0 : 1 + rand() % (A-1);
    h = L/2; sh = rand()%2; dir = (rand()%2) ? 1 : -1; ph = 2; int alive = 1;
    while (alive && !inY()) alive = step();
    uint64_t prev[16]; int have = 0;
    for (long st = 0; alive && st < ST; st++) {
      uint64_t cur[16]; for (int r = 0; r <= R; r++) { uint64_t x = (1469598103934665603ULL ^ (uint64_t)(sh*2 + (dir>0) + 7)) * 1099511628211ULL;
        for (int d = -r; d <= r; d++) { x ^= (uint64_t)(tp[h + d*dir] + 1) * 0x9E3779B97F4A7C15ULL; x *= 1099511628211ULL; x ^= x >> 29; } cur[r] = x ^ ((uint64_t)r << 56); }
      if (have) for (int r = 0; r <= R; r++) for (int k = 0; k < nn; k++) if (!bad[r][k]) {
        Node *T = tab[r][k]; int n = ns_list[k]; int a = getn(r,k,prev[r]), b = getn(r,k,cur[r]); int oa, ob;
        int ra = find(T, a, n, &oa), rb = find(T, b, n, &ob);
        if (ra == rb) { if (((ob - oa - 1) % n + n) % n) bad[r][k] = 1; }
        else { T[rb].par = ra; T[rb].off = ((oa + 1 - ob) % n + n) % n; } }
      if (getenv("DBG") && tn == 0 && st < 24) fprintf(stderr, "%c%c%d ", sh?'H':'F', dir>0?'>':'<', tp[h]);
      memcpy(prev, cur, sizeof cur); have = 1;
      do { alive = step(); } while (alive && !inY());
    }
  }
  for (int k = 0; k < nn; k++) { printf("n=%d:", ns_list[k]); for (int r = 0; r <= R; r++) printf(" r%d:%s", r, bad[r][k] ? "X" : "ok"); printf("\n"); }
  return 0;
}
