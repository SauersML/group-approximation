/* Per-local-type step counts inside the level-L crossings of a NON-mirror machine (state = shape x dir).
 * Table tokens: S s > s' v f  as in even_dfs output, e.g. F0>H0 F1>H1f ... where the source letter is
 * F,H,K,L = (shape0,left),(shape0,right),(shape1,left),(shape1,right); target letter F/H = shape0/shape1;
 * 'f' = flip relative to the current direction.  Types: phase-2 steps keyed by (state, source symbol, target symbol).
 * For each type prints counts at the first arrivals L = 0..LMAX and the exact fit  a*2^L + b*(-1)^L + c*L + d
 * over L = LMAX-3..LMAX (checked at LMAX-4); also the longest run of consecutive phase-2 steps of one type.
 * usage: types LMAX SP tok...  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define A 4
int main(int argc, char **argv) {
  int L = atoi(argv[1]), sp = atoi(argv[2]); int def[4][A] = {{0}}, osh[4][A], osy[4][A], ofl[4][A];
  for (int a = 3; a < argc; a++) { char *t = argv[a]; int st = strchr("FHKL", t[0]) - "FHKL", s = t[1]-'0';
    def[st][s] = 1; osh[st][s] = t[3]=='H'; osy[st][s] = t[4]-'0'; ofl[st][s] = t[5]=='f'; }
  static unsigned char tp[1<<18]; memset(tp, 0, sizeof tp); int off = 16, h = off, sh = 0, dir = 1, ph = 2, next = 1;
  tp[off] = sp; static long cnt[64][32]; long cur[64] = {0}; int nT = 4*A*A; long run = 0, maxrun[64] = {0}; int lastty = -1;
  while (next <= L + 1) {
    if (ph == 2) { int st = sh*2 + (dir > 0), ty = (st*A + tp[h])*A + tp[h+dir]; cur[ty]++;
      if (ty == lastty) run++; else run = 1; lastty = ty; if (run > maxrun[ty]) maxrun[ty] = run;
      h += dir; ph = 1; if (h < off) { printf("left of 0\n"); return 1; }
      if (h == off + next) { for (int t = 0; t < nT; t++) cnt[t][next-1] = cur[t]; next++; } }
    else { int st = sh*2 + (dir > 0), s = tp[h]; if (!def[st][s]) { printf("undefined %c%d\n", "FHKL"[st], s); return 1; }
      tp[h] = osy[st][s]; if (ofl[st][s]) dir = -dir; sh = osh[st][s]; ph = 2; }
  }
  printf("type: counts L=0..%d | fit a b c d (check) | maxrun\n", L);
  for (int t = 0; t < nT; t++) { int any = 0; for (int l = 0; l <= L; l++) if (cnt[t][l]) any = 1; if (!any) continue;
    int st = t / (A*A), src = (t / A) % A, dst = t % A; printf("%c src%d dst%d:", "FHKL"[st], src, dst);
    for (int l = 0; l <= L; l++) printf(" %ld", cnt[t][l]);
    /* solve 4x4 for a,b,c,d on L-3..L using doubles */
    double M[4][5]; for (int i = 0; i < 4; i++) { int l = L - 3 + i; M[i][0] = (double)(1L << l); M[i][1] = (l % 2) ? -1 : 1; M[i][2] = l; M[i][3] = 1; M[i][4] = cnt[t][l]; }
    for (int c = 0; c < 4; c++) { int p = c; for (int r = c; r < 4; r++) if (M[r][c]*M[r][c] > M[p][c]*M[p][c]) p = r;
      for (int k = 0; k < 5; k++) { double x = M[c][k]; M[c][k] = M[p][k]; M[p][k] = x; }
      for (int r = 0; r < 4; r++) if (r != c) { double f = M[r][c] / M[c][c]; for (int k = 0; k < 5; k++) M[r][k] -= f*M[c][k]; } }
    double a = M[0][4]/M[0][0], b = M[1][4]/M[1][1], c = M[2][4]/M[2][2], d = M[3][4]/M[3][3]; int l = L - 4;
    double pred = a*(double)(1L << l) + b*((l % 2) ? -1 : 1) + c*l + d;
    printf(" | %.3f %.3f %.3f %.3f (%s) | %ld\n", a, b, c, d, (pred - cnt[t][l])*(pred - cnt[t][l]) < 1e-6 ? "ok" : "FIT FAILS", maxrun[t]);
  }
  return 0;
}
