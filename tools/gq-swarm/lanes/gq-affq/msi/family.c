/* Guessed family M_m, m = 2j+1, alphabet 0..2j, shapes F=0, H=1 (SMART format, mirror-symmetric):
 *   F0 -> (1,H,flip);  F_i -> (i+1,H,flip) for 1<=i<=j-1;  F_j -> (0,F,noflip);
 *   H0 -> (2j,H,noflip);  F_i -> (i-1,H,flip) for j+2<=i<=2j;  F_{j+1} -> (0,H,flip);  H1 -> (1,F,flip).
 * Prints T(L) (first arrival at cell L+1 from F-right on s+ = 1) and checks T(L+1) = m T(L) + c, clean tape.
 * usage: family m LMAX */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  int m = atoi(argv[1]), L = atoi(argv[2]), j = (m-1)/2, A = m;
  int def[2][64] = {{0}}, ns[2][64], nsym[2][64], nf[2][64];
#define SET(s,i,sym,sh,f) (def[s][i]=1, nsym[s][i]=(sym), ns[s][i]=(sh), nf[s][i]=(f))
  SET(0,0,1,1,1); for (int i = 1; i <= j-1; i++) SET(0,i,i+1,1,1); SET(0,j,0,0,0);
  SET(1,0,2*j,1,0); for (int i = j+2; i <= 2*j; i++) SET(0,i,i-1,1,1); SET(0,j+1,0,1,1); SET(1,1,1,0,1);
  static unsigned char tape[1<<16]; memset(tape,0,sizeof tape); int off = 8, h = off, sh = 0, dir = 1, ph = 2, next = 1;
  tape[off] = 1; long t = 0, T[40]; int bad = 0;
  while (next <= L + 1 && t < 2000000000L) {
    if (ph == 2) { h += dir; ph = 1; t++; if (h < off) { bad = 1; break; }
      if (h == off + next) { int clean = tape[off] == 1; for (int i = 1; i < next; i++) if (tape[off+i]) clean = 0;
        if (!clean) { bad = 2; break; } T[next-1] = t; next++; } }
    else { int s = tape[h]; if (!def[sh][s]) { printf("undefined pair %c%d at t=%ld\n", sh?'H':'F', s, t); bad = 3; break; }
      tape[h] = nsym[sh][s]; if (nf[sh][s]) dir = -dir; sh = ns[sh][s]; ph = 2; t++; }
  }
  printf("m=%d bad=%d T:", m, bad); for (int i = 0; i < next-1; i++) printf(" %ld", T[i]);
  if (next-1 >= 3) { long c = T[next-2] - m*T[next-3]; int ok = 1; for (int i = 1; i+1 < next-1; i++) if (T[i+1] != m*T[i] + c) ok = 0;
    printf("  exact T(L+1)=%d*T(L)+%ld: %s", m, c, ok ? "YES" : "no"); }
  printf("\n"); return 0;
}
