/* Count candidate "genuine level-0 move" steps inside the level-L crossings of a SMART-format machine.
 * Table given as DFS-format tokens, e.g.  F0>F2f F1>H2f ...  (shapes F,H; 'f' = flip).
 * Y rule a: phase-2 step with shape F whose source cell is nonzero, or shape H whose target cell is nonzero.
 * Y rule b: the same with F and H swapped.  Prints T(L) and N_a(L), N_b(L) at each first arrival.
 * usage: ycount LMAX SPLUS tok1 tok2 ...  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  int L = atoi(argv[1]), sp = atoi(argv[2]); int def[2][16] = {{0}}, ns[2][16], nsym[2][16], nf[2][16];
  for (int a = 3; a < argc; a++) { char *t = argv[a]; int s = t[0]=='H', i = t[1]-'0', s2 = t[3]=='H', sy = t[4]-'0', f = t[5]=='f';
    def[s][i] = 1; ns[s][i] = s2; nsym[s][i] = sy; nf[s][i] = f; }
  static unsigned char tape[1<<16]; memset(tape, 0, sizeof tape); int off = 8, h = off, sh = 0, dir = 1, ph = 2, next = 1;
  tape[off] = sp; long t = 0, na = 0, nb = 0;
  printf("L T Na Nb\n");
  while (next <= L + 1) {
    if (ph == 2) { int src = tape[h], dst = tape[h+dir];
      if ((sh == 0 && src) || (sh == 1 && dst)) na++;
      if ((sh == 1 && src) || (sh == 0 && dst)) nb++;
      h += dir; ph = 1; t++; if (h < off) { printf("left of 0\n"); return 1; }
      if (h == off + next) { printf("%d %ld %ld %ld\n", next-1, t, na, nb); next++; } }
    else { int s = tape[h]; if (!def[sh][s]) { printf("undefined %c%d\n", sh?'H':'F', s); return 1; }
      tape[h] = nsym[sh][s]; if (nf[sh][s]) dir = -dir; sh = ns[sh][s]; ph = 2; t++; }
  }
  return 0;
}
