/* For a non-mirror machine (tokens as in types.c), search all subsets Y of the used phase-2 local types
 * (state, source symbol, target symbol) for: (i) N_Y(L) = K * 2^L exactly for L = L0..LMAX (K rational, fixed);
 * (ii) bounded return: the maximal gap between consecutive Y-steps up to level LMAX-3 equals the one up to LMAX.
 * Prints each good subset (types listed) with K*2^L0 and the gap.  usage: ysubsets LMAX L0 SP tok... */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define A 6
int main(int argc, char **argv) {
  int L = atoi(argv[1]), L0 = atoi(argv[2]), sp = atoi(argv[3]); int B = getenv("B") ? atoi(getenv("B")) : 2; int def[4][A] = {{0}}, osh[4][A], osy[4][A], ofl[4][A];
  for (int a = 4; a < argc; a++) { char *t = argv[a]; int st = strchr("FHKL", t[0]) - "FHKL", s = t[1]-'0';
    def[st][s] = 1; osh[st][s] = t[3]=='H'; osy[st][s] = t[4]-'0'; ofl[st][s] = t[5]=='f'; }
  static unsigned char tp[1<<18]; memset(tp, 0, sizeof tp); int off = 16, h = off, sh = 0, dir = 1, ph = 2, next = 1;
  tp[off] = sp; int nT = 4*A*A; static unsigned char seq[1<<24]; long n = 0, arr[40]; int used[64] = {0};
  while (next <= L + 1) {
    if (ph == 2) { int st = sh*2 + (dir > 0), ty = (st*A + tp[h])*A + tp[h+dir]; seq[n++] = ty; used[ty] = 1;
      h += dir; ph = 1; if (h < off) { printf("left of 0\n"); return 1; } if (h == off + next) { arr[next-1] = n; next++; } }
    else { int st = sh*2 + (dir > 0), s = tp[h]; if (!def[st][s]) { printf("undefined\n"); return 1; }
      tp[h] = osy[st][s]; if (ofl[st][s]) dir = -dir; sh = osh[st][s]; ph = 2; }
  }
  int idx[64], k = 0; for (int t = 0; t < nT; t++) if (used[t]) idx[k++] = t;
  printf("%d used types, run length %ld\n", k, n); long good = 0; if (k > 20) { printf("too many types for subset search\n"); return 0; }
  for (long mask = 1; mask < (1L << k); mask++) {
    int inY[64] = {0}; for (int i = 0; i < k; i++) if (mask >> i & 1) inY[idx[i]] = 1;
    long cnt = 0, lastY = -1, gap = 0, gapEarly = 0; long NY[40]; int lv = 0;
    for (long i = 0; i < n; i++) { if (inY[seq[i]]) { cnt++; if (lastY >= 0 && i - lastY > gap) gap = i - lastY; lastY = i; }
      while (lv <= L && i + 1 == arr[lv]) { NY[lv] = cnt; if (lv == L - 3) gapEarly = gap; lv++; } }
    int ok = 1; for (int l = L0; l < L; l++) if (NY[l+1] != B*NY[l]) { ok = 0; break; }
    if (!ok || gap != gapEarly || NY[L0] == 0) continue;
    good++; if (good <= 12) { printf("Y:"); for (int i = 0; i < k; i++) if (mask >> i & 1) { int t = idx[i]; printf(" %c%d%d", "FHKL"[t/(A*A)], (t/A)%A, t%A); }
      printf("  N_Y(L0)=%ld  maxgap=%ld\n", NY[L0], gap); }
  }
  printf("good subsets: %ld\n", good); return 0;
}
