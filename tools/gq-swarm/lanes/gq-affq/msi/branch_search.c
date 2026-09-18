/* Exhaustive search: 2-shape (F=0,H=1), mirror-symmetric reversible moving-head machines on A symbols
 * in SMART's format.  Phase 2: move by dir.  Phase 1: (shape,sym) -> (shape',sym') by a permutation pi of the
 * 2A pairs, and dir flips iff flip[shape][sym].  Every such table is reversible.
 * Crossing test (SMART's M_b(k)): start (F, right, phase 2) on cell 0 holding s+ != 0, zeros elsewhere.
 * T(L) = time of first arrival of the head at cell L+1.  Require: head never left of cell 0, and at arrival
 * cells 0..L are restored (cell 0 = s+, cells 1..L = 0).  Report tables whose T satisfies
 * T(L+1) = b*T(L) + c for L = LMIN..LMAX-1 with the same integers b >= 2, c.
 * Calibration: SMART (A=3) must be reported with b = 3, c = 4.
 * usage: branch_search A LMAX [smart]  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXA 12
#define TAPE 4096
static int A, LMAX, NP, NS = 2;
static int pi_s[2*MAXA], pi_sym[2*MAXA], flp[2*MAXA];
static unsigned char tape[TAPE];

static long crossing(int splus, long *T) { /* returns number of levels measured cleanly */
  memset(tape, 0, TAPE); int off = 8, h = off, shape = 0, dir = 1, phase = 2; tape[h] = splus;
  long t = 0, cap = 40000000L, lastT = 1; int next = 1; /* waiting for first arrival at off+next */
  while (t < cap) {
    if (t > 25*lastT + 200) return next - 1; /* no new cell for too long: bounded loop or slow walk */
    if (phase == 2) { h += dir; phase = 1; t++;
      if (h < off) return next - 1;
      if (h >= TAPE - 2) return next - 1;
      if (h == off + next) {
        if (tape[off] != splus) return next - 1;
        for (int i = 1; i < next; i++) if (tape[off+i]) return next - 1;
        T[next-1] = t; lastT = t; if (next == LMAX + 1) return next; next++;
      }
    } else { int k = shape*A + tape[h]; tape[h] = pi_sym[k]; if (flp[k]) dir = -dir; shape = pi_s[k]; phase = 2; t++; }
  }
  return next - 1;
}

static void report(long *T, int n, int splus, int b, long c) {
  printf("b=%d c=%ld s+=%d  T:", b, c, splus); for (int i = 0; i < n; i++) printf(" %ld", T[i]);
  printf("  table:"); for (int k = 0; k < NP; k++) printf(" %c%d>%c%d%s", "FHKLM"[k/A], k%A, "FHKLM"[pi_s[k]], pi_sym[k], flp[k]?"f":"");
  printf("\n"); fflush(stdout);
}

static long found = 0, tested = 0;
static void test_table(void) {
  tested++; long T[32];
  for (int sp = 1; sp < A; sp++) {
    int n = (int)crossing(sp, T); if (n < 5) continue;
    int L0 = n - 4; long b = T[L0+1] / (T[L0] ? T[L0] : 1); if (b < 2) continue;
    long c = T[L0+1] - b*T[L0]; int ok = 1;
    for (int L = L0; L + 1 < n; L++) if (T[L+1] != b*T[L] + c) { ok = 0; break; }
    if (ok) { found++; report(T, n, sp, (int)b, c); }
  }
}

static int perm[2*MAXA], used[2*MAXA];
static void rec(int k) {
  if (k == NP) { for (int f = 0; f < (1 << NP); f++) { for (int j = 0; j < NP; j++) flp[j] = (f >> j) & 1; test_table(); } return; }
  for (int v = 0; v < NP; v++) if (!used[v]) { used[v] = 1; pi_s[k] = v / A; pi_sym[k] = v % A; rec(k+1); used[v] = 0; }
}

int main(int argc, char **argv) {
  A = atoi(argv[1]); LMAX = atoi(argv[2]); if (getenv("NS")) NS = atoi(getenv("NS")); NP = NS*A;
  if (argc > 3) { /* SMART calibration, A = 3 */
    int S[6][3] = {{0,1,1},{1,1,1},{1,2,1},{0,2,0},{0,0,0},{1,0,1}}; /* F0 F1 F2 H0 H1 H2 -> shape',sym',flip */
    for (int k = 0; k < 6; k++) { pi_s[k] = S[k][0]; pi_sym[k] = S[k][1]; flp[k] = S[k][2]; }
    test_table(); printf("calibration done, found %ld\n", found); return 0;
  }
  rec(0); printf("A=%d LMAX=%d tested %ld tables, reported %ld\n", A, LMAX, tested, found); return 0;
}
