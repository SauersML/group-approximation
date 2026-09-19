/* Lazy DFS over SMART-format reversible machines (NS shapes, A symbols, mirror-symmetric):
 * a table entry (shape,sym)->(shape',sym',flip) is chosen only when the crossing run first reads that pair,
 * keeping the partial map injective (so every completion is reversible).  Run: start (shape 0, right,
 * phase 2) on cell 0 = s+ (fixed nonzero symbol SP), zeros elsewhere; T(L) = first arrival at cell L+1;
 * prune if the head goes left of cell 0, a restored-tape check fails at an arrival, or no new cell is reached
 * within 25*T(last)+200 steps.  Report partial tables reaching level LMAX with T(L+1) = b T(L) + c on the last
 * 4 levels.  usage: branch_dfs NS A LMAX SP   (env SKIP3=1 to print only b != 3) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MP 32
#define TP 96
static int NS, A, LMAX, SP, NP, skip3;
static int def[MP], os[MP], osym[MP], of[MP], usedout[MP];
static long nodes = 0, reports = 0, hist[64];

typedef struct { unsigned char tape[TP]; int h, shape, dir, phase, next; long t, lastT, T[24]; } Sim;

static void finish(Sim *s) {
  int n = s->next - 1; if (n < 6) return; int L0 = n - 5;
  long b = s->T[L0+1] / (s->T[L0] ? s->T[L0] : 1); if (b < 2) return; long c = s->T[L0+1] - b*s->T[L0];
  for (int L = L0; L + 1 < n; L++) if (s->T[L+1] != b*s->T[L] + c) return;
  if (b < 64) hist[b]++; reports++;
  if (skip3 && b == 3) return;
  printf("b=%ld c=%ld T:", b, c); for (int i = 0; i < n; i++) printf(" %ld", s->T[i]);
  printf("  table:"); for (int k = 0; k < NP; k++) if (def[k]) printf(" %c%d>%c%d%s", "FHKLMNOP"[k/A], k%A, "FHKLMNOP"[os[k]], osym[k], of[k]?"f":"");
  printf("\n"); fflush(stdout);
}

static void run(Sim *s) {
  nodes++;
  const int off = 8;
  for (;;) {
    if (s->t > 25*s->lastT + 200) return;
    if (s->phase == 2) { s->h += s->dir; s->phase = 1; s->t++;
      if (s->h < off || s->h >= TP - 2) return;
      if (s->h == off + s->next) {
        if (s->tape[off] != SP) return;
        for (int i = 1; i < s->next; i++) if (s->tape[off+i]) return;
        s->T[s->next-1] = s->t; s->lastT = s->t;
        if (s->next == LMAX + 1) { s->next++; finish(s); return; }
        s->next++;
      }
    } else {
      int k = s->shape*A + s->tape[s->h];
      if (!def[k]) {                       /* branch over every unused output and both flips */
        for (int v = 0; v < NP; v++) if (!usedout[v]) for (int f = 0; f < 2; f++) {
          def[k] = 1; os[k] = v / A; osym[k] = v % A; of[k] = f; usedout[v] = 1;
          Sim c = *s; run(&c);
          def[k] = 0; usedout[v] = 0;
        }
        return;
      }
      s->tape[s->h] = osym[k]; if (of[k]) s->dir = -s->dir; s->shape = os[k]; s->phase = 2; s->t++;
    }
  }
}

int main(int argc, char **argv) {
  NS = atoi(argv[1]); A = atoi(argv[2]); LMAX = atoi(argv[3]); SP = atoi(argv[4]); NP = NS*A; skip3 = getenv("SKIP3") != 0;
  Sim s; memset(&s, 0, sizeof s); s.h = 8; s.tape[8] = SP; s.shape = 0; s.dir = 1; s.phase = 2; s.next = 1; s.lastT = 1;
  run(&s);
  printf("NS=%d A=%d LMAX=%d SP=%d nodes=%ld reports=%ld hist:", NS, A, LMAX, SP, nodes, reports);
  for (int b = 2; b < 64; b++) if (hist[b]) printf(" b%d:%ld", b, hist[b]); printf("\n"); return 0;
}
