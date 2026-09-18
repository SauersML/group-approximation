/* Head drift of non-mirror machines on random tapes: for each table (stdin, one per line, tokens as in
 * even_dfs), NR tapes, report median over tapes of |h(t)-h(0)| at t = 1e4, 1e5, 1e6 (ballistic ~ t, SMART-like
 * ~ log t or small).  usage: drift NR P0 < tables */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define LT 3000000
static int def[4][8], osh[4][8], osy[4][8], ofl[4][8], A; static unsigned char tp[LT];
static int cmp(const void *a, const void *b) { long x = *(long*)a, y = *(long*)b; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
  int NR = atoi(argv[1]); double p0 = atof(argv[2]); char line[4096]; srand(5); int nt = 0;
  while (fgets(line, sizeof line, stdin)) { memset(def, 0, sizeof def); A = 2; char orig[4096]; strcpy(orig, line); orig[strcspn(orig, "\n")] = 0;
    for (char *q = strtok(line, " \n"); q; q = strtok(0, " \n")) { int s = strchr("FHKL", q[0]) - "FHKL", sy = q[1]-'0';
      def[s][sy] = 1; osh[s][sy] = q[3]=='H'; osy[s][sy] = q[4]-'0'; ofl[s][sy] = q[5]=='f'; if (sy+1 > A) A = sy+1; if (osy[s][sy]+1 > A) A = osy[s][sy]+1; }
    long D[3][64]; int nd = 0;
    for (int r = 0; r < NR; r++) { for (long i = 0; i < LT; i++) tp[i] = ((double)rand()/RAND_MAX < p0) ? 0 : 1 + rand() % (A-1);
      long h = LT/2, h0 = h; int st = rand() % 4, ph = 2, ok = 1; long mark[3] = {10000, 100000, 1000000};
      for (long t = 1; t <= 1000000 && ok; t++) {
        if (ph == 2) { h += (st % 2) ? 1 : -1; ph = 1; if (h < 10 || h > LT - 10) ok = 0; }
        else { int s = tp[h]; if (!def[st][s]) { ok = 0; break; } int d = (st % 2) ? 1 : -1; tp[h] = osy[st][s]; int nd2 = ofl[st][s] ? -d : d; st = osh[st][s]*2 + (nd2 > 0); ph = 2; }
        for (int m = 0; m < 3; m++) if (t == mark[m]) D[m][nd] = labs(h - h0); }
      if (ok) nd++; }
    nt++; printf("table %d: tapes %d  median |dh| at 1e4 1e5 1e6:", nt, nd);
    for (int m = 0; m < 3; m++) { qsort(D[m], nd, sizeof(long), cmp); printf(" %ld", nd ? D[m][nd/2] : -1); }
    printf("  |%s\n", orig); fflush(stdout); }
  return 0;
}
