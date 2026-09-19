/* Periodicity check for non-mirror machines (tokens as in types.c; undefined pairs -> machine stops, counted).
 * From NR random tapes, run up to NS steps; declare PERIODIC if the head stays inside a window of width <= 64
 * for the last half of the run and the configuration (state, head offset, window contents) repeats.
 * Reads tables from stdin, one per line, in even_dfs output format ("... table: tok tok ...").
 * usage: percheck NR NS P0   < tables */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define LT 20000
static int def[4][8], osh[4][8], osy[4][8], ofl[4][8], A;
static unsigned char tp[LT];
static uint64_t mix(uint64_t x) { x ^= x >> 31; x *= 0x9E3779B97F4A7C15ULL; x ^= x >> 29; return x; }
static int run1(long NS, double p0) { /* 1 periodic, 0 aperiodic-looking, -1 stuck/undefined */
  for (int i = 0; i < LT; i++) tp[i] = ((double)rand()/RAND_MAX < p0) ? 0 : 1 + rand() % (A-1);
  int h = LT/2, st = rand() % 4, ph = 2, lo = h, hi = h;
  uint64_t seen[4096] = {0}; long t;
  for (t = 0; t < NS; t++) {
    if (ph == 2) { h += (st % 2) ? 1 : -1; ph = 1; if (h < 100 || h > LT - 100) return 0; }
    else { int s = tp[h]; if (!def[st][s]) return -1; int d = (st % 2) ? 1 : -1; tp[h] = osy[st][s]; int nd = ofl[st][s] ? -d : d; st = osh[st][s]*2 + (nd > 0); ph = 2; }
    if (t == NS/2) { lo = h; hi = h; }
    if (t > NS/2) { if (h < lo) lo = h; if (h > hi) hi = h; if (hi - lo > 64) return 0;
      if ((t & 1) == 0) { uint64_t x = mix(st * 7 + ph); for (int i = lo - 2; i <= hi + 2; i++) x = mix(x ^ (tp[i] + 1) ^ ((uint64_t)(i - lo) << 20)); x = mix(x ^ (uint64_t)(h - lo));
        uint64_t k = x % 4096; if (seen[k] == x) return 1; seen[k] = x; } }
  }
  return 0;
}
int main(int argc, char **argv) {
  int NR = atoi(argv[1]); long NS = atol(argv[2]); double p0 = atof(argv[3]); char line[4096], orig[4096]; int nt = 0; srand(11);
  while (fgets(line, sizeof line, stdin)) {
    char *tb = strstr(line, "table:"); if (!tb) continue; strncpy(orig, tb + 6, sizeof orig - 1); orig[strcspn(orig, "\n")] = 0; memset(def, 0, sizeof def); A = 2;
    for (char *q = strtok(tb + 6, " \n"); q; q = strtok(0, " \n")) { int s = strchr("FHKL", q[0]) - "FHKL", sy = q[1]-'0';
      def[s][sy] = 1; osh[s][sy] = q[3]=='H'; osy[s][sy] = q[4]-'0'; ofl[s][sy] = q[5]=='f'; if (sy+1 > A) A = sy+1; if (osy[s][sy]+1 > A) A = osy[s][sy]+1; }
    int per = 0, ap = 0, stuck = 0; for (int r = 0; r < NR; r++) { int v = run1(NS, p0); if (v == 1) per++; else if (v == 0) ap++; else stuck++; }
    nt++; printf("table %d: periodic %d aperiodic %d undefined %d |%s\n", nt, per, ap, stuck, orig);
  }
  return 0;
}
