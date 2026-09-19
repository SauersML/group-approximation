/* bh-free-61: half-tube lemma in rank n = m+1 >= 3.  zeta generic (random 56-bit integer coordinates), t > 0,
   w = primitive part of round(t.zeta).  d = w - t'.zeta has |d|_inf < 1/2.  Strategy: pick a pair (i,j) with
   d_i d_j >= 0 and z_i > z_j, preferring u_j > 0; the lemma says u_i >= u_j always and |d|_inf stays < 1/2.
   Exact arithmetic: d = D / DEN with D, DEN integers.  Single core, self-timed. */
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>
typedef __int128 i128; typedef long long ll;
static volatile sig_atomic_t timeup = 0; static void on_alarm(int s) { (void)s; timeup = 1; }
static unsigned long long rs = 0x9E3779B97F4A7C15ull;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static i128 ab(i128 x) { return x < 0 ? -x : x; }
int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 4; ll L = argc > 2 ? atoll(argv[2]) : 100000; int NS = argc > 3 ? atoi(argv[3]) : 20000;
  int lim = argc > 4 ? atoi(argv[4]) : 60; signal(SIGALRM, on_alarm); alarm(lim);
  ll whyc[10] = {0}; ll tested = 0, won = 0, ties = 0, bad = 0, maxsteps = 0, caseB = 0;
  for (int k = 0; k < NS && !timeup; k++) {
    i128 z[8]; ll u[8]; i128 D[8];
    for (int i = 0; i < n; i++) z[i] = (i128)(rnd() >> 8) + 1;
    ll lam = L/2 + (ll)(rnd() % (unsigned long long)(L/2 + 1)); i128 den = z[0]; for (int i = 1; i < n; i++) if (z[i] > den) den = z[i];
    for (int i = 0; i < n; i++) { u[i] = (ll)((2*(i128)lam*z[i] + den) / (2*den)); D[i] = den*(i128)u[i] - (i128)lam*z[i]; }
    ll g = 0; for (int i = 0; i < n; i++) { ll x = u[i], y = g; while (y) { ll t = x % y; x = y; y = t; } g = x; }
    if (g == 0) continue;
    for (int i = 0; i < n; i++) u[i] /= g;
    i128 DEN = (i128)g * den; int ok = 1;
    for (int i = 0; i < n; i++) if (2*ab(D[i]) >= DEN) ok = 0;
    if (!ok) continue;
    tested++; ll steps = 0; int why = 0;
    for (;;) {
      int npos = 0; for (int i = 0; i < n; i++) if (u[i] > 0) npos++;
      if (npos == 1) break;
      int tie = 0; for (int i = 0; i < n; i++) for (int j = i+1; j < n; j++) if (z[i] == z[j]) tie = 1;
      if (tie) { why = 1; break; }
      int bi = -1, bj = -1;
      /* Case A: two coordinates with u > 0 and d of the same sign; orient by z */
      for (int i = 0; i < n && bi < 0; i++) for (int j = 0; j < n && bi < 0; j++) if (i != j && u[i] > 0 && u[j] > 0 && z[i] > z[j] && ((D[i] >= 0 && D[j] >= 0) || (D[i] <= 0 && D[j] <= 0))) { bi = i; bj = j; }
      if (bi < 0) { /* Case B: P = {a,b}, d_a > 0 > d_b; move (b,k) with u_k = 0, z_k largest; the lemma forces z_b > z_k */
        int b = -1, k = -1; for (int i = 0; i < n; i++) if (u[i] > 0 && D[i] < 0) b = i;
        for (int i = 0; i < n; i++) if (u[i] == 0 && (k < 0 || z[i] > z[k])) k = i;
        if (b < 0 || k < 0) { why = 2; break; }
        if (!(z[b] > z[k])) { why = 7; break; }
        bi = b; bj = k; caseB++; }
      if (u[bi] < u[bj]) { why = 3; break; }
      { i128 qz = (z[bi] - 1) / z[bj]; i128 qd = D[bj] == 0 ? qz : (D[bi] / D[bj]) + 1; i128 qm = qz < qd ? qz : qd;
        i128 qu = u[bj] > 0 ? (i128)(u[bi] / u[bj]) : qm; if (qu < qm) { why = 8; break; }   /* lemma: u-legality never binds first */
        if (qm < 1) { why = 9; break; }
        u[bi] -= (ll)qm * u[bj]; z[bi] -= qm * z[bj]; D[bi] -= qm * D[bj]; steps++; }
      for (int i = 0; i < n; i++) if (2*ab(D[i]) >= DEN || z[i] <= 0) why = 4;
      if (why || steps > 50000000) { if (!why) why = 5; break; }
    }
    if (!why) { int one = 0; for (int i = 0; i < n; i++) if (u[i] == 1) one++; if (one == 1) won++; else { why = 6; } }
    if (why == 1) ties++; else if (why) { bad++; whyc[why]++; }
    if (steps > maxsteps) maxsteps = steps;
  }
  printf("%s n=%d L=%lld: tested=%lld won=%lld ties(rational artifact)=%lld BAD=%lld maxsteps=%lld non-progress-moves=%lld\n",
         timeup ? "TIMEOUT(partial)" : "DONE", n, L, tested, won, ties, bad, maxsteps, caseB);
  printf("  BAD by reason: 2:%lld 3:%lld 4:%lld 5(step cap):%lld 6:%lld 7:%lld 8:%lld 9:%lld\n", whyc[2], whyc[3], whyc[4], whyc[5], whyc[6], whyc[7], whyc[8], whyc[9]);
  return 0;
}
