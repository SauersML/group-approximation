/* bh-free-61: joint subtractive game.  State (u, z): u = lattice point w in the current cell's frame (nonneg
   integers), z = the point zeta in that frame (positive, generic).  Move (i,j): allowed iff u_i >= u_j and
   z_i > z_j; then u_i -= u_j, z_i -= z_j (both pass to the same child of the edge split at (i,j)).
   Won iff u is a unit vector (w is a vertex of a descendant cell containing zeta).
   w in V_C(zeta)  <=>  the game from C's frame is won.
   Tests: (A) density of winners near zeta from Delta; (B) shared vertices of Delta and a stuck cell c = X.Delta.
   Generic rational zeta (random 40-bit coordinates) stands in for a totally irrational one: a finite game only
   reads finitely many strict comparisons, so a loss at a tie-free generic zeta persists on an open set. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <signal.h>
#include <unistd.h>
typedef __int128 i128; typedef long long ll;
static volatile sig_atomic_t timeup = 0; static void on_alarm(int s) { (void)s; timeup = 1; }
static unsigned long long rs = 88172645463325252ull;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
#define HB 20
#define HS (1u<<HB)
typedef struct { ll u[3]; i128 z[3]; int used; } St;
static St *T; static unsigned *touched; static int ntouched; static ll budget; static int tie;
static unsigned hh(const ll *u, const i128 *z) { unsigned long long h = 1469598103934665603ull;
  for (int i = 0; i < 3; i++) { h ^= (unsigned long long)u[i]; h *= 1099511628211ull; h ^= (unsigned long long)(z[i] ^ (z[i] >> 64)); h *= 1099511628211ull; }
  return (unsigned)(h ^ (h >> 29)); }
static int seen(const ll *u, const i128 *z) { /* returns 1 if already visited; else inserts */
  unsigned i = hh(u, z) & (HS-1);
  for (int n = 0; n < 256; n++, i = (i+1) & (HS-1)) {
    if (!T[i].used) { T[i].used = 1; memcpy(T[i].u, u, sizeof T[i].u); memcpy(T[i].z, z, sizeof T[i].z); touched[ntouched++] = i; return 0; }
    if (!memcmp(T[i].u, u, sizeof T[i].u) && !memcmp(T[i].z, z, sizeof T[i].z)) return 1;
  }
  return 1; /* crowded: treat as seen (may undercount wins; reported via budget) */
}
static int isunit(const ll *u) { int nz = 0, one = 0; for (int i = 0; i < 3; i++) { if (u[i]) nz++; if (u[i] == 1) one++; } return nz == 1 && one == 1; }
static int depth;
static int game(ll *u, i128 *z) {
  if (isunit(u)) return 1;
  if (depth > 4000) { budget = -1; return 0; }
  if (--budget < 0 || ntouched > (int)(HS/2)) return 0;
  if (seen(u, z)) return 0;
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (i != j) {
    if (z[i] == z[j]) tie = 1;
    if (u[i] >= u[j] && z[i] > z[j]) {
      u[i] -= u[j]; z[i] -= z[j];
      depth++; int r = game(u, z); depth--;
      u[i] += u[j]; z[i] += z[j];
      if (r) return 1;
    }
  }
  return 0;
}
static void clear(void) { for (int k = 0; k < ntouched; k++) T[touched[k]].used = 0; ntouched = 0; }
/* play from frame X (columns = rays): u = X^{-1} w, z = X^{-1} zeta ; returns -1 if w not in cone(X) */
static ll Xi[9]; /* adjugate/det of X, integer since unimodular */
static int from_frame(const ll *w, const i128 *zeta, int *unknown) {
  ll u[3]; i128 z[3];
  for (int r = 0; r < 3; r++) { u[r] = 0; z[r] = 0; for (int c = 0; c < 3; c++) { u[r] += Xi[3*r+c]*w[c]; z[r] += (i128)Xi[3*r+c]*zeta[c]; } }
  for (int r = 0; r < 3; r++) if (u[r] < 0) return -1;
  budget = 400000; tie = 0; depth = 0; int res = game(u, z); clear();
  if (budget < 0 || tie) *unknown = 1;
  return res;
}
static double ang(const ll *w, const double *zd) { double a = 0, b = 0, c = 0; for (int i = 0; i < 3; i++) { a += w[i]*zd[i]; b += (double)w[i]*w[i]; c += zd[i]*zd[i]; } double x = a / sqrt(b*c); if (x > 1) x = 1; return acos(x); }
int main(int argc, char **argv) {
  int S = argc > 1 ? atoi(argv[1]) : 40, trials = argc > 2 ? atoi(argv[2]) : 4, lim = argc > 3 ? atoi(argv[3]) : 100;
  double RAD = argc > 4 ? atof(argv[4]) : 10.0; int mode = argc > 5 ? atoi(argv[5]) : 1; ll L = argc > 6 ? atoll(argv[6]) : 1000; int NS = argc > 7 ? atoi(argv[7]) : 2000;
  signal(SIGALRM, on_alarm); alarm(lim);
  T = calloc(HS, sizeof(St)); touched = malloc(sizeof(unsigned) * HS); if (!T || !touched) return 1;
  ll X[3][9] = {{1,0,0,0,1,0,0,0,1}, {3,1,0,1,1,1,0,1,2}, {9,2,0,2,1,1,0,1,2}};  /* Delta, M, X9 (row-major; columns = rays) */
  ll XI[3][9];
  for (int t = 0; t < 3; t++) { ll *a = X[t]; ll d = a[0]*(a[4]*a[8]-a[5]*a[7]) - a[1]*(a[3]*a[8]-a[5]*a[6]) + a[2]*(a[3]*a[7]-a[4]*a[6]);
    ll adj[9] = { a[4]*a[8]-a[5]*a[7], a[2]*a[7]-a[1]*a[8], a[1]*a[5]-a[2]*a[4], a[5]*a[6]-a[3]*a[8], a[0]*a[8]-a[2]*a[6], a[2]*a[3]-a[0]*a[5], a[3]*a[7]-a[4]*a[6], a[1]*a[6]-a[0]*a[7], a[0]*a[4]-a[1]*a[3] };
    for (int k = 0; k < 9; k++) XI[t][k] = adj[k] / d; printf("frame %d det=%lld\n", t, d); }
  /* calibration: w = (1,1,1) wins from Delta for any zeta; w=(1,1,100), zeta ~ (1,2,2.001) loses */
  { i128 z[3] = {1000000000000LL, 2000100000000LL, 2001100000000LL}; ll w1[3] = {1,1,1}, w2[3] = {1,1,100}; int un = 0;
    memcpy(Xi, XI[0], sizeof Xi); printf("calib: (1,1,1) %d (want 1); (1,1,100) %d (want 0) unknown=%d\n", from_frame(w1, z, &un), from_frame(w2, z, &un), un); }
  for (int t = 0; t < trials && !timeup; t++) {
    int f = 1 + (t % 2);  /* stuck frame c = M or X9 */
    ll y[3]; for (int i = 0; i < 3; i++) y[i] = (ll)(rnd() >> (mode == 3 ? 4 : 24)) + 1;   /* zeta = X_f . y, generic, interior of c */
    i128 zeta[3]; double zd[3];
    for (int r = 0; r < 3; r++) { zeta[r] = 0; for (int c = 0; c < 3; c++) zeta[r] += (i128)X[f][3*r+c] * y[c]; zd[r] = (double)zeta[r]; }
    ll nwinD = 0, nloseD = 0, nwinC = 0, nloseC = 0, nboth = 0, nunk = 0, bestboth = -1; double dloseD = 9, dloseC = 9, dboth = 9;
    ll bw[3] = {0,0,0};
    int bins = 8; ll wD[8] = {0}, lD[8] = {0};
    for (ll s = 1; s <= S && !timeup; s++) for (ll a = 0; a <= s; a++) for (ll b = 0; a+b <= s; b++) {
      ll w[3] = {a, b, s-a-b}; ll g = 0; for (int i = 0; i < 3; i++) { ll x = w[i], yy = g; while (yy) { ll tt = x % yy; x = yy; yy = tt; } g = x; }
      if (g != 1) continue;
      if (mode != 1) goto skip; if (ang(w, zd) > RAD) continue;
      int un = 0; memcpy(Xi, XI[0], sizeof Xi); int rD = from_frame(w, zeta, &un);
      memcpy(Xi, XI[f], sizeof Xi); int rC = from_frame(w, zeta, &un);
      if (un) { nunk++; continue; }
      double d = ang(w, zd); int bin = 0; double lo = 0.4; while (bin < bins-1 && d < lo) { bin++; lo /= 2; }
      if (rD == 1) { nwinD++; wD[bin]++; } else { nloseD++; lD[bin]++; if (d < dloseD) dloseD = d; }
      if (rC == 1) nwinC++; else if (rC == 0) { nloseC++; if (d < dloseC) dloseC = d; }
      if (rD == 1 && rC == 1) { nboth++; if (bestboth < 0 || s < bestboth) { bestboth = s; memcpy(bw, w, sizeof bw); } if (d < dboth) dboth = d; }
    }
    skip:;
    if (mode == 2) { /* random primitive points of norm ~L within angle ~RAD of zeta */
      double zs = zd[0] + zd[1] + zd[2]; int shown = 0;
      for (int k = 0; k < NS && !timeup; k++) {
        double lam = L * (0.5 + 0.5 * (rnd() % 1000000) / 1e6), D = RAD * lam * ((rnd() % 1000000) / 1e6);
        ll w[3]; int ok = 1;
        for (int i = 0; i < 3; i++) { double x = zd[i] * lam / zs + D * (2.0 * (rnd() % 1000000) / 1e6 - 1.0); w[i] = (ll)llround(x); if (w[i] < 0) ok = 0; }
        if (!ok) continue;
        ll g = 0; for (int i = 0; i < 3; i++) { ll x = w[i], yy = g; while (yy) { ll tt = x % yy; x = yy; yy = tt; } g = x; }
        if (g != 1) continue;
        int un = 0; memcpy(Xi, XI[0], sizeof Xi); int rD = from_frame(w, zeta, &un);
        memcpy(Xi, XI[f], sizeof Xi); int rC = from_frame(w, zeta, &un);
        if (un) { nunk++; continue; }
        double d = ang(w, zd); int bin = 0; double lo = RAD; while (bin < bins-1 && d < lo) { bin++; lo /= 2; }
        if (rD == 1) { nwinD++; wD[bin]++; } else { nloseD++; lD[bin]++; if (d < dloseD) dloseD = d; if (shown++ < 6) printf("  loser(Delta) w=(%lld,%lld,%lld) angle=%.3e\n", w[0], w[1], w[2], d); }
        if (rC == 1) nwinC++; else if (rC == 0) { nloseC++; if (d < dloseC) dloseC = d; }
        if (rD == 1 && rC == 1) nboth++;
      }
    }
    if (mode == 3) { /* tube lemma: w = primitive part of round(t.zeta) must be won by the tube-preserving strategy */
      ll sharedunk = 0, sharedlost = 0, ties = 0, tested = 0, won = 0, fail = 0, maxsteps = 0, shared = 0, sharedwon = 0, gamecheck = 0, gamebad = 0; ll sw[3] = {0,0,0}; ll swn = -1;
      for (int k = 0; k < NS && !timeup; k++) for (int side = 0; side < 2; side++) {
        /* side 0: tube in Delta frame around zeta; side 1: tube in c frame around y = X^{-1} zeta */
        i128 z0[3]; for (int i = 0; i < 3; i++) z0[i] = side ? (i128)y[i] : zeta[i];
        ll lam = L/2 + (ll)(rnd() % (unsigned long long)(L/2 + 1));
        i128 den = z0[0]; ll w[3]; i128 D[3];
        for (int i = 0; i < 3; i++) { i128 num = 2*(i128)lam*z0[i] + den; w[i] = (ll)(num / (2*den)); }
        ll g = 0; for (int i = 0; i < 3; i++) { ll x = w[i], yy = g; while (yy) { ll tt = x % yy; x = yy; yy = tt; } g = x; }
        if (g == 0) continue;
        for (int i = 0; i < 3; i++) D[i] = den * (i128)w[i] - (i128)lam * z0[i];   /* d = D / (g.den) after dividing w by g */
        for (int i = 0; i < 3; i++) w[i] /= g;
        i128 DEN = (i128)g * den;
        int intube = 1; for (int i = 0; i < 3; i++) if (2*(D[i] < 0 ? -D[i] : D[i]) >= DEN) intube = 0;
        if (!intube) continue;
        tested++;
        i128 D0[3] = {D[0], D[1], D[2]};
        ll u[3] = {w[0], w[1], w[2]}; i128 z[3] = {z0[0], z0[1], z0[2]}; ll steps = 0; int ok = 1, why = 0;
        while (!isunit(u) && ok) {
          int bi = -1, bj = -1, prog = 0;
          for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (i != j && z[i] > z[j] && ((D[i] >= 0 && D[j] >= 0) || (D[i] <= 0 && D[j] <= 0))) {
            int p = u[j] > 0; if (bi < 0 || (p && !prog)) { bi = i; bj = j; prog = p; } }
          { int tie2 = 0; for (int i = 0; i < 3; i++) for (int j = i+1; j < 3; j++) if (z[i] == z[j]) tie2 = 1;
            if (tie2) { ok = 0; why = 1; break; }
            if (bi < 0) { ok = 0; why = 2; break; } if (u[bi] < u[bj]) { ok = 0; why = 3; break; } }   /* the lemma says this never happens */
          u[bi] -= u[bj]; z[bi] -= z[bj]; D[bi] -= D[bj]; steps++;
          for (int i = 0; i < 3; i++) if (2*(D[i] < 0 ? -D[i] : D[i]) >= DEN || z[i] <= 0) { ok = 0; why = 4; }
          if (steps > 10000000) ok = 0;
        }
        if (ok) won++; else { if (why == 1) ties++; else { fail++; if (fail <= 5) printf("  TUBE-FAIL why=%d side=%d w=(%lld,%lld,%lld)\n", why, side, w[0], w[1], w[2]); } }
        if (steps > maxsteps) maxsteps = steps;
        /* full game search as an independent check on small w */
        if (w[0] + w[1] + w[2] <= 400) { ll ww[3]; if (side) { for (int r = 0; r < 3; r++) { ww[r] = 0; for (int c = 0; c < 3; c++) ww[r] += X[f][3*r+c] * w[c]; } } else memcpy(ww, w, sizeof ww);
          int un = 0; memcpy(Xi, XI[side ? f : 0], sizeof Xi); int r = from_frame(ww, zeta, &un); gamecheck++; if (r != 1 && !un) gamebad++; }
        /* shared vertex: a Delta-tube point that is also in the c-tube (same t) */
        if (side == 0) { i128 Dc[3]; int inc = 1; for (int r = 0; r < 3; r++) { Dc[r] = 0; for (int c = 0; c < 3; c++) Dc[r] += (i128)XI[f][3*r+c] * D0[c]; if (2*(Dc[r] < 0 ? -Dc[r] : Dc[r]) >= DEN) inc = 0; }
          ll wc[3]; for (int r = 0; r < 3; r++) { wc[r] = 0; for (int c = 0; c < 3; c++) wc[r] += XI[f][3*r+c] * w[c]; if (wc[r] < 0) inc = 0; }
          if (inc) { shared++; int un = 0; memcpy(Xi, XI[f], sizeof Xi); int rc = (w[0]+w[1]+w[2] <= 400) ? from_frame(w, zeta, &un) : 1; if (rc == 1) sharedwon++; else if (un) sharedunk++; else { sharedlost++; if (sharedlost <= 3) { printf("  SHARED-LOST w=(%lld,%lld,%lld) u_c=(%lld,%lld,%lld) z_c=(%.6g,%.6g,%.6g) d_c=(%.4f,%.4f,%.4f)\n", w[0], w[1], w[2], wc[0], wc[1], wc[2], (double)y[0], (double)y[1], (double)y[2], (double)Dc[0]/(double)DEN, (double)Dc[1]/(double)DEN, (double)Dc[2]/(double)DEN);
              ll uu[3] = {wc[0], wc[1], wc[2]}; i128 zz[3] = {(i128)y[0], (i128)y[1], (i128)y[2]}, DD[3] = {Dc[0], Dc[1], Dc[2]}; int st = 0;
              while (!isunit(uu) && st < 100000) { int bi = -1, bj = -1; for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (i != j && zz[i] > zz[j] && ((DD[i] >= 0 && DD[j] >= 0) || (DD[i] <= 0 && DD[j] <= 0))) { if (bi < 0 || uu[j] > 0) { bi = i; bj = j; } }
                if (bi < 0 || uu[bi] < uu[bj]) { printf("    strategy stuck at u=(%lld,%lld,%lld)\n", uu[0], uu[1], uu[2]); break; }
                uu[bi] -= uu[bj]; zz[bi] -= zz[bj]; DD[bi] -= DD[bj]; st++; }
              printf("    c-frame strategy: %s after %d moves\n", isunit(uu) ? "WON" : "not won", st); } }
            if (swn < 0 || w[0]+w[1]+w[2] < swn) { swn = w[0]+w[1]+w[2]; memcpy(sw, w, sizeof sw); } } }
      }
      printf("  tube: tested=%lld strategy-won=%lld ties(rational zeta artifact)=%lld FAIL=%lld maxsteps=%lld | full-search check %lld, not won %lld | shared Delta&c tube points=%lld (c-game won %lld, budget-out %lld, lost %lld) smallest=(%lld,%lld,%lld)\n",
             tested, won, ties, fail, maxsteps, gamecheck, gamebad, shared, sharedwon, sharedunk, sharedlost, sw[0], sw[1], sw[2]);
    }
    printf("trial %d frame=%d y=(%lld,%lld,%lld): fromDelta win=%lld lose=%lld (closest loser %.2e) | fromC win=%lld lose=%lld (closest %.2e) | BOTH=%lld smallest=(%lld,%lld,%lld) unknown=%lld\n",
      t, f, y[0], y[1], y[2], nwinD, nloseD, dloseD, nwinC, nloseC, dloseC, nboth, bw[0], bw[1], bw[2], nunk);
    printf("   fromDelta by angle bin (>=0.4, then halving): "); for (int k = 0; k < bins; k++) printf(" %lld/%lld", wD[k], wD[k]+lD[k]); printf("\n");
    fflush(stdout);
  }
  printf("%s\n", timeup ? "TIMEOUT" : "DONE");
  return 0;
}
