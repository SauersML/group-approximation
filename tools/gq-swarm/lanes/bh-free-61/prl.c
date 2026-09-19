/* bh-free-61: pointwise round lemma (PRL) for Sync_2.
   For a stuck nonnegative unimodular 3x3 X (columns = rays of c in Delta-side coordinates) and a braid pair
   (a,b), cut cone(X) by the wall x_a = x_b with the Euclid rule (right splits); a leaf Z is GOOD if left
   reductions reach entry sum < esum(X) (or a permutation). PRL: for every point of cone(X) some pair has
   a good leaf containing it, i.e. the bad leaves of the three pairs have no common interior point.
   PRL for all stuck X implies Sync_2 by induction on the entry sum at each point, then compactness.
   Exact integer arithmetic (__int128 for the cone-intersection test). Single core, self-timed. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <unistd.h>
#include <time.h>

typedef long long ll; typedef __int128 i128;
typedef struct { int e[9]; } Mat;
#define E(X,r,c) ((X).e[3*(r)+(c)])
static volatile sig_atomic_t timeup = 0;
static void on_alarm(int s) { (void)s; timeup = 1; }
static int perms[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
static Mat canon(const Mat *X) {
  Mat best; int have = 0;
  for (int p = 0; p < 6; p++) for (int q = 0; q < 6; q++) {
    Mat Y;
    for (int r = 0; r < 3; r++) for (int c = 0; c < 3; c++) E(Y,r,c) = E(*X, perms[p][r], perms[q][c]);
    if (!have || memcmp(Y.e, best.e, sizeof Y.e) < 0) { best = Y; have = 1; }
  }
  return best;
}
static ll det(const Mat *X) { const int *a = X->e;
  return (ll)a[0]*((ll)a[4]*a[8]-(ll)a[5]*a[7]) - (ll)a[1]*((ll)a[3]*a[8]-(ll)a[5]*a[6]) + (ll)a[2]*((ll)a[3]*a[7]-(ll)a[4]*a[6]); }
static int is_perm(const Mat *X) { int used[3] = {0,0,0};
  for (int r = 0; r < 3; r++) { int one = -1;
    for (int c = 0; c < 3; c++) { int v = E(*X,r,c); if (v == 1) { if (one >= 0) return 0; one = c; } else if (v != 0) return 0; }
    if (one < 0 || used[one]) return 0; used[one] = 1; }
  return 1; }
static int dom(const Mat *X, int a, int b) { for (int c = 0; c < 3; c++) if (E(*X,a,c) < E(*X,b,c)) return 0; return 1; }
static int stuck(const Mat *X) { if (is_perm(X)) return 0;
  for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) if (a != b && dom(X,a,b)) return 0; return 1; }
static ll esum(const Mat *X) { ll s = 0; for (int i = 0; i < 9; i++) s += X->e[i]; return s; }

/* memo for mu keyed by canonical matrix */
#define HB 22
#define HS (1u<<HB)
typedef struct { Mat k; int used; int mu; } MS;
static MS *MH;
static unsigned hsh(const Mat *X) { unsigned h = 2166136261u; for (int i = 0; i < 9; i++) { h ^= (unsigned)X->e[i]; h *= 16777619u; } return h; }
/* mu(X): least entry sum of a terminal position (stuck or permutation) reachable by left reductions */
static int mu_rec(const Mat *X, int depth) {
  Mat K = canon(X); unsigned i = hsh(&K) & (HS-1); MS *slot = NULL;
  for (unsigned n = 0; n < 64; n++, i = (i+1) & (HS-1)) {
    if (!MH[i].used) { slot = &MH[i]; break; }
    if (!memcmp(MH[i].k.e, K.e, sizeof K.e)) return MH[i].mu;
  }
  int best = -1, any = 0;
  if (is_perm(X)) best = 3;
  else for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) if (a != b && dom(X,a,b)) {
    any = 1; Mat Z = *X; for (int c = 0; c < 3; c++) E(Z,a,c) -= E(Z,b,c);
    int m = mu_rec(&Z, depth+1); if (m >= 0 && (best < 0 || m < best)) best = m;
  }
  if (!any && best < 0) best = (int)esum(X);
  (void)slot; i = hsh(&K) & (HS-1);   /* re-probe: the recursion may have filled the slot seen above */
  for (unsigned n = 0; n < 64; n++, i = (i+1) & (HS-1)) {
    if (!MH[i].used) { MH[i].used = 1; MH[i].k = K; MH[i].mu = best; break; }
    if (!memcmp(MH[i].k.e, K.e, sizeof K.e)) break;
  }
  return best;
}
#define MAXL 20000
static Mat LV[3][MAXL]; static int NL[3], OVF;
static void cutleaves(const Mat *Z, int a, int b, int p) {
  int v[3], pos = 0, neg = 0;
  for (int c = 0; c < 3; c++) { v[c] = E(*Z,a,c) - E(*Z,b,c); if (v[c] > 0) pos = 1; if (v[c] < 0) neg = 1; }
  if (!(pos && neg)) { if (NL[p] < MAXL) LV[p][NL[p]++] = *Z; else OVF = 1; return; }
  int T = 0; for (int c = 0; c < 3; c++) if (abs(v[c]) > T) T = abs(v[c]);
  int i = -1, sg = 0, j = -1, hasp = 0, hasn = 0;
  for (int c = 0; c < 3; c++) if (abs(v[c]) == T) { if (v[c] > 0) hasp = 1; else hasn = 1; }
  for (int c = 0; c < 3; c++) if (abs(v[c]) == T) { i = c; sg = v[c] > 0 ? 1 : -1; break; }
  if (hasp && hasn) { for (int c = 0; c < 3; c++) if (abs(v[c]) == T && (v[c] > 0 ? 1 : -1) == -sg) { j = c; break; } }
  else { for (int c = 0; c < 3; c++) if (v[c] != 0 && (v[c] > 0 ? 1 : -1) == -sg) { j = c; break; } }
  Mat Z1 = *Z, Z2 = *Z;
  for (int r = 0; r < 3; r++) { E(Z1,r,j) += E(*Z,r,i); E(Z2,r,i) += E(*Z,r,j); }
  cutleaves(&Z1, a, b, p); cutleaves(&Z2, a, b, p);
}
/* facet normals of cone(Z), oriented inward */
typedef struct { i128 n[3][3]; } Cone;
static void cross(const i128 *u, const i128 *v, i128 *w) { w[0] = u[1]*v[2]-u[2]*v[1]; w[1] = u[2]*v[0]-u[0]*v[2]; w[2] = u[0]*v[1]-u[1]*v[0]; }
static i128 dot(const i128 *u, const i128 *v) { return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]; }
static Cone mkcone(const Mat *Z) {
  Cone C; i128 z[3][3];
  for (int k = 0; k < 3; k++) for (int r = 0; r < 3; r++) z[k][r] = E(*Z,r,k);
  for (int k = 0; k < 3; k++) { cross(z[(k+1)%3], z[(k+2)%3], C.n[k]); if (dot(C.n[k], z[k]) < 0) for (int r = 0; r < 3; r++) C.n[k][r] = -C.n[k][r]; }
  return C;
}
static i128 g128(i128 a, i128 b) { if (a < 0) a = -a; if (b < 0) b = -b; while (b) { i128 t = a % b; a = b; b = t; } return a; }
/* do the interiors of the given cones share a point? returns 1 and a witness ray */
static int meet(const Cone *cs, int k, i128 *wit) {
  const i128 *N[9]; int nn = 0;
  for (int c = 0; c < k; c++) for (int f = 0; f < 3; f++) N[nn++] = cs[c].n[f];
  i128 s[3] = {0,0,0};
  for (int i = 0; i < nn; i++) for (int j = i+1; j < nn; j++) {
    i128 r[3]; cross(N[i], N[j], r);
    if (!r[0] && !r[1] && !r[2]) continue;
    i128 g = g128(g128(r[0], r[1]), r[2]); for (int t = 0; t < 3; t++) r[t] /= g;
    for (int sgn = -1; sgn <= 1; sgn += 2) {
      int ok = 1; for (int q = 0; q < nn && ok; q++) if (sgn*dot(N[q], r) < 0) ok = 0;
      if (ok) for (int t = 0; t < 3; t++) s[t] += sgn*r[t];
    }
  }
  for (int q = 0; q < nn; q++) if (dot(N[q], s) <= 0) return 0;
  if (wit) { i128 g = g128(g128(s[0], s[1]), s[2]); for (int t = 0; t < 3; t++) wit[t] = g ? s[t]/g : s[t]; }
  return 1;
}
static void pm(const Mat *X) { printf("[[%d,%d,%d],[%d,%d,%d],[%d,%d,%d]]", X->e[0],X->e[1],X->e[2],X->e[3],X->e[4],X->e[5],X->e[6],X->e[7],X->e[8]); }
static Cone BC[3][MAXL]; static int NB[3];

int main(int argc, char **argv) {
  int S = argc > 1 ? atoi(argv[1]) : 24; int limit = argc > 2 ? atoi(argv[2]) : 240;
  signal(SIGALRM, on_alarm); alarm(limit);
  MH = calloc(HS, sizeof(MS)); if (!MH) { printf("alloc\n"); return 1; }
  /* calibration: M is won by one split, so some pair must be globally good; the round-fail example must need PRL */
  { Mat cal[3] = {{{3,1,0,1,1,1,0,1,2}}, {{9,2,0,2,1,1,0,1,2}}, {{0,2,5,2,1,1,7,2,0}}}; int pr[3][2] = {{0,1},{0,2},{1,2}};
    for (int t = 0; t < 3; t++) { printf("calib "); pm(&cal[t]); printf(" det=%lld stuck=%d bad:", det(&cal[t]), stuck(&cal[t]));
      for (int p = 0; p < 3; p++) { NL[p] = 0; NB[p] = 0; cutleaves(&cal[t], pr[p][0], pr[p][1], p);
        for (int l = 0; l < NL[p]; l++) { int m = mu_rec(&LV[p][l], 0); if (m < 0 || m >= esum(&cal[t])) NB[p]++; }
        printf(" %d/%d", NB[p], NL[p]); }
      printf("\n"); }
    Mat I = {{1,0,0,0,1,0,0,0,1}}, A = {{1,1,0,0,1,0,0,0,1}}, B = {{1,0,0,1,1,0,0,0,1}};
    Cone t2[2] = {mkcone(&A), mkcone(&A)}; Cone u2[2] = {mkcone(&A), mkcone(&B)}; Cone v2[2] = {mkcone(&I), mkcone(&B)};
    printf("control meet: same=%d (1) halves=%d (0) nested=%d (1)\n", meet(t2,2,NULL), meet(u2,2,NULL), meet(v2,2,NULL)); fflush(stdout); }
  ll nst = 0, nglob = 0, npw = 0, nfail = 0, novf = 0; int lastS = -1; time_t t0 = time(NULL);
  int a[9];
  for (int s = 3; s <= S; s++)
  for (a[0] = 0; a[0] <= s; a[0]++) for (a[1] = 0; a[0]+a[1] <= s; a[1]++) for (a[2] = 0; a[0]+a[1]+a[2] <= s; a[2]++)
  for (a[3] = 0; a[0]+a[1]+a[2]+a[3] <= s; a[3]++) for (a[4] = 0; a[0]+a[1]+a[2]+a[3]+a[4] <= s; a[4]++)
  for (a[5] = 0; a[0]+a[1]+a[2]+a[3]+a[4]+a[5] <= s; a[5]++) for (a[6] = 0; a[0]+a[1]+a[2]+a[3]+a[4]+a[5]+a[6] <= s; a[6]++)
  for (a[7] = 0; a[0]+a[1]+a[2]+a[3]+a[4]+a[5]+a[6]+a[7] <= s; a[7]++) {
    a[8] = s - (a[0]+a[1]+a[2]+a[3]+a[4]+a[5]+a[6]+a[7]);
    if (s != lastS) { if (lastS >= 0) { printf("sum<=%d: stuck=%lld globalgood=%lld pointwise=%lld PRLFAIL=%lld ovf=%lld t=%lds\n", lastS, nst, nglob, npw, nfail, novf, (long)(time(NULL)-t0)); fflush(stdout); } lastS = s; }
    if (timeup) goto done;
    Mat X; memcpy(X.e, a, sizeof a);
    ll dt = det(&X); if (dt != 1 && dt != -1) continue;
    if (!stuck(&X)) continue;
    Mat K = canon(&X); if (memcmp(K.e, X.e, sizeof X.e)) continue;
    nst++; ll sx = esum(&X); int glob = 0; OVF = 0;
    int pr[3][2] = {{0,1},{0,2},{1,2}};
    for (int p = 0; p < 3; p++) {
      NL[p] = 0; NB[p] = 0; cutleaves(&X, pr[p][0], pr[p][1], p);
      for (int l = 0; l < NL[p]; l++) { int m = mu_rec(&LV[p][l], 0); if (m < 0 || m >= sx) BC[p][NB[p]++] = mkcone(&LV[p][l]); }
      if (NB[p] == 0) glob = 1;
    }
    if (OVF) { novf++; continue; }
    if (glob) { nglob++; continue; }
    int bad = 0; i128 wit[3];
    for (int i = 0; i < NB[0] && !bad; i++) for (int j = 0; j < NB[1] && !bad; j++) {
      Cone two[3] = {BC[0][i], BC[1][j]}; if (!meet(two, 2, NULL)) continue;
      for (int k = 0; k < NB[2] && !bad; k++) { two[2] = BC[2][k]; if (meet(two, 3, wit)) bad = 1; }
    }
    if (bad) { nfail++; if (nfail <= 40) { printf("PRL-FAIL sum=%lld ", sx); pm(&X); printf(" bad=%d/%d/%d witness=(%lld,%lld,%lld)\n", NB[0], NB[1], NB[2], (ll)wit[0], (ll)wit[1], (ll)wit[2]); } }
    else { npw++; if (npw <= 5) { printf("pointwise-only sum=%lld ", sx); pm(&X); printf(" bad=%d/%d/%d\n", NB[0], NB[1], NB[2]); } }
  }
done:
  printf("%s S=%d: stuck=%lld globalgood=%lld pointwise=%lld PRLFAIL=%lld ovf=%lld t=%lds\n", timeup ? "TIMEOUT(partial)" : "DONE", S, nst, nglob, npw, nfail, novf, (long)(time(NULL)-t0));
  return 0;
}
