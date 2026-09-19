/* bh-free-61: bounded exact test of Sync_2 (unimodular-cells-synchronize-under-edge-splits).
   Positions: 3x3 integer matrices X (cell cone(X) in Delta-side coordinates).
   Left reduction (a,b): row a -= row b, allowed when row_a >= row_b entrywise.
   Right split (c,d): children X*T_cd (col d += col c) and X*T_dc (col c += col d); both must be won.
   Won: permutation matrix.  Strategy "braid cut": at a stuck position pick a braid form x_a - x_b,
   run the cut-lemma Euclid rule on row_a - row_b, then reduce. Fallback: exhaustive AND-OR search.
   Single core, exact int arithmetic, self-timed. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <unistd.h>
#include <time.h>

typedef struct { int e[9]; } Mat;
#define E(X,r,c) ((X).e[3*(r)+(c)])

static volatile sig_atomic_t timeup = 0;
static void on_alarm(int s) { (void)s; timeup = 1; }

static int perms[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};

static Mat canon(const Mat *X) {
  Mat best; int have = 0;
  for (int p = 0; p < 6; p++) for (int q = 0; q < 6; q++) {
    Mat Y;
    for (int r = 0; r < 3; r++) for (int c = 0; c < 3; c++)
      E(Y,r,c) = E(*X, perms[p][r], perms[q][c]);
    if (!have || memcmp(Y.e, best.e, sizeof Y.e) < 0) { best = Y; have = 1; }
  }
  return best;
}
static long long det(const Mat *X) {
  const int *a = X->e;
  return (long long)a[0]*((long long)a[4]*a[8]-(long long)a[5]*a[7])
       - (long long)a[1]*((long long)a[3]*a[8]-(long long)a[5]*a[6])
       + (long long)a[2]*((long long)a[3]*a[7]-(long long)a[4]*a[6]);
}
static int is_perm(const Mat *X) {
  int used[3] = {0,0,0};
  for (int r = 0; r < 3; r++) {
    int one = -1;
    for (int c = 0; c < 3; c++) {
      int v = E(*X,r,c);
      if (v == 1) { if (one >= 0) return 0; one = c; } else if (v != 0) return 0;
    }
    if (one < 0 || used[one]) return 0;
    used[one] = 1;
  }
  return 1;
}
static int dom(const Mat *X, int a, int b) {
  /* cone(X) lies in the child C_ab only if cone(X) lies in Delta at all, i.e. X >= 0 */
  for (int i = 0; i < 9; i++) if (X->e[i] < 0) return 0;
  for (int c = 0; c < 3; c++) if (E(*X,a,c) < E(*X,b,c)) return 0;
  return 1;
}
static int stuck(const Mat *X) {
  if (is_perm(X)) return 0;
  for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) if (a != b && dom(X,a,b)) return 0;
  return 1;
}
static long long esum(const Mat *X) { long long s = 0; for (int i = 0; i < 9; i++) s += X->e[i]; return s; }

/* ---- memo: key = canonical matrix, value = won-at-depth (min) / lost-at-depth (max) per table ---- */
#define HBITS 21
#define HSIZE (1u<<HBITS)
typedef struct { Mat k; signed char used, wond, lostd; } Slot;
static Slot *H[2];
static unsigned hsh(const Mat *X) {
  unsigned h = 2166136261u;
  for (int i = 0; i < 9; i++) { h ^= (unsigned)X->e[i]; h *= 16777619u; }
  return h;
}
static Slot *hget(int t, const Mat *K) {
  unsigned i = hsh(K) & (HSIZE-1);
  for (unsigned n = 0; n < 64; n++, i = (i+1) & (HSIZE-1)) {
    Slot *s = &H[t][i];
    if (!s->used) { s->used = 1; s->k = *K; s->wond = 127; s->lostd = -1; return s; }
    if (!memcmp(s->k.e, K->e, sizeof K->e)) return s;
  }
  return NULL; /* table crowded: no memo */
}

/* ---- reduction closure: all irreducible matrices reachable by left reductions ---- */
#define MAXT 8
static long long red_budget;
static int reduce_all(const Mat *X, Mat *out, int nout) {
  /* DFS; returns count; 1 if a permutation is found (placed first). */
  static Mat stack[4096]; int sp = 0; int n = 0;   /* not reentrant: reduce_all never recurses */
  static Mat seen[512]; int ns = 0;
  stack[sp++] = *X;
  while (sp > 0 && red_budget > 0) {
    Mat Y = stack[--sp]; red_budget--;
    Mat Kc = canon(&Y); int dup = 0;
    for (int i = 0; i < ns; i++) if (!memcmp(seen[i].e, Kc.e, sizeof Kc.e)) { dup = 1; break; }
    if (dup) continue;
    if (ns < 512) seen[ns++] = Kc;
    if (is_perm(&Y)) { out[0] = Y; return -1; }
    int any = 0;
    for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) if (a != b && dom(&Y,a,b)) {
      any = 1;
      if (sp < 4096) { Mat Z = Y; for (int c = 0; c < 3; c++) E(Z,a,c) -= E(Z,b,c); stack[sp++] = Z; }
    }
    if (!any && n < nout) out[n++] = Y;
  }
  return n;
}

static long long nodes;
static int win(const Mat *X, int d);
static int cut_rec(const Mat *Z, int a, int b, int d) {
  if (timeup) return 0;
  int v[3], pos = 0, neg = 0;
  for (int c = 0; c < 3; c++) { v[c] = E(*Z,a,c) - E(*Z,b,c); if (v[c] > 0) pos = 1; if (v[c] < 0) neg = 1; }
  if (!(pos && neg)) {
    /* no sign change: for Z >= 0 this is a row dominance, so win() strictly lowers the entry sum.
       For Z with a negative entry it is not, and recursing would loop: this branch is lost. */
    for (int k = 0; k < 9; k++) if (Z->e[k] < 0) return 0;
    return win(Z, d);
  }
  if (d <= 0) return 0;
  int T = 0; for (int c = 0; c < 3; c++) if (abs(v[c]) > T) T = abs(v[c]);
  int i = -1, sg = 0, j = -1;
  int hasp = 0, hasn = 0;
  for (int c = 0; c < 3; c++) if (abs(v[c]) == T) { if (v[c] > 0) hasp = 1; else hasn = 1; }
  for (int c = 0; c < 3; c++) if (abs(v[c]) == T) { i = c; sg = v[c] > 0 ? 1 : -1; break; }
  if (hasp && hasn) { for (int c = 0; c < 3; c++) if (abs(v[c]) == T && (v[c] > 0 ? 1 : -1) == -sg) { j = c; break; } }
  else { for (int c = 0; c < 3; c++) if (v[c] != 0 && (v[c] > 0 ? 1 : -1) == -sg) { j = c; break; } }
  Mat Z1 = *Z, Z2 = *Z;
  for (int r = 0; r < 3; r++) { E(Z1,r,j) += E(*Z,r,i); E(Z2,r,i) += E(*Z,r,j); }
  return cut_rec(&Z1, a, b, d-1) && cut_rec(&Z2, a, b, d-1);
}
static int win(const Mat *X, int d) {
  if (timeup) return 0;
  nodes++;
  Mat K = canon(X);
  Slot *s = hget(0, &K);
  if (s && s->wond <= d) return 1;
  if (s && s->lostd >= d) return 0;
  Mat term[MAXT]; red_budget = 20000;
  int n = reduce_all(X, term, MAXT);
  int res = 0;
  if (n < 0) res = 1;
  else if (d > 0) {
    for (int t = 0; t < n && !res; t++)
      for (int a = 0; a < 3 && !res; a++) for (int b = a+1; b < 3 && !res; b++)
        res = cut_rec(&term[t], a, b, d);
  }
  s = hget(0, &K);
  if (s && !timeup) { if (res) { if (d < s->wond) s->wond = d; } else if (d > s->lostd) s->lostd = d; }
  return res;
}
/* exhaustive AND-OR search over all splits (fallback) */
static int ex(const Mat *X, int d) {
  if (timeup) return 0;
  nodes++;
  Mat K = canon(X);
  Slot *s = hget(1, &K);
  if (s && s->wond <= d) return 1;
  if (s && s->lostd >= d) return 0;
  Mat term[MAXT]; red_budget = 20000;
  int n = reduce_all(X, term, MAXT);
  int res = 0;
  if (n < 0) res = 1;
  else if (d > 0) {
    for (int t = 0; t < n && !res; t++)
      for (int c = 0; c < 3 && !res; c++) for (int e = c+1; e < 3 && !res; e++) {
        Mat A = term[t], B = term[t];
        for (int r = 0; r < 3; r++) { E(A,r,e) += E(term[t],r,c); E(B,r,c) += E(term[t],r,e); }
        res = ex(&A, d-1) && ex(&B, d-1);
      }
  }
  s = hget(1, &K);
  if (s && !timeup) { if (res) { if (d < s->wond) s->wond = d; } else if (d > s->lostd) s->lostd = d; }
  return res;
}
static int mindepth(const Mat *X, int D) { for (int d = 0; d <= D; d++) { if (win(X,d)) return d; if (timeup) return -2; } return -1; }
static void pm(const Mat *X) { printf("[[%d,%d,%d],[%d,%d,%d],[%d,%d,%d]]", X->e[0],X->e[1],X->e[2],X->e[3],X->e[4],X->e[5],X->e[6],X->e[7],X->e[8]); }

int main(int argc, char **argv) {
  int S = argc > 1 ? atoi(argv[1]) : 30, D = argc > 2 ? atoi(argv[2]) : 12, DX = argc > 3 ? atoi(argv[3]) : 6;
  int limit = argc > 4 ? atoi(argv[4]) : 540;
  signal(SIGALRM, on_alarm); alarm(limit);
  H[0] = calloc(HSIZE, sizeof(Slot)); H[1] = calloc(HSIZE, sizeof(Slot));
  if (!H[0] || !H[1]) { printf("alloc failed\n"); return 1; }
  Mat M = {{3,1,0,1,1,1,0,1,2}}, X9 = {{9,2,0,2,1,1,0,1,2}}, NEG = {{1,0,0,0,1,0,-1,0,1}};
  Mat NEG2 = {{1,0,-1,0,1,0,0,0,1}}; /* col-negative control too */
  printf("calib: M stuck=%d det=%lld mindepth=%d\n", stuck(&M), det(&M), mindepth(&M, D));
  printf("calib: X9 stuck=%d det=%lld mindepth=%d\n", stuck(&X9), det(&X9), mindepth(&X9, D));
  /* negative controls: the part of the cell outside Delta can never be won, so these must LOSE */
  printf("control: NEG strategy(D=%d)=%d exhaustive(d=%d)=%d (both must be 0)\n", D, win(&NEG, D), DX, ex(&NEG, DX));
  printf("control: NEG2 strategy(D=%d)=%d exhaustive(d=%d)=%d (both must be 0)\n", D, win(&NEG2, D), DX, ex(&NEG2, DX));
  fflush(stdout);
  long long ndeep = 0, nprint = 0; long long cand = 0, nstuck = 0, nwon = 0, nfail = 0, nexwon = 0, hist[64] = {0};
  int a[9];
  time_t t0 = time(NULL); int lastS = -1;
  for (int s = 3; s <= S; s++)
  for (a[0] = 0; a[0] <= s; a[0]++)
  for (a[1] = 0; a[0]+a[1] <= s; a[1]++)
  for (a[2] = 0; a[0]+a[1]+a[2] <= s; a[2]++)
  for (a[3] = 0; a[0]+a[1]+a[2]+a[3] <= s; a[3]++)
  for (a[4] = 0; a[0]+a[1]+a[2]+a[3]+a[4] <= s; a[4]++)
  for (a[5] = 0; a[0]+a[1]+a[2]+a[3]+a[4]+a[5] <= s; a[5]++)
  for (a[6] = 0; a[0]+a[1]+a[2]+a[3]+a[4]+a[5]+a[6] <= s; a[6]++)
  for (a[7] = 0; a[0]+a[1]+a[2]+a[3]+a[4]+a[5]+a[6]+a[7] <= s; a[7]++) {
    a[8] = s - (a[0]+a[1]+a[2]+a[3]+a[4]+a[5]+a[6]+a[7]);
    if (s != lastS) { if (lastS >= 0) { printf("sum<=%d complete: stuck=%lld won=%lld exwon=%lld fail=%lld t=%lds\n", lastS, nstuck, nwon, nexwon, nfail, (long)(time(NULL)-t0)); fflush(stdout); } lastS = s; }
    if (timeup) goto done;
    Mat X; memcpy(X.e, a, sizeof a);
    long long dt = det(&X);
    if (dt != 1 && dt != -1) continue;
    if (!stuck(&X)) continue;
    Mat K = canon(&X);
    if (memcmp(K.e, X.e, sizeof X.e)) continue;
    nstuck++;
    int md = mindepth(&X, D);
    if (md == -2) goto done;
    if (md >= 0) { nwon++; hist[md]++; if (md >= 4 && ndeep++ < 40) { printf("deep d=%d sum=%lld ", md, esum(&X)); pm(&X); printf("\n"); } }
    else {
      int r = ex(&X, DX);
      if (r) nexwon++; else nfail++;
      if (nprint++ < 60) { printf(r ? "strategy-fail but exhaustive-won(d<=%d): " : "FAIL (exhaustive d<=%d): ", DX); pm(&X); printf(" sum=%lld\n", esum(&X)); }
    }
    cand++;
    if ((nstuck % 2000) == 0) { printf("progress: stuck=%lld won=%lld exwon=%lld fail=%lld t=%lds\n", nstuck, nwon, nexwon, nfail, (long)(time(NULL)-t0)); fflush(stdout); }
  }
done:
  printf("%s S=%d D=%d DX=%d: stuck canonical=%lld strategy-won=%lld exhaustive-only=%lld FAIL=%lld nodes=%lld t=%lds\n",
         timeup ? "TIMEOUT(partial)" : "DONE", S, D, DX, nstuck, nwon, nexwon, nfail, nodes, (long)(time(NULL)-t0));
  printf("depth histogram:"); for (int d = 0; d <= D; d++) printf(" %d:%lld", d, hist[d]); printf("\n");
  return 0;
}
