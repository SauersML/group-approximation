/* Exact pair transfer counts for vertical-slot excursion trails on one concrete
 * decoration of F_2 x Z.
 *
 * usage: pairx c R Na a_1..a_Na Nb b_1..b_Nb  > counts.txt
 *   R  = comma list of allowed vertical runs, e.g. 0,1  or -1,0,1  or -2,-1,0,1,2
 *        (r > 0: r steps z -> z+c ; r < 0: |r| steps z -> z-c)
 *
 * Slot grammar (block i+1, in the fibre of w_i, next letter t):
 *   vertical run r in R, then either nothing or one excursion
 *   (e, u, u'), e in L \ {t_i^-1}, u != u' in D_e, then the step s in D_t,
 *   with s != u' when e = t.
 * Letters 0=a 1=a^-1 2=b 3=b^-1, D_{a^-1} = -D_a.
 *
 * For every context (t_i, t) and every start offset h in [-H, H] (H = sharing
 * radius) prints the counts N(h, h', k) = number of pairs of block data (trail 1
 * from height 0, trail 2 from height h) with |E1 u E2| = k and final offset h'.
 * Also prints the far kernel g(Delta, k) (pairs with no shared edge), which is
 * the exact transfer for |h| > H.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXE 12
typedef struct { int ne; int lab[MAXE]; int lo[MAXE]; int up[MAXE]; int d; } Dat;

static int *S[4], Sn[4];
static int c, R[16], nR;

static Dat *dat; static int ndat, capdat;
static void push(Dat *x) {
  if (ndat == capdat) { capdat = capdat ? 2 * capdat : 1024; dat = realloc(dat, capdat * sizeof(Dat)); }
  dat[ndat++] = *x;
}

static void gen(int t, int o1, int o2) {
  int lets[3] = {t, o1, o2};
  ndat = 0;
  for (int ir = 0; ir < nR; ir++) {
    int r = R[ir];
    Dat base; memset(&base, 0, sizeof base);
    int z = 0;
    if (r > 0) for (int j = 0; j < r; j++) { base.lab[base.ne] = 0; base.lo[base.ne] = j * c; base.up[base.ne] = j * c + c; base.ne++; }
    if (r < 0) for (int j = 1; j <= -r; j++) { base.lab[base.ne] = 0; base.lo[base.ne] = -j * c; base.up[base.ne] = -j * c + c; base.ne++; }
    z = r * c;
    /* no excursion */
    for (int is = 0; is < Sn[t]; is++) {
      Dat x = base; int s = S[t][is];
      x.lab[x.ne] = 1; x.lo[x.ne] = z; x.up[x.ne] = z + s; x.ne++; x.d = z + s; push(&x);
    }
    for (int ie = 0; ie < 3; ie++) {
      int e = lets[ie];
      for (int iu = 0; iu < Sn[e]; iu++) for (int iv = 0; iv < Sn[e]; iv++) {
        if (iu == iv) continue;
        int u = S[e][iu], v = S[e][iv];
        for (int is = 0; is < Sn[t]; is++) {
          int s = S[t][is];
          if (ie == 0 && s == v) continue;
          Dat x = base;
          x.lab[x.ne] = 1 + ie; x.lo[x.ne] = z; x.up[x.ne] = z + u; x.ne++;
          x.lab[x.ne] = 1 + ie; x.lo[x.ne] = z + u - v; x.up[x.ne] = z + u; x.ne++;
          int z2 = z + u - v;
          x.lab[x.ne] = 1; x.lo[x.ne] = z2; x.up[x.ne] = z2 + s; x.ne++;
          x.d = z2 + s;
          /* internal distinctness check (excluded data) */
          int ok = 1;
          for (int i = 0; i < x.ne && ok; i++) for (int j = i + 1; j < x.ne; j++)
            if (x.lab[i] == x.lab[j] && x.lo[i] == x.lo[j] && x.up[i] == x.up[j]) { ok = 0; break; }
          if (!ok) { fprintf(stderr, "internal coincidence excluded\n"); continue; }
          push(&x);
        }
      }
    }
  }
}

/* edge index */
typedef struct { long long key; int idx; } KI;
static KI *ki; static int nki;
#define OFF 100000LL
static long long ekey(int lab, int lo, int up) { return ((long long)lab * 2 * OFF + (lo + OFF)) * 2 * OFF + (up + OFF); }
static int cmpki(const void *a, const void *b) {
  long long x = ((KI *)a)->key, y = ((KI *)b)->key; return x < y ? -1 : x > y;
}
static int lower(long long key) {
  int lo = 0, hi = nki;
  while (lo < hi) { int mid = (lo + hi) / 2; if (ki[mid].key < key) lo = mid + 1; else hi = mid; }
  return lo;
}

int main(int argc, char **argv) {
  int ai = 1;
  c = atoi(argv[ai++]);
  { char *p = argv[ai++]; nR = 0; while (*p) { R[nR++] = strtol(p, &p, 10); if (*p == ',') p++; } }
  int na = atoi(argv[ai++]); int *A = malloc(na * sizeof(int)); for (int i = 0; i < na; i++) A[i] = atoi(argv[ai++]);
  int nb = atoi(argv[ai++]); int *B = malloc(nb * sizeof(int)); for (int i = 0; i < nb; i++) B[i] = atoi(argv[ai++]);
  S[0] = A; Sn[0] = na; S[2] = B; Sn[2] = nb;
  S[1] = malloc(na * sizeof(int)); for (int i = 0; i < na; i++) S[1][i] = -A[i]; Sn[1] = na;
  S[3] = malloc(nb * sizeof(int)); for (int i = 0; i < nb; i++) S[3][i] = -B[i]; Sn[3] = nb;
  int inv[4] = {1, 0, 3, 2};
  printf("c %d R", c); for (int i = 0; i < nR; i++) printf(" %d", R[i]); printf("\n");
  for (int ti = 0; ti < 4; ti++) for (int t = 0; t < 4; t++) {
    if (t == inv[ti]) continue;
    int o[2], no = 0;
    for (int e = 0; e < 4; e++) if (e != inv[ti] && e != t) o[no++] = e;
    gen(t, o[0], o[1]);
    /* ranges */
    int mind = 1 << 30, maxd = -(1 << 30), minlo = 1 << 30, maxlo = -(1 << 30), maxne = 0;
    for (int i = 0; i < ndat; i++) {
      if (dat[i].d < mind) mind = dat[i].d; if (dat[i].d > maxd) maxd = dat[i].d;
      if (dat[i].ne > maxne) maxne = dat[i].ne;
      for (int j = 0; j < dat[i].ne; j++) { if (dat[i].lo[j] < minlo) minlo = dat[i].lo[j]; if (dat[i].lo[j] > maxlo) maxlo = dat[i].lo[j]; }
    }
    int H = maxlo - minlo;
    int DW = maxd - mind;
    int KM = 2 * maxne + 1;
    printf("ctx %d %d ndat %d H %d DW %d KM %d\n", ti, t, ndat, H, DW, KM);
    /* histogram of displacement by ne */
    int nd = DW + 1;
    long long *hist = calloc((size_t)nd * KM, sizeof(long long));
    for (int i = 0; i < ndat; i++) hist[(dat[i].d - mind) * KM + dat[i].ne]++;
    /* far kernel g(Delta,k), Delta = d_b - d_a in [-DW, DW] */
    long long *g = calloc((size_t)(2 * DW + 1) * KM, sizeof(long long));
    for (int da = 0; da < nd; da++) for (int ka = 0; ka < KM; ka++) { long long x = hist[da * KM + ka]; if (!x) continue;
      for (int db = 0; db < nd; db++) for (int kb = 0; ka + kb < KM; kb++) { long long y = hist[db * KM + kb]; if (!y) continue;
        g[(db - da + DW) * KM + ka + kb] += x * y; } }
    for (int D = 0; D <= 2 * DW; D++) for (int k = 0; k < KM; k++) if (g[D * KM + k]) printf("g %d %d %lld\n", D - DW, k, g[D * KM + k]);
    /* index */
    nki = 0; ki = realloc(ki, sizeof(KI) * (size_t)ndat * MAXE);
    for (int i = 0; i < ndat; i++) for (int j = 0; j < dat[i].ne; j++) { ki[nki].key = ekey(dat[i].lab[j], dat[i].lo[j], dat[i].up[j]); ki[nki].idx = i; nki++; }
    qsort(ki, nki, sizeof(KI), cmpki);
    int HW = H + DW;
    long long *N = malloc(sizeof(long long) * (size_t)(2 * HW + 1) * KM);
    for (int h = -H; h <= H; h++) {
      memset(N, 0, sizeof(long long) * (size_t)(2 * HW + 1) * KM);
      /* start from the no-share kernel, then correct the sharing pairs */
      for (int D = -DW; D <= DW; D++) for (int k = 0; k < KM; k++) N[(h + D + HW) * KM + k] += g[(D + DW) * KM + k];
      for (int b = 0; b < ndat; b++) {
        Dat *B2 = &dat[b];
        for (int j = 0; j < B2->ne; j++) {
          long long key = ekey(B2->lab[j], B2->lo[j] + h, B2->up[j] + h);
          int pos = lower(key);
          for (; pos < nki && ki[pos].key == key; pos++) {
            Dat *A2 = &dat[ki[pos].idx];
            /* is some earlier edge of b also in a? then skip (count pair once) */
            int earlier = 0, sh = 0;
            for (int jj = 0; jj < B2->ne; jj++) {
              int in = 0;
              for (int i = 0; i < A2->ne; i++)
                if (A2->lab[i] == B2->lab[jj] && A2->lo[i] == B2->lo[jj] + h && A2->up[i] == B2->up[jj] + h) { in = 1; break; }
              if (in) { sh++; if (jj < j) earlier = 1; }
            }
            if (earlier) continue;
            int hp = h + B2->d - A2->d;
            int k0 = A2->ne + B2->ne;
            N[(hp + HW) * KM + k0]--;
            N[(hp + HW) * KM + k0 - sh]++;
          }
        }
      }
      for (int hp = -HW; hp <= HW; hp++) for (int k = 0; k < KM; k++) if (N[(hp + HW) * KM + k]) printf("n %d %d %d %lld\n", h, hp, k, N[(hp + HW) * KM + k]);
    }
    free(N); free(g); free(hist);
    fflush(stdout);
  }
  return 0;
}
