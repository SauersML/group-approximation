/* vanneal.c -- simulated annealing search for almost-homomorphisms V -> Sym(k).
 *
 * Presentation: Bleak--Quick (2.4), right action, generators a,b,c with
 * a^2 = b^3 = c^2 = 1 imposed exactly (all true in V; c^2 = 1 follows from (2.4)).
 * Separation is imposed exactly: a and c are fixed-point-free involutions and
 * b is a fixed-point-free 3-cycle product, so every generator moves all k points
 * (k divisible by 6).  By the character dictionary any fixed positive
 * non-collapse is equivalent, so this is the t = 1 normalization.
 *
 * Objective: average normalized Hamming defect of the six relators
 * r3..r8 = (ab)^4, c^-1(ac)^2 a, and the four long words of (2.4):
 *   defect(r) = |{x : x.r != x}| / k.
 * Moves: conjugate one generator by a random transposition (keeps cycle type).
 * Output: best average defect and per-relator defects.
 *
 * Numerics only suggest; they prove nothing about soficity of V.
 *
 * usage: vanneal k iters T0 T1 seed
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static unsigned long long rs;
static unsigned long long rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void){ return (rnd() >> 11) * (1.0/9007199254740992.0); }

/* word letters: 0=a,1=b,2=c ; inverse: +3 */
static const char *RELS[6] = {
 "(ab)^4",
 "c^-1(ac)^2a",
 "(cab^-1aba)^2cb(cabab^-1a)^2",
 "a(cb)^2a(b^-1c)^2bcabcb^-1cab^-1acb^-1(cb)^2ab^-1",
 "ab^-1cbc(ab^-1)^2cbcb^-1a(b^-1c)^2babcb^-1cab^-1",
 "ca(b^-1c)^2bacabacbc(b^-1ca)^2b(cb^-1)^2(acb)^2cb^-1cab^-1"
};
static int W[6][256]; static int WL[6];

static int parse(const char *s, int *i, int *out, int n){
  while (s[*i] && s[*i] != ')'){
    if (s[*i] == '('){
      int buf[256]; int m = 0; (*i)++;
      m = parse(s, i, buf, 0); (*i)++; /* skip ')' */
      int rep = 1;
      if (s[*i] == '^'){ (*i)++; rep = atoi(s + *i); while (s[*i]=='-'||(s[*i]>='0'&&s[*i]<='9')) (*i)++; }
      for (int r = 0; r < rep; r++) for (int j = 0; j < m; j++) out[n++] = buf[j];
    } else {
      int L = s[*i] - 'a'; (*i)++;
      if (s[*i] == '^'){
        (*i)++;
        if (s[*i] == '-'){ (*i) += 2; out[n++] = L + 3; }
        else { int rep = atoi(s + *i); while (s[*i]>='0'&&s[*i]<='9') (*i)++; for (int r=0;r<rep;r++) out[n++] = L; }
      } else out[n++] = L;
    }
  }
  return n;
}

static int k;
static int *P[6]; /* a,b,c and inverses */
static int *tmp1, *tmp2;

static void set_inv(int g){ for (int x = 0; x < k; x++) P[g+3][P[g][x]] = x; }

static double rel_defect(int r){
  for (int x = 0; x < k; x++) tmp1[x] = x;
  for (int j = 0; j < WL[r]; j++){ int *p = P[W[r][j]]; for (int x = 0; x < k; x++) tmp1[x] = p[tmp1[x]]; }
  int mv = 0; for (int x = 0; x < k; x++) if (tmp1[x] != x) mv++;
  return (double)mv / k;
}
static double avg_defect(double *per){
  double s = 0; for (int r = 0; r < 6; r++){ double d = rel_defect(r); if (per) per[r] = d; s += d; }
  return s / 6.0;
}
/* conjugate generator g by transposition (u v) */
static void conj_transp(int g, int u, int v){
  int *p = P[g];
  /* new p' = t p t, t=(u v): p'(x) = t(p(t(x))) */
  for (int x = 0; x < k; x++) tmp2[x] = p[x];
  for (int x = 0; x < k; x++){
    int tx = (x==u)?v:(x==v)?u:x;
    int y = tmp2[tx];
    p[x] = (y==u)?v:(y==v)?u:y;
  }
  set_inv(g);
}

int main(int argc, char **argv){
  if (argc < 6){ fprintf(stderr, "usage: vanneal k iters T0 T1 seed\n"); return 1; }
  k = atoi(argv[1]); long iters = atol(argv[2]); double T0 = atof(argv[3]), T1 = atof(argv[4]);
  rs = strtoull(argv[5], 0, 10) * 2654435761ULL + 12345;
  if (k % 6){ fprintf(stderr, "k must be divisible by 6\n"); return 1; }
  for (int r = 0; r < 6; r++){ int i = 0; WL[r] = parse(RELS[r], &i, W[r], 0); }
  for (int g = 0; g < 6; g++) P[g] = malloc(sizeof(int)*k);
  tmp1 = malloc(sizeof(int)*k); tmp2 = malloc(sizeof(int)*k);
  /* random fpf involutions a,c and fpf order-3 b from random permutations of the base pattern */
  int *perm = malloc(sizeof(int)*k);
  for (int g = 0; g < 3; g++){
    for (int x = 0; x < k; x++) perm[x] = x;
    for (int x = k-1; x > 0; x--){ int j = rnd() % (x+1); int t = perm[x]; perm[x] = perm[j]; perm[j] = t; }
    if (g == 1){ for (int x = 0; x < k; x += 3){ P[1][perm[x]] = perm[x+1]; P[1][perm[x+1]] = perm[x+2]; P[1][perm[x+2]] = perm[x]; } }
    else { for (int x = 0; x < k; x += 2){ P[g][perm[x]] = perm[x+1]; P[g][perm[x+1]] = perm[x]; } }
    set_inv(g);
  }
  double per[6], cur = avg_defect(per), best = cur, bestper[6];
  memcpy(bestper, per, sizeof per);
  int *save = malloc(sizeof(int)*k);
  for (long it = 0; it < iters; it++){
    double T = T0 * pow(T1/T0, (double)it/iters);
    int g = rnd() % 3; int u = rnd() % k, v = rnd() % k; if (u == v) continue;
    memcpy(save, P[g], sizeof(int)*k);
    conj_transp(g, u, v);
    double nd = avg_defect(per);
    if (nd <= cur || urand() < exp((cur - nd) / T)){ cur = nd; if (cur < best){ best = cur; memcpy(bestper, per, sizeof per); } }
    else { memcpy(P[g], save, sizeof(int)*k); set_inv(g); }
  }
  /* baseline: defect of random fpf generators (fresh) */
  printf("k=%d iters=%ld T0=%g T1=%g seed=%s best_avg=%.5f per:", k, iters, T0, T1, argv[5], best);
  for (int r = 0; r < 6; r++) printf(" %.4f", bestper[r]);
  printf("\n");
  return 0;
}
