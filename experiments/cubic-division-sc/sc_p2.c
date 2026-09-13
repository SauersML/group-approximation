/* sc_p2.c -- Schreier operators of SL_1(Lambda), Lambda = O_K + O_K x + O_K x^2 in the
   cyclic algebra D = (K/Q, sigma, 2), K = Q(theta), theta = 2cos(2pi/7), x^3 = 2,
   x alpha = sigma(alpha) x.  D has invariants 1/3 at 2 and -1/3 at 7: a division algebra.
   Left regular representation on the right K-space D with basis 1, x, x^2:
     L_u = [[a0, 2a2, 2a1], [a1', a0', 2a2'], [a2'', a1'', a0'']],  ' = sigma^-1, '' = sigma^-2.
   Modes:
     search B                      norm-one u = a0 + a1 x + a2 x^2 (a1,a2 not both 0), coeffs in [-B,B]
     pingpong c0..c8 mmax          smallest m with a numerical ping-pong certificate for <a^m, b^m>,
                                   a = L_theta, b = L_u a L_u^-1
     schreier p c0..c8 m twist ctl k seed
                                   extreme Lanczos Ritz values of T(A)+T(A^-1)+T(B)+T(B^-1) on
                                   P^2(F_p), twist 0: mean-zero functions, twist 1: sections twisted
                                   by the Legendre character; ctl 0: A=a^m, B=b^m mod p;
                                   ctl 1: B = random conjugate of A; ctl 2: A, B random in SL_3(F_p). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdint.h>
typedef int64_t i64;
static i64 P;
static i64 md(i64 a) { a %= P; return a < 0 ? a + P : a; }
static i64 pw(i64 a, i64 e) { i64 r = 1; a = md(a); while (e) { if (e & 1) r = r * a % P; a = a * a % P; e >>= 1; } return r; }
typedef struct { i64 m[3][3]; } M3;
static M3 mul(M3 A, M3 B) { M3 C; for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { i64 s = 0;
  for (int k = 0; k < 3; k++) s = (s + A.m[i][k] * B.m[k][j]) % P; C.m[i][j] = s; } return C; }
static M3 mpow(M3 A, long e) { M3 R; memset(&R, 0, sizeof R); for (int i = 0; i < 3; i++) R.m[i][i] = 1;
  while (e) { if (e & 1) R = mul(R, A); A = mul(A, A); e >>= 1; } return R; }
static M3 adj(M3 A) { M3 C; for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) {
  int i1 = (j + 1) % 3, i2 = (j + 2) % 3, j1 = (i + 1) % 3, j2 = (i + 2) % 3;
  C.m[i][j] = md(A.m[i1][j1] * A.m[i2][j2] - A.m[i1][j2] * A.m[i2][j1]); } return C; }
static i64 det(M3 A) { i64 d = 0; M3 C = adj(A); for (int j = 0; j < 3; j++) d += A.m[0][j] * C.m[j][0]; return md(d); }
static M3 minv(M3 A) { i64 di = pw(det(A), P - 2); M3 C = adj(A);
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) C.m[i][j] = C.m[i][j] * di % P; return C; }
static uint64_t rs = 88172645463325252ULL;
static uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static M3 rnd_sl3(void) { M3 A; i64 d; do { for (int i = 0; i < 9; i++) A.m[i / 3][i % 3] = xr() % P; d = det(A); } while (!d);
  i64 di = pw(d, P - 2); for (int j = 0; j < 3; j++) A.m[0][j] = A.m[0][j] * di % P; return A; }
/* theta values: real embedding and mod p */
static double TH[3];
static void Lreal(const int *c, double L[3][3], double th[3]) {
  double a[3][3]; /* a[i][e] = alpha_i evaluated at conjugate e */
  for (int i = 0; i < 3; i++) for (int e = 0; e < 3; e++) a[i][e] = c[3*i] + c[3*i+1] * th[e] + c[3*i+2] * th[e] * th[e];
  L[0][0] = a[0][0]; L[0][1] = 2 * a[2][0]; L[0][2] = 2 * a[1][0];
  L[1][0] = a[1][1]; L[1][1] = a[0][1];   L[1][2] = 2 * a[2][1];
  L[2][0] = a[2][2]; L[2][1] = a[1][2];   L[2][2] = a[0][2]; }
static M3 Lmod(const int *c, i64 r[3]) { M3 L; i64 a[3][3];
  for (int i = 0; i < 3; i++) for (int e = 0; e < 3; e++) a[i][e] = md(c[3*i] + c[3*i+1] * r[e] + md(c[3*i+2]) * (r[e] * r[e] % P));
  L.m[0][0] = a[0][0]; L.m[0][1] = md(2 * a[2][0]); L.m[0][2] = md(2 * a[1][0]);
  L.m[1][0] = a[1][1]; L.m[1][1] = a[0][1];         L.m[1][2] = md(2 * a[2][1]);
  L.m[2][0] = a[2][2]; L.m[2][1] = a[1][2];         L.m[2][2] = a[0][2]; return L; }
static double det3(double A[3][3]) { return A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1]) - A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0])
  + A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0]); }
static void inv3(double A[3][3], double B[3][3]) { double d = det3(A);
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { int i1 = (j+1)%3, i2 = (j+2)%3, j1 = (i+1)%3, j2 = (i+2)%3;
    B[i][j] = (A[i1][j1]*A[i2][j2] - A[i1][j2]*A[i2][j1]) / d; } }
static int do_search(int B) { int c[9], n = 0; double L[3][3]; long tot = 1; for (int i = 0; i < 9; i++) tot *= (2*B+1);
  for (long t = 0; t < tot; t++) { long s = t; for (int i = 0; i < 9; i++) { c[i] = (int)(s % (2*B+1)) - B; s /= (2*B+1); }
    int nz = 0; for (int i = 3; i < 9; i++) nz |= c[i]; if (!nz) continue;
    Lreal(c, L, TH); double d = det3(L); if (fabs(d - 1) < 1e-9) { n++; printf("u");
      for (int i = 0; i < 9; i++) printf(" %d", c[i]); printf("\n"); } }
  fprintf(stderr, "found %d\n", n); return 0; }
/* ping-pong: eigenbasis columns V (unit), eigen-moduli ordered, for h = g^(+-m) */
static int do_pingpong(const int *c, int mmax) {
  double U[3][3], Ui[3][3]; Lreal(c, U, TH); inv3(U, Ui);
  int ord[3] = {0, 1, 2}; /* sort conjugates by |theta| descending */
  for (int i = 0; i < 3; i++) for (int j = i+1; j < 3; j++) if (fabs(TH[ord[j]]) > fabs(TH[ord[i]])) { int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
  for (int m = 1; m <= mmax; m++) {
    double V[4][3][3], Vi[4][3][3], rho[4]; /* h = a^m, a^-m, b^m, b^-m ; inverse pairs (0,1),(2,3) */
    for (int h = 0; h < 4; h++) { int dir = (h % 2 == 0) ? 1 : -1; int e[3];
      for (int i = 0; i < 3; i++) e[i] = dir > 0 ? ord[i] : ord[2 - i];
      double l1 = fabs(TH[e[0]]), l2 = fabs(TH[e[1]]); rho[h] = pow(dir > 0 ? l2 / l1 : l1 / l2, m);
      double E[3][3]; memset(E, 0, sizeof E); for (int k = 0; k < 3; k++) E[e[k]][k] = 1; /* columns: eigenvectors of a */
      for (int i = 0; i < 3; i++) for (int k = 0; k < 3; k++) { double s = 0; if (h < 2) s = E[i][k]; else for (int j = 0; j < 3; j++) s += U[i][j] * E[j][k]; V[h][i][k] = s; }
      for (int k = 0; k < 3; k++) { double nn = 0; for (int i = 0; i < 3; i++) nn += V[h][i][k] * V[h][i][k]; nn = sqrt(nn); for (int i = 0; i < 3; i++) V[h][i][k] /= nn; }
      inv3(V[h], Vi[h]); }
    for (double eps = 0.2; eps > 1e-4; eps *= 0.8) { int ok = 1;
      for (int h = 0; h < 4 && ok; h++) for (int g = h+1; g < 4 && ok; g++) { double dot = 0;
        for (int i = 0; i < 3; i++) dot += V[h][i][0] * V[g][i][0]; if (sqrt(fmax(0, 1 - dot*dot)) < 2.5 * eps) ok = 0; }
      for (int h = 0; h < 4 && ok; h++) { double F = 0; for (int i = 0; i < 9; i++) F += Vi[h][i/3][i%3] * Vi[h][i/3][i%3];
        double delta = 2 * sqrt(3.0) * eps * sqrt(F);
        for (int g = 0; g < 4 && ok; g++) { if (g == (h ^ 1)) continue; double cc[3];
          for (int i = 0; i < 3; i++) { cc[i] = 0; for (int j = 0; j < 3; j++) cc[i] += Vi[h][i][j] * V[g][j][0]; }
          double S = fabs(cc[1]) + fabs(cc[2]) + delta, c1 = fabs(cc[0]) - delta - rho[h] * S;
          if (c1 <= 0 || rho[h] * S / c1 > eps) ok = 0; } }
      if (ok) { printf("certified m=%d eps=%.4g rho_a=%.4g rho_ainv=%.4g\n", m, eps, rho[0], rho[1]); return 0; } } }
  printf("no certificate up to m=%d\n", mmax); return 1; }
