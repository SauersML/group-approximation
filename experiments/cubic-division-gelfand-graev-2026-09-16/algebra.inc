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
