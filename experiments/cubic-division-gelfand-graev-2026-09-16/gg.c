/* gg.c -- the Gelfand--Graev sector of the prime-level congruence representation of
   Gamma = SL_1(Lambda), with the algebra and generators exactly as in
   experiments/cubic-division-sc/sc_p2.c (copied verbatim into algebra.inc).
   Build:  gcc -O2 -o gg gg.c -lm
   Every nontrivial irreducible representation of SL_3(F_p) is a constituent of
   l^2_0(F_p^3 minus 0) or of GG_p = sum_a Ind_U^G psi_a,  psi_a(u) = e((u12 + a u23)/p),
   a over F_p^x / cubes; so ||l^2_0(SL_3(F_p))(z)|| = max(||vector sector||, max_a ||Ind psi_a||).
   G/U = {(v, w) : v in F_p^3 minus 0, w != 0, w_i = 0 at the first nonzero coordinate i of v},
   section s(v, w) = (v, w, w3), w3 = e_k / det(v, w, e_k), k the coordinate outside {pivot v, pivot w}.
   g s(x) = s(gx) u(g, x) with u(g, x) upper unitriangular;  pi(g) delta_x = psi(u(g, x)) delta_gx.
     gg test p                              cocycle and character checks (Haar-random elements)
     gg run p c0..c8 m ctl a k seed         extreme Lanczos Ritz values of A + A^-1 + B + B^-1
        a >= 1: Ind_U^G psi_a;  a = 0: l^2_0(F_p^3 minus 0)
        ctl 0: A, B = a^m, b^m mod p; 1: B = Haar-random conjugate of A; 2: Haar-random pair */
#include "algebra.inc"
#include <complex.h>
static i64 N, NW;
static i64 *INV;
static int pivot(const i64 v[3]) { return v[0] ? 0 : (v[1] ? 1 : 2); }
static i64 triple(const i64 v[3], const i64 w[3], const i64 u[3]) {
  return md(v[0] * md(w[1] * u[2] - w[2] * u[1]) + v[1] * md(w[2] * u[0] - w[0] * u[2]) + v[2] * md(w[0] * u[1] - w[1] * u[0])); }
static void apply(M3 g, const i64 x[3], i64 y[3]) { for (int r = 0; r < 3; r++) y[r] = (g.m[r][0] * x[0] + g.m[r][1] * x[1] + g.m[r][2] * x[2]) % P; }
static void decode(i64 idx, i64 v[3], i64 w[3]) {
  i64 vi = idx / NW + 1, wi = idx % NW + 1; v[0] = vi / (P * P); v[1] = (vi / P) % P; v[2] = vi % P;
  int i = pivot(v), a = (i == 0) ? 1 : 0, b = (i == 2) ? 1 : 2; w[i] = 0; w[a] = wi / P; w[b] = wi % P; }
static i64 encode(const i64 v[3], const i64 w[3]) {
  int i = pivot(v), a = (i == 0) ? 1 : 0, b = (i == 2) ? 1 : 2;
  return (v[0] * P * P + v[1] * P + v[2] - 1) * NW + (w[a] * P + w[b] - 1); }
/* coset action; returns 0 on an internal inconsistency */
static int act(M3 g, i64 idx, i64 *out, int *u12, int *u23) {
  i64 v[3], w[3], e[3] = {0, 0, 0}, w3[3] = {0, 0, 0}, vp[3], gw[3], gw3[3], wp[3];
  decode(idx, v, w); int i = pivot(v), j = pivot(w), k = 3 - i - j; if (j == i) return 0;
  e[k] = 1; i64 d = triple(v, w, e); if (!d) return 0; w3[k] = INV[d];
  apply(g, v, vp); apply(g, w, gw); apply(g, w3, gw3);
  int ip = pivot(vp); i64 c = gw[ip] * INV[vp[ip]] % P;
  for (int r = 0; r < 3; r++) wp[r] = md(gw[r] - c * vp[r]);
  int jp = pivot(wp), kp = 3 - ip - jp; if (jp == ip || !wp[jp]) return 0;
  i64 al = gw3[ip] * INV[vp[ip]] % P, be = md(gw3[jp] - al * vp[jp]) * INV[wp[jp]] % P;
  i64 ek[3] = {0, 0, 0}; ek[kp] = 1; i64 dp = triple(vp, wp, ek); if (!dp) return 0;
  for (int r = 0; r < 3; r++) { i64 t = md(gw3[r] - al * vp[r] - be * wp[r]); if (t != (r == kp ? INV[dp] : 0)) return 0; }
  *out = encode(vp, wp); *u12 = (int)c; *u23 = (int)be; return 1; }
static i64 cube_rep(int t, int *kk) { /* representatives 1, g, g^2 of F_p^x / cubes */
  *kk = ((P - 1) % 3 == 0) ? 3 : 1; if (t == 0) return 1; i64 g = 2;
  for (;; g++) { int ok = 1; for (i64 q = 2; q < P; q++) if ((P - 1) % q == 0) { int pr = 1; for (i64 r = 2; r * r <= q; r++) if (q % r == 0) pr = 0;
        if (pr && pw(g, (P - 1) / q) == 1) ok = 0; } if (ok) break; }
  return pw(g, t); }
static void init(i64 p) { P = p; NW = p * p - 1; N = (p * p * p - 1) * NW;
  INV = malloc(sizeof(i64) * p); INV[0] = 0; for (i64 a = 1; a < p; a++) INV[a] = pw(a, p - 2); }
static M3 conjg(M3 x, M3 g) { return mul(mul(g, x), minv(g)); }
static double complex trace_a(M3 g, i64 a, double complex *E) { double complex s = 0;
  for (i64 x = 0; x < N; x++) { i64 y; int u12, u23; if (!act(g, x, &y, &u12, &u23)) { printf("act failure\n"); exit(1); }
    if (y == x) s += E[(u12 + a * u23) % P]; } return s; }
static int do_test(i64 p, uint64_t seed) {
  init(p); rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
  int kk; cube_rep(0, &kk); double complex *E = malloc(sizeof(double complex) * p);
  for (i64 t = 0; t < p; t++) E[t] = cexp(2 * M_PI * I * (double)t / (double)p);
  long bad = 0, tot = 0; M3 Id; memset(&Id, 0, sizeof Id); for (int i = 0; i < 3; i++) Id.m[i][i] = 1;
  for (i64 x = 0; x < N; x++) { i64 y; int a1, b1; if (!act(Id, x, &y, &a1, &b1) || y != x || a1 || b1) bad++; }
  printf("p=%ld N=%ld identity-action failures: %ld\n", (long)p, (long)N, bad); bad = 0;
  for (int t = 0; t < 20; t++) { M3 g = rnd_sl3(), h = rnd_sl3(), gh = mul(g, h);
    for (int s = 0; s < 20000; s++, tot++) { i64 x = (i64)(xr() % (uint64_t)N), y, z, zz; int a1, b1, a2, b2, a3, b3;
      if (!act(h, x, &y, &a1, &b1) || !act(g, y, &z, &a2, &b2) || !act(gh, x, &zz, &a3, &b3)) { bad++; continue; }
      if (z != zz || (a1 + a2) % P != a3 || (b1 + b2) % P != b3) bad++; } }
  printf("cocycle u(gh,x) = u(g,hx) u(h,x) failures: %ld of %ld\n", bad, tot);
  M3 el[8]; const char *nm[8]; int ne = 0; memset(el, 0, sizeof el);
  el[ne] = Id; nm[ne++] = "identity         pred per a: (p^2-1)(p^3-1)";
  el[ne] = Id; el[ne].m[0][2] = 1; nm[ne++] = "transvection     pred per a: -(p^2-1)";
  for (int t = 0; t < kk; t++) { el[ne] = Id; el[ne].m[0][1] = 1; el[ne].m[1][2] = cube_rep(t, &kk); nm[ne++] = "regular unipotent pred sum over a: gcd(3,p-1)"; }
  memset(&el[ne], 0, sizeof(M3)); el[ne].m[0][0] = 1; el[ne].m[1][1] = 2; el[ne].m[2][2] = INV[2]; nm[ne++] = "diag(1,2,1/2)    pred 0";
  memset(&el[ne], 0, sizeof(M3)); el[ne].m[0][0] = P - 1; el[ne].m[0][1] = 1; el[ne].m[1][1] = P - 1; el[ne].m[2][2] = 1; nm[ne++] = "(-1 Jordan)+(1)  pred 0";
  el[ne] = rnd_sl3(); nm[ne++] = "random           pred 0 (if not unipotent)";
  for (int e = 0; e < ne; e++) { M3 g = conjg(el[e], rnd_sl3()); double complex sum = 0; printf("%-48s", nm[e]);
    for (int t = 0; t < kk; t++) { double complex tr = trace_a(g, cube_rep(t, &kk), E); sum += tr; printf("  a=%ld: %+.4f%+.4fi", (long)cube_rep(t, &kk), creal(tr), cimag(tr)); }
    printf("  sum: %+.4f%+.4fi\n", creal(sum), cimag(sum)); }
  printf("predicted: identity %ld, transvection %ld\n", (long)((p * p - 1) * (p * p * p - 1)), (long)(-(p * p - 1)));
  return 0; }
static double sturm_count(int k, double *al, double *be, double x) { int cnt = 0; double d = al[0] - x; if (d < 0) cnt++;
  for (int i = 1; i < k; i++) { if (fabs(d) < 1e-300) d = 1e-300; d = al[i] - x - be[i-1] * be[i-1] / d; if (d < 0) cnt++; } return cnt; }
static double extreme(int k, double *al, double *be, int top, double R) { double lo = -R, hi = R;
  for (int it = 0; it < 200; it++) { double mid = 0.5 * (lo + hi); double c = sturm_count(k, al, be, mid);
    if (top) { if (c >= k) hi = mid; else lo = mid; } else { if (c >= 1) hi = mid; else lo = mid; } }
  return 0.5 * (lo + hi); }
static int do_run(i64 p, const int *c, int m, int ctl, int arep, int k, uint64_t seed) {
  init(p); rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
  i64 r[3]; int nr = 0; for (i64 t = 0; t < p; t++) if (md(t*t % P * t + t*t - 2*t - 1) == 0) { if (!nr) r[0] = t; nr++; }
  if (nr != 3) { printf("p=%ld does not split in K\n", (long)p); return 1; }
  r[2] = md(r[0] * r[0] - 2); r[1] = md(r[2] * r[2] - 2);
  int cth[9] = {0, 1, 0, 0, 0, 0, 0, 0, 0}; M3 La = Lmod(cth, r), Lu = Lmod(c, r);
  if (det(La) != 1 || det(Lu) != 1) { printf("det check failed\n"); return 1; }
  M3 A = mpow(La, m), B = mpow(conjg(La, Lu), m);
  if (ctl == 1) B = conjg(A, rnd_sl3());
  if (ctl == 2) { A = rnd_sl3(); B = rnd_sl3(); }
  int kk; cube_rep(0, &kk); int vec = (arep == 0); i64 a = 0;
  if (!vec) { if (arep > kk) { printf("a index out of range (k=%d)\n", kk); return 1; } a = cube_rep(arep - 1, &kk); }
  i64 n = vec ? p * p * p - 1 : N; M3 g4[4] = {A, minv(A), B, minv(B)};
  int32_t *perm[4]; uint8_t *ph[4];
  for (int h = 0; h < 4; h++) { perm[h] = malloc(4 * n); ph[h] = malloc(n);
    for (i64 y = 0; y < n; y++) {
      if (vec) { i64 x[3] = {(y + 1) / (P * P), ((y + 1) / P) % P, (y + 1) % P}, z[3]; apply(g4[h], x, z);
        perm[h][y] = (int32_t)(z[0] * P * P + z[1] * P + z[2] - 1); ph[h][y] = 0; continue; }
      i64 z; int u12, u23; if (!act(g4[h], y, &z, &u12, &u23)) { printf("act failure\n"); return 1; }
      perm[h][y] = (int32_t)z; ph[h][y] = (uint8_t)md(-(u12 + a * u23)); } }
  for (int h = 0; h < 4; h += 2) for (i64 y = 0; y < n; y++)
    if (perm[h + 1][perm[h][y]] != y || (ph[h][y] + ph[h + 1][perm[h][y]]) % P) { printf("inverse check failed\n"); return 1; }
  double complex *E = malloc(sizeof(double complex) * p); for (i64 t = 0; t < p; t++) E[t] = cexp(2 * M_PI * I * (double)t / (double)p);
  double complex *v = malloc(16 * n), *w = malloc(16 * n), *vp = calloc(n, 16); double *al = malloc(8 * k), *be = malloc(8 * k), nn = 0, bprev = 0;
  double complex mu = 0; for (i64 y = 0; y < n; y++) { v[y] = ((double)(xr() % 2000001) / 1e6 - 1) + I * ((double)(xr() % 2000001) / 1e6 - 1); mu += v[y]; }
  if (vec) { mu /= n; for (i64 y = 0; y < n; y++) v[y] -= mu; }
  for (i64 y = 0; y < n; y++) nn += creal(v[y] * conj(v[y])); nn = sqrt(nn); for (i64 y = 0; y < n; y++) v[y] /= nn;
  for (int j = 0; j < k; j++) {
    for (i64 y = 0; y < n; y++) { double complex s = 0; for (int h = 0; h < 4; h++) s += E[ph[h][y]] * v[perm[h][y]]; w[y] = s; }
    if (vec) { mu = 0; for (i64 y = 0; y < n; y++) mu += w[y]; mu /= n; for (i64 y = 0; y < n; y++) w[y] -= mu; }
    double complex aa = 0; for (i64 y = 0; y < n; y++) aa += conj(v[y]) * w[y]; al[j] = creal(aa);
    double b = 0; for (i64 y = 0; y < n; y++) { w[y] -= al[j] * v[y] + bprev * vp[y]; b += creal(w[y] * conj(w[y])); }
    b = sqrt(b); be[j] = b; if (b < 1e-12) { k = j + 1; break; }
    for (i64 y = 0; y < n; y++) { vp[y] = v[y]; v[y] = w[y] / b; } bprev = b; }
  double lmax = extreme(k, al, be, 1, 4.5), lmin = extreme(k, al, be, 0, 4.5), nrm = fmax(lmax, -lmin);
  printf("p=%ld n=%ld sector=%s a=%ld ctl=%d m=%d k=%d lmax=%.7f lmin=%.7f norm=%.7f excess=%+.7f\n", (long)p, (long)n,
         vec ? "vector" : "gelfand-graev", (long)a, ctl, m, k, lmax, lmin, nrm, nrm - 2 * sqrt(3.0));
  return 0; }
int main(int argc, char **argv) {
  TH[0] = 2 * cos(2 * M_PI / 7); TH[1] = 2 * cos(6 * M_PI / 7); TH[2] = 2 * cos(4 * M_PI / 7);
  if (argc >= 3 && !strcmp(argv[1], "test")) return do_test(atol(argv[2]), argc > 3 ? strtoull(argv[3], 0, 10) : 1);
  if (argc >= 17 && !strcmp(argv[1], "run")) { int c[9]; for (int i = 0; i < 9; i++) c[i] = atoi(argv[3 + i]);
    return do_run(atol(argv[2]), c, atoi(argv[12]), atoi(argv[13]), atoi(argv[14]), atoi(argv[15]), strtoull(argv[16], 0, 10)); }
  fprintf(stderr, "usage: gg test p [seed] | gg run p c0..c8 m ctl a k seed\n"); return 64; }
