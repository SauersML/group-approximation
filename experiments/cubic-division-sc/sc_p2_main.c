/* second half of sc_p2.c: Schreier operators on P^2(F_p) and main */
static i64 N;
static i64 *INV;
/* index of the normalised representative of y (first nonzero coordinate 1); *c = that coordinate */
static i64 pidx(i64 y[3], i64 *c) {
  if (y[0]) { *c = y[0]; i64 iv = INV[y[0]]; return (y[1] * iv % P) * P + y[2] * iv % P; }
  if (y[1]) { *c = y[1]; i64 iv = INV[y[1]]; return P * P + y[2] * iv % P; }
  *c = y[2]; return P * P + P; }
static void prep(i64 i, i64 x[3]) {
  if (i < P * P) { x[0] = 1; x[1] = i / P; x[2] = i % P; }
  else if (i < P * P + P) { x[0] = 0; x[1] = 1; x[2] = i - P * P; }
  else { x[0] = 0; x[1] = 0; x[2] = 1; } }
static void build(M3 g, int32_t *perm, int8_t *sgn) {
  for (i64 i = 0; i < N; i++) { i64 x[3], y[3], c; prep(i, x);
    for (int r = 0; r < 3; r++) y[r] = (g.m[r][0] * x[0] + g.m[r][1] * x[1] + g.m[r][2] * x[2]) % P;
    perm[i] = (int32_t)pidx(y, &c); sgn[i] = (int8_t)((pw(c, (P - 1) / 2) == 1) ? 1 : -1); } }
static double sturm_count(int k, double *al, double *be, double x) { int cnt = 0; double d = al[0] - x; if (d < 0) cnt++;
  for (int i = 1; i < k; i++) { if (fabs(d) < 1e-300) d = 1e-300; d = al[i] - x - be[i-1] * be[i-1] / d; if (d < 0) cnt++; } return cnt; }
static double extreme(int k, double *al, double *be, int top) { double lo = -4.5, hi = 4.5;
  for (int it = 0; it < 200; it++) { double mid = 0.5 * (lo + hi); double c = sturm_count(k, al, be, mid);
    if (top) { if (c >= k) hi = mid; else lo = mid; } else { if (c >= 1) hi = mid; else lo = mid; } }
  return 0.5 * (lo + hi); }
static int do_schreier(i64 p, const int *c, int m, int twist, int ctl, int k, uint64_t seed) {
  P = p; N = p * p + p + 1; rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
  INV = malloc(sizeof(i64) * p); INV[0] = 0; for (i64 a = 1; a < p; a++) INV[a] = pw(a, p - 2);
  i64 r[3]; int nr = 0; for (i64 t = 0; t < p; t++) if (md(t*t % P * t + t*t - 2*t - 1) == 0) { if (!nr) r[0] = t; nr++; }
  if (nr != 3) { printf("p=%ld does not split in K (roots %d)\n", (long)p, nr); return 1; }
  r[2] = md(r[0] * r[0] - 2); r[1] = md(r[2] * r[2] - 2); /* r[1] = sigma^-1(theta), r[2] = sigma(theta) */
  int cth[9] = {0, 1, 0, 0, 0, 0, 0, 0, 0};
  M3 A, B, g4[4]; M3 La = Lmod(cth, r), Lu = Lmod(c, r);
  if (det(La) != 1 || det(Lu) != 1) { printf("det check failed: %ld %ld\n", (long)det(La), (long)det(Lu)); return 1; }
  A = mpow(La, m); B = mpow(mul(mul(Lu, La), minv(Lu)), m);
  if (ctl == 1) { M3 g = rnd_sl3(); B = mul(mul(g, A), minv(g)); }
  if (ctl == 2) { A = rnd_sl3(); B = rnd_sl3(); }
  g4[0] = A; g4[1] = minv(A); g4[2] = B; g4[3] = minv(B);
  int32_t *perm[4]; int8_t *sg[4];
  for (int h = 0; h < 4; h++) { perm[h] = malloc(4 * N); sg[h] = malloc(N); build(g4[h], perm[h], sg[h]); }
  double *v = malloc(8 * N), *w = malloc(8 * N), *vp = calloc(N, 8), *al = malloc(8 * k), *be = malloc(8 * k);
  double nn = 0; for (i64 i = 0; i < N; i++) { v[i] = (double)(xr() % 2000001) / 1e6 - 1; }
  if (twist == 0) { double mu = 0; for (i64 i = 0; i < N; i++) mu += v[i]; mu /= N; for (i64 i = 0; i < N; i++) v[i] -= mu; }
  for (i64 i = 0; i < N; i++) nn += v[i] * v[i]; nn = sqrt(nn); for (i64 i = 0; i < N; i++) v[i] /= nn;
  double bprev = 0;
  for (int j = 0; j < k; j++) {
    for (i64 i = 0; i < N; i++) { double s = 0; for (int h = 0; h < 4; h++) s += (twist ? sg[h][i] : 1) * v[perm[h][i]]; w[i] = s; }
    if (twist == 0) { double mu = 0; for (i64 i = 0; i < N; i++) mu += w[i]; mu /= N; for (i64 i = 0; i < N; i++) w[i] -= mu; }
    double a = 0; for (i64 i = 0; i < N; i++) a += w[i] * v[i]; al[j] = a;
    double b = 0; for (i64 i = 0; i < N; i++) { w[i] -= a * v[i] + bprev * vp[i]; b += w[i] * w[i]; }
    b = sqrt(b); be[j] = b; if (b < 1e-12) { k = j + 1; break; }
    for (i64 i = 0; i < N; i++) { vp[i] = v[i]; v[i] = w[i] / b; } bprev = b; }
  double lmax = extreme(k, al, be, 1), lmin = extreme(k, al, be, 0), nrm = fmax(lmax, -lmin);
  printf("p=%ld N=%ld twist=%d ctl=%d m=%d k=%d lmax=%.6f lmin=%.6f norm=%.6f excess=%+.6f\n", (long)p, (long)N, twist, ctl, m, k,
         lmax, lmin, nrm, nrm - 2 * sqrt(3.0));
  return 0; }
int main(int argc, char **argv) {
  TH[0] = 2 * cos(2 * M_PI / 7); TH[1] = 2 * cos(6 * M_PI / 7); TH[2] = 2 * cos(4 * M_PI / 7);
  if (argc < 2) { fprintf(stderr, "usage: see header\n"); return 64; }
  if (!strcmp(argv[1], "search")) return do_search(atoi(argv[2]));
  int c[9]; if (argc < 11) { fprintf(stderr, "need 9 coefficients\n"); return 64; }
  if (!strcmp(argv[1], "pingpong")) { for (int i = 0; i < 9; i++) c[i] = atoi(argv[2 + i]); return do_pingpong(c, atoi(argv[11])); }
  if (!strcmp(argv[1], "schreier") && argc >= 17) { P = atol(argv[2]); for (int i = 0; i < 9; i++) c[i] = atoi(argv[3 + i]);
    return do_schreier(P, c, atoi(argv[12]), atoi(argv[13]), atoi(argv[14]), atoi(argv[15]), strtoull(argv[16], 0, 10)); }
  fprintf(stderr, "bad mode\n"); return 64; }
