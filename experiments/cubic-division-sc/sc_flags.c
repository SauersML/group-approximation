/* third part (replaces sc_p2_main.c when built as scf): spaces P^2 (twist 0/1) and flags (space 2),
   weighted element c1(A+A^-1) + c2(B+B^-1); regular norm of that element for free A, B by Lehner:
   ||c1(u+u*) + c2(v+v*)|| = min_t [ -t + sqrt(t^2+4c1^2) + sqrt(t^2+4c2^2) ]. */
static i64 N, NP;
static i64 *INV;
static i64 pidx(i64 y[3], i64 *c) {
  if (y[0]) { *c = y[0]; i64 iv = INV[y[0]]; return (y[1] * iv % P) * P + y[2] * iv % P; }
  if (y[1]) { *c = y[1]; i64 iv = INV[y[1]]; return P * P + y[2] * iv % P; }
  *c = y[2]; return P * P + P; }
static void prep(i64 i, i64 x[3]) {
  if (i < P * P) { x[0] = 1; x[1] = i / P; x[2] = i % P; }
  else if (i < P * P + P) { x[0] = 0; x[1] = 1; x[2] = i - P * P; }
  else { x[0] = 0; x[1] = 0; x[2] = 1; } }
/* coordinates (alpha, beta) of a line l through the normalised point x in the basis of x^perp */
static i64 lidx(i64 x[3], i64 l[3]) { i64 al, be;
  if (x[0]) { al = l[1]; be = l[2]; } else if (x[1]) { al = l[0]; be = l[2]; } else { al = l[0]; be = l[1]; }
  return al ? be * INV[al] % P : P; }
static void lrep(i64 x[3], i64 t, i64 l[3]) { i64 al = (t < P) ? 1 : 0, be = (t < P) ? t : 1;
  if (x[0]) { l[0] = md(-x[1] * al - x[2] * be); l[1] = al; l[2] = be; }
  else if (x[1]) { l[0] = al; l[1] = md(-x[2] * be); l[2] = be; }
  else { l[0] = al; l[1] = be; l[2] = 0; } }
static void build(M3 g, M3 gi, int space, int32_t *perm, int8_t *sgn) {
  for (i64 i = 0; i < N; i++) { i64 x[3], y[3], c, ip = (space == 2) ? i / (P + 1) : i; prep(ip, x);
    for (int r = 0; r < 3; r++) y[r] = (g.m[r][0] * x[0] + g.m[r][1] * x[1] + g.m[r][2] * x[2]) % P;
    i64 jp = pidx(y, &c); sgn[i] = (int8_t)((pw(c, (P - 1) / 2) == 1) ? 1 : -1);
    if (space < 2) { perm[i] = (int32_t)jp; continue; }
    i64 l[3], lg[3], yn[3]; lrep(x, i % (P + 1), l);
    for (int r = 0; r < 3; r++) lg[r] = (l[0] * gi.m[0][r] + l[1] * gi.m[1][r] + l[2] * gi.m[2][r]) % P;
    prep(jp, yn); perm[i] = (int32_t)(jp * (P + 1) + lidx(yn, lg)); } }
static double sturm_count(int k, double *al, double *be, double x) { int cnt = 0; double d = al[0] - x; if (d < 0) cnt++;
  for (int i = 1; i < k; i++) { if (fabs(d) < 1e-300) d = 1e-300; d = al[i] - x - be[i-1] * be[i-1] / d; if (d < 0) cnt++; } return cnt; }
static double extreme(int k, double *al, double *be, int top, double R) { double lo = -R, hi = R;
  for (int it = 0; it < 200; it++) { double mid = 0.5 * (lo + hi); double c = sturm_count(k, al, be, mid);
    if (top) { if (c >= k) hi = mid; else lo = mid; } else { if (c >= 1) hi = mid; else lo = mid; } }
  return 0.5 * (lo + hi); }
static double lehner(double c1, double c2) { double best = 1e9;
  for (int i = 0; i <= 200000; i++) { double t = i * 1e-4; double v = -t + sqrt(t*t + 4*c1*c1) + sqrt(t*t + 4*c2*c2); if (v < best) best = v; }
  return best; }
static int do_run(i64 p, const int *c, int m, int space, int ctl, double c1, double c2, int k, uint64_t seed) {
  P = p; NP = p * p + p + 1; N = (space == 2) ? NP * (p + 1) : NP; rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
  INV = malloc(sizeof(i64) * p); INV[0] = 0; for (i64 a = 1; a < p; a++) INV[a] = pw(a, p - 2);
  i64 r[3]; int nr = 0; for (i64 t = 0; t < p; t++) if (md(t*t % P * t + t*t - 2*t - 1) == 0) { if (!nr) r[0] = t; nr++; }
  if (nr != 3) { printf("p=%ld does not split in K\n", (long)p); return 1; }
  r[2] = md(r[0] * r[0] - 2); r[1] = md(r[2] * r[2] - 2);
  int cth[9] = {0, 1, 0, 0, 0, 0, 0, 0, 0}; M3 La = Lmod(cth, r), Lu = Lmod(c, r), A, B, g4[4];
  if (det(La) != 1 || det(Lu) != 1) { printf("det check failed\n"); return 1; }
  A = mpow(La, m); B = mpow(mul(mul(Lu, La), minv(Lu)), m);
  if (ctl == 1) { M3 g = rnd_sl3(); B = mul(mul(g, A), minv(g)); }
  if (ctl == 2) { A = rnd_sl3(); B = rnd_sl3(); }
  g4[0] = A; g4[1] = minv(A); g4[2] = B; g4[3] = minv(B); double wt[4] = {c1, c1, c2, c2};
  int32_t *perm[4]; int8_t *sg[4];
  for (int h = 0; h < 4; h++) { perm[h] = malloc(4 * N); sg[h] = malloc(N); build(g4[h], g4[h ^ 1], space, perm[h], sg[h]); }
  for (int h = 0; h < 4; h += 2) for (i64 i = 0; i < N; i++)
    if (perm[h][i] < 0 || perm[h][i] >= N || perm[h + 1][perm[h][i]] != i) { printf("perm check failed h=%d i=%ld\n", h, (long)i); return 1; }
  int tw = (space == 1);
  double *v = malloc(8 * N), *w = malloc(8 * N), *vp = calloc(N, 8), *al = malloc(8 * k), *be = malloc(8 * k), nn = 0, bprev = 0;
  for (i64 i = 0; i < N; i++) v[i] = (double)(xr() % 2000001) / 1e6 - 1;
  if (!tw) { double mu = 0; for (i64 i = 0; i < N; i++) mu += v[i]; mu /= N; for (i64 i = 0; i < N; i++) v[i] -= mu; }
  for (i64 i = 0; i < N; i++) nn += v[i] * v[i]; nn = sqrt(nn); for (i64 i = 0; i < N; i++) v[i] /= nn;
  for (int j = 0; j < k; j++) {
    for (i64 i = 0; i < N; i++) { double s = 0; for (int h = 0; h < 4; h++) s += wt[h] * (tw ? sg[h][i] : 1) * v[perm[h][i]]; w[i] = s; }
    if (!tw) { double mu = 0; for (i64 i = 0; i < N; i++) mu += w[i]; mu /= N; for (i64 i = 0; i < N; i++) w[i] -= mu; }
    double a = 0; for (i64 i = 0; i < N; i++) a += w[i] * v[i]; al[j] = a;
    double b = 0; for (i64 i = 0; i < N; i++) { w[i] -= a * v[i] + bprev * vp[i]; b += w[i] * w[i]; }
    b = sqrt(b); be[j] = b; if (b < 1e-12) { k = j + 1; break; }
    for (i64 i = 0; i < N; i++) { vp[i] = v[i]; v[i] = w[i] / b; } bprev = b; }
  double R = 2 * (c1 + c2) + 0.5, lmax = extreme(k, al, be, 1, R), lmin = extreme(k, al, be, 0, R), nrm = fmax(lmax, -lmin), lr = lehner(c1, c2);
  printf("p=%ld N=%ld space=%d ctl=%d m=%d c1=%g c2=%g k=%d lmax=%.6f lmin=%.6f norm=%.6f regular=%.6f excess=%+.6f\n",
         (long)p, (long)N, space, ctl, m, c1, c2, k, lmax, lmin, nrm, lr, nrm - lr);
  return 0; }
int main(int argc, char **argv) {
  TH[0] = 2 * cos(2 * M_PI / 7); TH[1] = 2 * cos(6 * M_PI / 7); TH[2] = 2 * cos(4 * M_PI / 7);
  if (argc < 19) { fprintf(stderr, "usage: scf run p c0..c8 m space ctl c1 c2 k seed\n"); return 64; }
  int c[9]; P = atol(argv[2]); for (int i = 0; i < 9; i++) c[i] = atoi(argv[3 + i]);
  return do_run(P, c, atoi(argv[12]), atoi(argv[13]), atoi(argv[14]), atof(argv[15]), atof(argv[16]), atoi(argv[17]), strtoull(argv[18], 0, 10)); }
