/* ib_main.c -- second half of ib.c:  cat experiments/cubic-division-sc/sc_p2.c ib_main.c > ib.c
   Extreme Lanczos Ritz values of nonlinear elements of C[F_2] in congruence Schreier
   representations of the thin free pair A = a^m, B = b^m in SL_1(Lambda) (algebra: sc_p2.c).
     ib run p c0..c8 m space ctl elem k seed
   space 0: P^2(F_p), N = p^2+p+1;  space 1: F_p^3 minus 0, N = p^3-1, which carries every
            degenerate principal series Ind_P^G(chi o det) at once.
   ctl   0: A, B = a^m, b^m mod p;  2: A, B Haar-random in SL_3(F_p);
         3: A, B uniformly random permutations of the same N points (Bordenave--Collins control).
   elem  0: A + A^-1 + B + B^-1                      regular norm 2 sqrt 3
         1: AB + (AB)^-1 + A^-1B + (A^-1B)^-1        2 sqrt 3  (AB, A^-1B: free basis, infinite index)
         2: A^2 + A^-2 + B^2 + B^-2 + AB + (AB)^-1   2 sqrt 5  (free basis of the even subgroup)
         3: A + A^-1 + B + B^-1 + AB + (AB)^-1       unknown: compare with ctl 3
         4: A + A^-1 + B + B^-1 + [A,B] + [A,B]^-1   unknown: compare with ctl 3
   Operator f -> sum_w f(w x) over the symmetric word set, constants projected out each step.
   Ritz values never exceed the true extremes, so a positive excess is a genuine outlier. */
static i64 N;
static i64 *INV;
static const char *WORDS[5][6] = {
  {"A", "a", "B", "b", 0, 0}, {"AB", "ba", "aB", "bA", 0, 0}, {"AA", "aa", "BB", "bb", "AB", "ba"},
  {"A", "a", "B", "b", "AB", "ba"}, {"A", "a", "B", "b", "ABab", "BAba"} };
static const double REF[5] = {3.4641016151377544, 3.4641016151377544, 4.4721359549995794, 0, 0};
static i64 pidx(i64 y[3]) {
  if (y[0]) { i64 iv = INV[y[0]]; return (y[1] * iv % P) * P + y[2] * iv % P; }
  if (y[1]) { i64 iv = INV[y[1]]; return P * P + y[2] * iv % P; }
  return P * P + P; }
static void prep(i64 i, i64 x[3]) {
  if (i < P * P) { x[0] = 1; x[1] = i / P; x[2] = i % P; }
  else if (i < P * P + P) { x[0] = 0; x[1] = 1; x[2] = i - P * P; }
  else { x[0] = 0; x[1] = 0; x[2] = 1; } }
static void build(int space, M3 g, int32_t *perm) {
  for (i64 i = 0; i < N; i++) { i64 x[3], y[3];
    if (space == 0) prep(i, x); else { i64 v = i + 1; x[0] = v / (P * P); x[1] = (v / P) % P; x[2] = v % P; }
    for (int r = 0; r < 3; r++) y[r] = (g.m[r][0] * x[0] + g.m[r][1] * x[1] + g.m[r][2] * x[2]) % P;
    perm[i] = (int32_t)(space == 0 ? pidx(y) : y[0] * P * P + y[1] * P + y[2] - 1); } }
static void rnd_perm(int32_t *pf, int32_t *pi) {
  for (i64 i = 0; i < N; i++) pf[i] = (int32_t)i;
  for (i64 i = N - 1; i > 0; i--) { i64 j = (i64)(xr() % (uint64_t)(i + 1)); int32_t t = pf[i]; pf[i] = pf[j]; pf[j] = t; }
  for (i64 i = 0; i < N; i++) pi[pf[i]] = (int32_t)i; }
static double sturm_count(int k, double *al, double *be, double x) { int cnt = 0; double d = al[0] - x; if (d < 0) cnt++;
  for (int i = 1; i < k; i++) { if (fabs(d) < 1e-300) d = 1e-300; d = al[i] - x - be[i-1] * be[i-1] / d; if (d < 0) cnt++; } return cnt; }
static double extreme(int k, double *al, double *be, int top, double R) { double lo = -R, hi = R;
  for (int it = 0; it < 200; it++) { double mid = 0.5 * (lo + hi); double c = sturm_count(k, al, be, mid);
    if (top) { if (c >= k) hi = mid; else lo = mid; } else { if (c >= 1) hi = mid; else lo = mid; } }
  return 0.5 * (lo + hi); }
static int do_run(i64 p, const int *c, int m, int space, int ctl, int elem, int k, uint64_t seed) {
  P = p; N = space == 0 ? p * p + p + 1 : p * p * p - 1; rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
  INV = malloc(sizeof(i64) * p); INV[0] = 0; for (i64 a = 1; a < p; a++) INV[a] = pw(a, p - 2);
  i64 r[3]; int nr = 0; for (i64 t = 0; t < p; t++) if (md(t*t % P * t + t*t - 2*t - 1) == 0) { if (!nr) r[0] = t; nr++; }
  if (nr != 3) { printf("p=%ld does not split in K (roots %d)\n", (long)p, nr); return 1; }
  r[2] = md(r[0] * r[0] - 2); r[1] = md(r[2] * r[2] - 2);
  int cth[9] = {0, 1, 0, 0, 0, 0, 0, 0, 0};
  M3 La = Lmod(cth, r), Lu = Lmod(c, r);
  if (det(La) != 1 || det(Lu) != 1) { printf("det check failed: %ld %ld\n", (long)det(La), (long)det(Lu)); return 1; }
  M3 A = mpow(La, m), B = mpow(mul(mul(Lu, La), minv(Lu)), m);
  if (ctl == 2) { A = rnd_sl3(); B = rnd_sl3(); }
  int32_t *let[4]; for (int h = 0; h < 4; h++) let[h] = malloc(4 * N);
  if (ctl == 3) { rnd_perm(let[0], let[1]); rnd_perm(let[2], let[3]); }
  else { build(space, A, let[0]); build(space, minv(A), let[1]); build(space, B, let[2]); build(space, minv(B), let[3]); }
  for (i64 i = 0; i < N; i++) if (let[1][let[0][i]] != i || let[3][let[2][i]] != i) { printf("inverse check failed\n"); return 1; }
  int nw = 0; while (nw < 6 && WORDS[elem][nw]) nw++;
  int32_t *wp[6];
  for (int q = 0; q < nw; q++) { const char *s = WORDS[elem][q]; int L = (int)strlen(s); wp[q] = malloc(4 * N);
    for (i64 i = 0; i < N; i++) { int32_t j = (int32_t)i;
      for (int l = L - 1; l >= 0; l--) { int h = s[l] == 'A' ? 0 : s[l] == 'a' ? 1 : s[l] == 'B' ? 2 : 3; j = let[h][j]; }
      wp[q][i] = j; } }
  for (int h = 0; h < 4; h++) free(let[h]);
  double *v = malloc(8 * N), *w = malloc(8 * N), *vp = calloc(N, 8), *al = malloc(8 * k), *be = malloc(8 * k);
  double nn = 0, mu = 0; for (i64 i = 0; i < N; i++) { v[i] = (double)(xr() % 2000001) / 1e6 - 1; mu += v[i]; }
  mu /= N; for (i64 i = 0; i < N; i++) { v[i] -= mu; nn += v[i] * v[i]; }
  nn = sqrt(nn); for (i64 i = 0; i < N; i++) v[i] /= nn;
  double bprev = 0;
  for (int j = 0; j < k; j++) {
    for (i64 i = 0; i < N; i++) { double s = 0; for (int q = 0; q < nw; q++) s += v[wp[q][i]]; w[i] = s; }
    mu = 0; for (i64 i = 0; i < N; i++) mu += w[i]; mu /= N; for (i64 i = 0; i < N; i++) w[i] -= mu;
    double a = 0; for (i64 i = 0; i < N; i++) a += w[i] * v[i]; al[j] = a;
    double b = 0; for (i64 i = 0; i < N; i++) { w[i] -= a * v[i] + bprev * vp[i]; b += w[i] * w[i]; }
    b = sqrt(b); be[j] = b; if (b < 1e-12) { k = j + 1; break; }
    for (i64 i = 0; i < N; i++) { vp[i] = v[i]; v[i] = w[i] / b; } bprev = b; }
  double R = nw + 0.5, lmax = extreme(k, al, be, 1, R), lmin = extreme(k, al, be, 0, R), nrm = fmax(lmax, -lmin);
  printf("p=%ld N=%ld space=%d ctl=%d m=%d elem=%d k=%d lmax=%.7f lmin=%.7f norm=%.7f", (long)p, (long)N, space, ctl, m, elem, k,
         lmax, lmin, nrm);
  if (REF[elem] > 0) printf(" excess=%+.7f", nrm - REF[elem]);
  printf("\n");
  return 0; }
int main(int argc, char **argv) {
  TH[0] = 2 * cos(2 * M_PI / 7); TH[1] = 2 * cos(6 * M_PI / 7); TH[2] = 2 * cos(4 * M_PI / 7);
  if (argc >= 18 && !strcmp(argv[1], "run")) { int c[9]; for (int i = 0; i < 9; i++) c[i] = atoi(argv[3 + i]);
    return do_run(atol(argv[2]), c, atoi(argv[12]), atoi(argv[13]), atoi(argv[14]), atoi(argv[15]), atoi(argv[16]),
                  strtoull(argv[17], 0, 10)); }
  fprintf(stderr, "usage: ib run p c0..c8 m space ctl elem k seed\n"); return 64; }
