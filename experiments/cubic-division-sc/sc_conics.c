/* third part (built as sc_p2.c + sc_conics.c = scc): nondegenerate conics of P^2(F_p), i.e. points of
   P^5(F_p) = symmetric 3x3 matrices up to scalars with det != 0, acted on by S -> g S g^T.
   The permutation module of GL_3(F_q) (q odd) on nondegenerate symmetric matrices contains every
   irreducible representation (twisted Frobenius-Schur indicators all +1: Gow; Kawanaka-Matsuyama), so
   the scaling sectors of this space carry cuspidal representations of SL_3(F_p).
   usage: scc run p c0..c8 m twist ctl c1 c2 k seed    (twist 0: scale-invariant mean-zero, 1: Legendre) */
static i64 NP5, OFF[7];
static int8_t *LEG;
static i64 *INV;
static void prep5(i64 i, i64 s[6]) { int j = 0; while (i >= OFF[j + 1]) j++; i64 v = i - OFF[j];
  for (int t = 0; t < j; t++) s[t] = 0; s[j] = 1; for (int t = 5; t > j; t--) { s[t] = v % P; v /= P; } }
static i64 idx5(i64 s[6], i64 *c) { int j = 0; while (!s[j]) j++; *c = s[j]; i64 iv = INV[s[j]], v = 0;
  for (int t = j + 1; t < 6; t++) v = v * P + s[t] * iv % P; return OFF[j] + v; }
static i64 sdet(i64 s[6]) { return md(s[0] * md(s[3] * s[5] - s[4] * s[4]) - s[1] * md(s[1] * s[5] - s[4] * s[2]) + s[2] * md(s[1] * s[4] - s[3] * s[2])); }
static double sturm_count(int k, double *al, double *be, double x) { int cnt = 0; double d = al[0] - x; if (d < 0) cnt++;
  for (int i = 1; i < k; i++) { if (fabs(d) < 1e-300) d = 1e-300; d = al[i] - x - be[i-1] * be[i-1] / d; if (d < 0) cnt++; } return cnt; }
static double extreme(int k, double *al, double *be, int top, double R) { double lo = -R, hi = R;
  for (int it = 0; it < 200; it++) { double mid = 0.5 * (lo + hi); double cc = sturm_count(k, al, be, mid);
    if (top) { if (cc >= k) hi = mid; else lo = mid; } else { if (cc >= 1) hi = mid; else lo = mid; } }
  return 0.5 * (lo + hi); }
static double lehner(double c1, double c2) { double best = 1e9;
  for (int i = 0; i <= 200000; i++) { double t = i * 1e-4; double v = -t + sqrt(t*t + 4*c1*c1) + sqrt(t*t + 4*c2*c2); if (v < best) best = v; }
  return best; }
int main(int argc, char **argv) {
  TH[0] = 2 * cos(2 * M_PI / 7); TH[1] = 2 * cos(6 * M_PI / 7); TH[2] = 2 * cos(4 * M_PI / 7);
  if (argc < 19) { fprintf(stderr, "usage: scc run p c0..c8 m twist ctl c1 c2 k seed\n"); return 64; }
  int c[9]; P = atol(argv[2]); for (int i = 0; i < 9; i++) c[i] = atoi(argv[3 + i]);
  int m = atoi(argv[12]), twist = atoi(argv[13]), ctl = atoi(argv[14]), k = atoi(argv[17]);
  double c1 = atof(argv[15]), c2 = atof(argv[16]); uint64_t seed = strtoull(argv[18], 0, 10);
  i64 p = P; rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
  /* OFF[j+1]-OFF[j] = p^(5-j): number of points whose first nonzero coordinate is j */
  OFF[0] = 0; for (int j = 0; j < 6; j++) { i64 q = 1; for (int t = 0; t < 5 - j; t++) q *= p; OFF[j + 1] = OFF[j] + q; }
  NP5 = OFF[6];
  INV = malloc(sizeof(i64) * p); LEG = malloc(p); INV[0] = 0; LEG[0] = 0;
  for (i64 a = 1; a < p; a++) { INV[a] = pw(a, p - 2); LEG[a] = (pw(a, (p - 1) / 2) == 1) ? 1 : -1; }
  i64 r[3]; int nr = 0; for (i64 t = 0; t < p; t++) if (md(t*t % P * t + t*t - 2*t - 1) == 0) { if (!nr) r[0] = t; nr++; }
  if (nr != 3) { printf("p=%ld does not split in K\n", (long)p); return 1; }
  r[2] = md(r[0] * r[0] - 2); r[1] = md(r[2] * r[2] - 2);
  int cth[9] = {0, 1, 0, 0, 0, 0, 0, 0, 0}; M3 La = Lmod(cth, r), Lu = Lmod(c, r), A, B, g4[4];
  if (det(La) != 1 || det(Lu) != 1) { printf("det check failed\n"); return 1; }
  A = mpow(La, m); B = mpow(mul(mul(Lu, La), minv(Lu)), m);
  if (ctl == 1) { M3 g = rnd_sl3(); B = mul(mul(g, A), minv(g)); }
  if (ctl == 2) { A = rnd_sl3(); B = rnd_sl3(); }
  g4[0] = A; g4[1] = minv(A); g4[2] = B; g4[3] = minv(B); double wt[4] = {c1, c1, c2, c2};
  uint8_t *nd = malloc(NP5); i64 nnd = 0; int32_t *perm[4]; int8_t *sg[4];
  /* SL_3-orbits on nondegenerate conics: det S modulo cubes (scaling multiplies det by a cube); keep the
     orbit of det in the cube class of 1.  f0(S) = LEG[det S] is the invariant section of the Legendre sector. */
  i64 cexp = (p - 1) / ((p - 1) % 3 == 0 ? 3 : 1); double *f0 = calloc(NP5, 8), f0n = 0;
  for (i64 i = 0; i < NP5; i++) { i64 s[6]; prep5(i, s); i64 d = sdet(s); nd[i] = d != 0 && pw(d, cexp) == 1; nnd += nd[i];
    if (nd[i]) { f0[i] = LEG[d]; f0n += 1; } }
  f0n = sqrt(f0n); for (i64 i = 0; i < NP5; i++) f0[i] /= f0n;
  for (int h = 0; h < 4; h++) { perm[h] = malloc(4 * NP5); sg[h] = malloc(NP5); M3 g = g4[h];
    for (i64 i = 0; i < NP5; i++) { i64 s[6], S[3][3], T[3][3], y[6], cc; prep5(i, s);
      S[0][0] = s[0]; S[0][1] = S[1][0] = s[1]; S[0][2] = S[2][0] = s[2]; S[1][1] = s[3]; S[1][2] = S[2][1] = s[4]; S[2][2] = s[5];
      for (int a = 0; a < 3; a++) for (int b = a; b < 3; b++) { i64 acc = 0;
        for (int u = 0; u < 3; u++) { i64 gs = 0; for (int w = 0; w < 3; w++) gs += g.m[a][w] * S[w][u]; acc = (acc + (gs % P) * g.m[b][u]) % P; }
        T[a][b] = acc; }
      y[0] = T[0][0]; y[1] = T[0][1]; y[2] = T[0][2]; y[3] = T[1][1]; y[4] = T[1][2]; y[5] = T[2][2];
      perm[h][i] = (int32_t)idx5(y, &cc); sg[h][i] = LEG[cc]; } }
  for (int h = 0; h < 4; h += 2) for (i64 i = 0; i < NP5; i++)
    if (perm[h + 1][perm[h][i]] != i || nd[perm[h][i]] != nd[i]) { printf("perm check failed h=%d i=%ld\n", h, (long)i); return 1; }
  double *v = malloc(8 * NP5), *w = malloc(8 * NP5), *vp = calloc(NP5, 8), *al = malloc(8 * k), *be = malloc(8 * k), nn = 0, bprev = 0;
  for (i64 i = 0; i < NP5; i++) v[i] = nd[i] ? (double)(xr() % 2000001) / 1e6 - 1 : 0;
  if (!twist) { double mu = 0; for (i64 i = 0; i < NP5; i++) mu += v[i]; mu /= nnd; for (i64 i = 0; i < NP5; i++) if (nd[i]) v[i] -= mu; }
  else { double pr = 0; for (i64 i = 0; i < NP5; i++) pr += v[i] * f0[i]; for (i64 i = 0; i < NP5; i++) v[i] -= pr * f0[i]; }
  for (i64 i = 0; i < NP5; i++) nn += v[i] * v[i]; nn = sqrt(nn); for (i64 i = 0; i < NP5; i++) v[i] /= nn;
  for (int j = 0; j < k; j++) {
    for (i64 i = 0; i < NP5; i++) { double s = 0; for (int h = 0; h < 4; h++) s += wt[h] * (twist ? sg[h][i] : 1) * v[perm[h][i]]; w[i] = s; }
    if (!twist) { double mu = 0; for (i64 i = 0; i < NP5; i++) mu += w[i]; mu /= nnd; for (i64 i = 0; i < NP5; i++) if (nd[i]) w[i] -= mu; }
    else { double pr = 0; for (i64 i = 0; i < NP5; i++) pr += w[i] * f0[i]; for (i64 i = 0; i < NP5; i++) w[i] -= pr * f0[i]; }
    double a = 0; for (i64 i = 0; i < NP5; i++) a += w[i] * v[i]; al[j] = a;
    double b = 0; for (i64 i = 0; i < NP5; i++) { w[i] -= a * v[i] + bprev * vp[i]; b += w[i] * w[i]; }
    b = sqrt(b); be[j] = b; if (b < 1e-12) { k = j + 1; break; }
    for (i64 i = 0; i < NP5; i++) { vp[i] = v[i]; v[i] = w[i] / b; } bprev = b; }
  double R = 2 * (c1 + c2) + 0.5, lmax = extreme(k, al, be, 1, R), lmin = extreme(k, al, be, 0, R), nrm = fmax(lmax, -lmin), lr = lehner(c1, c2);
  printf("p=%ld N=%ld space=conics twist=%d ctl=%d m=%d c1=%g c2=%g k=%d lmax=%.6f lmin=%.6f norm=%.6f regular=%.6f excess=%+.6f\n",
         (long)p, (long)nnd, twist, ctl, m, c1, c2, k, lmax, lmin, nrm, lr, nrm - lr);
  return 0; }
