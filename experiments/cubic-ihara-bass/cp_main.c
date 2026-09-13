/* cp_main.c -- second half of cp.c:  cat experiments/cubic-division-sc/sc_p2.c cp_main.c > cp.c
   Characteristic-polynomial coincidences among cyclically reduced words of length n in a free pair.
     cp run n c0..c8 m ctl
   ctl 0: A = a^m, B = b^m of SL_1(Lambda), reduced mod two primes P1, P2 ~ 1e9 with P = 1 mod 7, so that
          (Trd w, Trd w^-1) mod P1 and mod P2 identifies the integer characteristic polynomial f_w, up to a
          64-bit hashing error;  ctl 2: A, B Haar-random in SL_3(F_P1), which shows universal coincidences only.
   A word's orbit is its class under cyclic rotation and inversion; words in one orbit share f_w.
   Output: orbits, distinct f_w, f_w classes carrying >= 2 orbits (coincidences beyond conjugacy and
   inversion), and the fraction of orbits whose reversed word has the same f_w. */
static uint64_t enc_rot(uint64_t w, int n, int r) { uint64_t mask = (1ULL << (2 * n)) - 1;
  return r == 0 ? w : (((w >> (2 * r)) | (w << (2 * (n - r)))) & mask); }
static uint64_t inv_word(uint64_t w, int n) { uint64_t v = 0; for (int i = 0; i < n; i++) { int l = (w >> (2 * i)) & 3; v |= (uint64_t)(l ^ 1) << (2 * (n - 1 - i)); } return v; }
static uint64_t rev_word(uint64_t w, int n) { uint64_t v = 0; for (int i = 0; i < n; i++) { int l = (w >> (2 * i)) & 3; v |= (uint64_t)l << (2 * (n - 1 - i)); } return v; }
static uint64_t canon(uint64_t w, int n) { uint64_t best = ~0ULL, iw = inv_word(w, n);
  for (int r = 0; r < n; r++) { uint64_t a = enc_rot(w, n, r), b = enc_rot(iw, n, r); if (a < best) best = a; if (b < best) best = b; } return best; }
typedef struct { uint64_t key, orb; } Rec;
static int cmp_rec(const void *x, const void *y) { const Rec *a = x, *b = y;
  if (a->key != b->key) return a->key < b->key ? -1 : 1; if (a->orb != b->orb) return a->orb < b->orb ? -1 : 1; return 0; }
static M3 GEN[2][4];   /* per prime: A, A^-1, B, B^-1 */
static i64 PR[2];
static uint64_t cpkey(uint64_t w, int n, int np) { uint64_t k = 0;
  for (int q = 0; q < np; q++) { P = PR[q]; M3 M; memset(&M, 0, sizeof M); for (int i = 0; i < 3; i++) M.m[i][i] = 1;
    for (int i = 0; i < n; i++) M = mul(M, GEN[q][(w >> (2 * i)) & 3]);
    i64 t1 = md(M.m[0][0] + M.m[1][1] + M.m[2][2]); M3 C = adj(M); i64 t2 = md(C.m[0][0] + C.m[1][1] + C.m[2][2]);
    k = (k * 0x9E3779B97F4A7C15ULL) ^ ((uint64_t)t1 * (uint64_t)PR[q] + (uint64_t)t2); } return k; }
static int prime_1mod7(i64 p) { if (p % 7 != 1) return 0; for (i64 d = 2; d * d <= p; d++) if (p % d == 0) return 0; return 1; }
static void putword(uint64_t w, int n) { for (int b = 0; b < n; b++) putchar("AaBb"[(w >> (2 * b)) & 3]); }
static int do_run(int n, const int *c, int m, int ctl) {
  if (n < 2 || n > 13) { printf("n out of range\n"); return 64; }
  PR[0] = 1000000000; while (!prime_1mod7(PR[0])) PR[0]++; PR[1] = PR[0] + 1; while (!prime_1mod7(PR[1])) PR[1]++;
  int np = ctl == 2 ? 1 : 2;
  for (int q = 0; q < np; q++) { P = PR[q]; i64 r[3], th = -1;
    for (int it = 0; it < 1000 && th < 0; it++) { i64 g = 2 + (i64)(xr() % (uint64_t)(P - 3)), z = pw(g, (P - 1) / 7);
      if (z != 1) { i64 t = md(z + pw(z, 6)); if (md((t * t % P) * t % P + t * t % P - 2 * t - 1) == 0) th = t; } }
    if (th < 0) { printf("no root found mod %ld\n", (long)P); return 1; }
    r[0] = th; r[2] = md(r[0] * r[0] - 2); r[1] = md(r[2] * r[2] - 2);
    int cth[9] = {0, 1, 0, 0, 0, 0, 0, 0, 0}; M3 La = Lmod(cth, r), Lu = Lmod(c, r);
    if (det(La) != 1 || det(Lu) != 1) { printf("det check failed mod %ld\n", (long)P); return 1; }
    M3 A = mpow(La, m), B = mpow(mul(mul(Lu, La), minv(Lu)), m); if (ctl == 2) { A = rnd_sl3(); B = rnd_sl3(); }
    GEN[q][0] = A; GEN[q][1] = minv(A); GEN[q][2] = B; GEN[q][3] = minv(B); }
  uint64_t tot = 1ULL << (2 * n), cnt = 0, revsame = 0;
  Rec *R = malloc(sizeof(Rec) * (4ULL * (uint64_t)pow(3, n - 1) + 8));
  for (uint64_t w = 0; w < tot; w++) { int ok = 1;
    for (int i = 0; i < n && ok; i++) { int l = (w >> (2 * i)) & 3, l2 = (w >> (2 * ((i + 1) % n))) & 3; if (l2 == (l ^ 1)) ok = 0; }
    if (!ok || canon(w, n) != w) continue;   /* one representative per orbit */
    R[cnt].key = cpkey(w, n, np); R[cnt].orb = w; cnt++;
    if (cpkey(rev_word(w, n), n, np) == R[cnt - 1].key) revsame++; }
  qsort(R, cnt, sizeof(Rec), cmp_rec);
  uint64_t classes = 0, multi = 0, maxorb = 0, inmulti = 0; int shown = 0;
  for (uint64_t i = 0; i < cnt; ) { uint64_t j = i; while (j < cnt && R[j].key == R[i].key) j++;
    uint64_t k = j - i; classes++; if (k > maxorb) maxorb = k;
    if (k >= 2) { multi++; inmulti += k;
      if (shown < 5) { printf("  coincidence (%lu orbits):", (unsigned long)k); for (uint64_t t = i; t < j && t < i + 4; t++) { putchar(' '); putword(R[t].orb, n); } putchar('\n'); shown++; } }
    i = j; }
  printf("n=%d ctl=%d m=%d P1=%ld orbits=%lu distinct_charpoly=%lu classes_with_>=2_orbits=%lu orbits_in_them=%lu max_orbits_per_class=%lu reverse_same_fraction=%.4f\n",
         n, ctl, m, (long)PR[0], (unsigned long)cnt, (unsigned long)classes, (unsigned long)multi, (unsigned long)inmulti,
         (unsigned long)maxorb, (double)revsame / (double)cnt);
  return 0; }
int main(int argc, char **argv) {
  TH[0] = 2 * cos(2 * M_PI / 7); TH[1] = 2 * cos(6 * M_PI / 7); TH[2] = 2 * cos(4 * M_PI / 7);
  if (argc >= 14 && !strcmp(argv[1], "run")) { int c[9]; for (int i = 0; i < 9; i++) c[i] = atoi(argv[3 + i]);
    return do_run(atoi(argv[2]), c, atoi(argv[12]), atoi(argv[13])); }
  fprintf(stderr, "usage: cp run n c0..c8 m ctl\n"); return 64; }
