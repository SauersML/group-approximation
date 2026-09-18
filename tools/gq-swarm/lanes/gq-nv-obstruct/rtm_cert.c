/* rtm_cert.c (from rtm_induce.c; prints the first conflicting pair per k as a certificate) -- for one machine and start (anchored zero tape), choose Y = the local types tau (phase, state,
 * head cell, two neighbours) whose level overhead v_j(tau) = n_{j+1}(tau) - 2 n_j(tau) vanishes on the last L
 * levels; then report (1) the maximal gap between consecutive Y-times, (2) Y-counts at the frontier times,
 * (3) for k = 1..K and window radius r, whether (window at Y-time) determines the induced index mod 2^k,
 *     counting conflicts (the orbit starts at t = 0, taken as phase 0 at every level).
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_induce n g mask beta start_state start_phase steps L K rmul radd  (radius r = rmul*k + radd)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, g, mask, dir[16], perm[128];
static long W = 1L << 23;

static void run(unsigned char *tape, int s0, int ph0, long steps, long *cnt, int NT, int *inY, long *ytimes,
                long *ny, long *tj, int *nj, long (*snap)[1024], int wantY, int K, int rmul, int radd,
                long *conf, long *ndist) {
    memset(tape, 0, W); long h = W / 2; tape[h] = 1; int s = s0, phase = ph0;
    long maxr = h, minl = h; int njr = 0, njl = 0; long tr[64], tl[64];
    static long (*snr)[1024], (*snl)[1024];
    if (!snr) { snr = malloc(64 * sizeof *snr); snl = malloc(64 * sizeof *snl); }
    memset(cnt, 0, NT * sizeof(long));
    long yi = 0, lastY = -1, maxgap = 0;
    /* phase tables: hash (window) -> phase for each k */
    #ifndef HSBITS
#define HSBITS 21
#endif
    const long HS = 1L << HSBITS;
    static unsigned long long *hk; static int *hv; static long *T1;
    if (wantY && !hk) { hk = malloc(K * HS * sizeof *hk); hv = malloc(K * HS * sizeof *hv); T1 = malloc(K * HS * sizeof *T1); }
    if (wantY) { memset(hk, 0, K * HS * sizeof *hk); for (int k = 0; k < K; k++) conf[k] = ndist[k] = 0; }
    for (long t = 0; t < steps; t++) {
        int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
        cnt[tau]++;
        if (wantY && inY[tau]) {
            if (lastY >= 0 && t - lastY > maxgap) maxgap = t - lastY;
            lastY = t;
            for (int k = 1; k <= K; k++) {
                int r = rmul * k + radd;
                unsigned long long key = (1469598103934665603ULL ^ (unsigned long long)(phase * n + s + 101)) * 1099511628211ULL; unsigned long long key2 = (14695981039346656037ULL ^ (unsigned long long)(phase * n + s + 7)) * 6364136223846793005ULL;
                for (long c = h - r; c <= h + r; c++) { key = (key ^ (tape[c] + 1)) * 1099511628211ULL; key2 = (key2 ^ (tape[c] + 3)) * 6364136223846793005ULL + 1442695040888963407ULL; } key ^= key2 >> 1;
                key |= 1ULL;
                if (ndist[k - 1] > (HS / 10) * 7) continue;
                long slot = key % HS; unsigned long long *K1 = hk + (k - 1) * HS; int *V1 = hv + (k - 1) * HS;
                int ph = (int)(yi % (1L << k));
                while (K1[slot] && K1[slot] != key) slot = (slot + 1) % HS;
                if (!K1[slot]) { K1[slot] = key; V1[slot] = ph; T1[(k - 1) * HS + slot] = t; ndist[k - 1]++; }
                else if (V1[slot] != ph) { if (conf[k - 1] == 0) printf("CERT k=%d r=%d t1=%ld t2=%ld phase1=%d phase2=%d\n", k, r, T1[(k - 1) * HS + slot], t, V1[slot], ph); conf[k - 1]++; }
            }
            yi++;
        }
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
        if (h <= 64 || h >= W - 64) break;
        if (h > maxr) { maxr = h; if (njr < 64) { tr[njr] = t + 1; memcpy(snr[njr], cnt, NT * sizeof(long)); if (wantY) ytimes[njr] = yi; njr++; } }
        if (h < minl) { minl = h; if (njl < 64) { tl[njl] = t + 1; memcpy(snl[njl], cnt, NT * sizeof(long)); if (wantY) ytimes[32 + njl] = yi; njl++; } }
    }
    if (njr >= njl) { *nj = njr; memcpy(tj, tr, sizeof tr); memcpy(snap, snr, 64 * sizeof *snr); }
    else { *nj = njl; memcpy(tj, tl, sizeof tl); memcpy(snap, snl, 64 * sizeof *snl); if (wantY) memmove(ytimes, ytimes + 32, 32 * sizeof(long)); }
    *ny = maxgap;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); g = atoi(argv[2]); mask = atoi(argv[3]); const char *bs = argv[4];
    int s0 = atoi(argv[5]), ph0 = atoi(argv[6]); long steps = atol(argv[7]); int L = atoi(argv[8]), K = atoi(argv[9]);
    int rmul = atoi(argv[10]), radd = atoi(argv[11]);
    const char *p = bs; for (int i = 0; i < n * g; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
    for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
    int NT = 2 * n * g * g * g;
    unsigned char *tape = malloc(W); long *cnt = malloc(NT * sizeof(long));
    long (*snap)[1024] = malloc(64 * sizeof *snap); long tj[64]; int nj; long gap; long ytimes[64];
    int *inY = calloc(NT, sizeof(int)); long conf[32], nd[32];
    run(tape, s0, ph0, steps, cnt, NT, inY, ytimes, &gap, tj, &nj, snap, 0, K, rmul, radd, conf, nd);
    int ny = 0;
    for (int tau = 0; tau < NT; tau++) {
        if (snap[nj - 1][tau] == 0) continue;
        int ok = 1;
        for (int j = nj - 1 - L; j < nj - 1; j++) if (snap[j + 1][tau] - 2 * snap[j][tau] != 0) ok = 0;
        inY[tau] = ok; ny += ok;
    }
    printf("levels=%d  Y types=%d\n", nj, ny);
    { FILE *yf = fopen("yt.txt", "w"); for (int tau = 0; tau < NT; tau++) if (inY[tau]) { int ph = tau / (n * g * g * g), rest = tau % (n * g * g * g); fprintf(yf, "%d %d %d %d %d\n", ph, rest / (g * g * g), (rest / (g * g)) % g, (rest / g) % g, rest % g); } fclose(yf); }
    run(tape, s0, ph0, steps, cnt, NT, inY, ytimes, &gap, tj, &nj, snap, 1, K, rmul, radd, conf, nd);
    printf("max gap between Y-times: %ld\nY-count at frontier times:", gap);
    for (int j = 0; j < nj && j < 32; j++) printf(" %ld", ytimes[j]); printf("\n");
    for (int k = 1; k <= K; k++) printf("k=%d radius=%d distinct=%ld conflicts=%ld\n", k, rmul * k + radd, nd[k - 1], conf[k - 1]);
    printf("RTM_INDUCE_DONE\n");
    return 0;
}
