/* Exact minimal defect/separation ratios for Thompson's F relators over Sym(n).
 *
 * For A, B in Sym(n) let m1, m2, mc be the numbers of points moved by
 *   R1 = [ab^-1, a^-1ba] = b A A B a a B A b a
 *   R2 = [ab^-1, a^-2ba^2] = b A A A B a a a B A A b a a
 *   C  = [a,b] up to conjugacy = a b A B      (moved points of abAB = points where AB, BA differ)
 * (capital = inverse; a word is a product, last letter acts first).
 * The ratio rho_sum = (m1+m2)/mc and rho_max = max(m1,m2)/mc for mc > 0 do not depend on n-normalization.
 * A runs over one representative per cycle type (simultaneous conjugation preserves all counts),
 * B over all of Sym(n) (lexicographic next_permutation).
 * Output: exact minima with argmin pairs, counts of pairs with ratio < 1, and the lower envelope
 * min(m1+m2) and min(max(m1,m2)) for each mc.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

#define MAXN 16
static int n;
static int npart = 0;
static int parts[400][MAXN + 1]; /* parts[k][0] = number of cycles, then lengths */

static void gen_partitions(int rem, int maxpart, int *cur, int len) {
    if (rem == 0) {
        parts[npart][0] = len;
        for (int i = 0; i < len; i++) parts[npart][i + 1] = cur[i];
        npart++;
        return;
    }
    for (int p = (rem < maxpart ? rem : maxpart); p >= 1; p--) {
        cur[len] = p;
        gen_partitions(rem - p, p, cur, len + 1);
    }
}

static int next_perm(unsigned char *p, int m) {
    int i = m - 2;
    while (i >= 0 && p[i] >= p[i + 1]) i--;
    if (i < 0) return 0;
    int j = m - 1;
    while (p[j] <= p[i]) j--;
    unsigned char t = p[i]; p[i] = p[j]; p[j] = t;
    for (int l = i + 1, r = m - 1; l < r; l++, r--) { t = p[l]; p[l] = p[r]; p[r] = t; }
    return 1;
}

static const char *R1 = "bAABaaBAba";
static const char *R2 = "bAAABaaaBAAbaa";
static const char *CW = "abAB";

static inline int moved(const char *w, const unsigned char *a, const unsigned char *ai,
                        const unsigned char *b, const unsigned char *bi) {
    int L = (int)strlen(w), cnt = 0;
    for (int x = 0; x < n; x++) {
        int y = x;
        for (int k = L - 1; k >= 0; k--) {
            switch (w[k]) {
                case 'a': y = a[y]; break;
                case 'A': y = ai[y]; break;
                case 'b': y = b[y]; break;
                default:  y = bi[y]; break;
            }
        }
        cnt += (y != x);
    }
    return cnt;
}

static unsigned long long class_size(int k) {
    unsigned long long f = 1;
    for (int i = 2; i <= n; i++) f *= (unsigned long long)i;
    int mult[MAXN + 1] = {0};
    for (int c = 1; c <= parts[k][0]; c++) mult[parts[k][c]]++;
    for (int i = 1; i <= n; i++) {
        for (int j = 0; j < mult[i]; j++) f /= (unsigned long long)i;
        for (int j = 2; j <= mult[i]; j++) f /= (unsigned long long)j;
    }
    return f;
}

typedef struct {
    unsigned long long wsep, wlt1_sum, weq1_sum, wlt1_max;
    long long pairs, sep_pairs, lt1_sum, lt1_max, eq1_sum;
    int best_sum_num, best_sum_den, best_max_num, best_max_den;
    unsigned char bs_a[MAXN], bs_b[MAXN], bm_a[MAXN], bm_b[MAXN];
    int env_sum[MAXN + 1], env_max[MAXN + 1];
} acc_t;

static void acc_init(acc_t *s) {
    memset(s, 0, sizeof *s);
    s->best_sum_num = 1000; s->best_sum_den = 1;
    s->best_max_num = 1000; s->best_max_den = 1;
    for (int i = 0; i <= MAXN; i++) { s->env_sum[i] = 1000; s->env_max[i] = 1000; }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: rho n\n"); return 1; }
    n = atoi(argv[1]);
    if (n < 2 || n > MAXN) return 1;
    int cur[MAXN];
    gen_partitions(n, n, cur, 0);
    acc_t tot; acc_init(&tot);
    #pragma omp parallel
    {
        acc_t loc; acc_init(&loc);
        #pragma omp for schedule(dynamic, 1)
        for (int k = 0; k < npart; k++) {
            unsigned char a[MAXN], ai[MAXN], b[MAXN], bi[MAXN];
            int pos = 0;
            for (int c = 1; c <= parts[k][0]; c++) {
                int L = parts[k][c];
                for (int i = 0; i < L; i++) a[pos + i] = (unsigned char)(pos + (i + 1) % L);
                pos += L;
            }
            for (int x = 0; x < n; x++) ai[a[x]] = (unsigned char)x;
            for (int x = 0; x < n; x++) b[x] = (unsigned char)x;
            unsigned long long cs = class_size(k);
            long long s0 = loc.sep_pairs, l0 = loc.lt1_sum, e0 = loc.eq1_sum, x0 = loc.lt1_max;
            do {
                for (int x = 0; x < n; x++) bi[b[x]] = (unsigned char)x;
                loc.pairs++;
                int mc = moved(CW, a, ai, b, bi);
                if (mc == 0) continue;
                int m1 = moved(R1, a, ai, b, bi), m2 = moved(R2, a, ai, b, bi);
                int s = m1 + m2, mx = m1 > m2 ? m1 : m2;
                loc.sep_pairs++;
                if (s < mc) loc.lt1_sum++;
                if (s == mc) loc.eq1_sum++;
                if (mx < mc) loc.lt1_max++;
                if (s < loc.env_sum[mc]) loc.env_sum[mc] = s;
                if (mx < loc.env_max[mc]) loc.env_max[mc] = mx;
                if ((long long)s * loc.best_sum_den < (long long)loc.best_sum_num * mc) {
                    loc.best_sum_num = s; loc.best_sum_den = mc;
                    memcpy(loc.bs_a, a, n); memcpy(loc.bs_b, b, n);
                }
                if ((long long)mx * loc.best_max_den < (long long)loc.best_max_num * mc) {
                    loc.best_max_num = mx; loc.best_max_den = mc;
                    memcpy(loc.bm_a, a, n); memcpy(loc.bm_b, b, n);
                }
            } while (next_perm(b, n));
            loc.wsep += cs * (unsigned long long)(loc.sep_pairs - s0);
            loc.wlt1_sum += cs * (unsigned long long)(loc.lt1_sum - l0);
            loc.weq1_sum += cs * (unsigned long long)(loc.eq1_sum - e0);
            loc.wlt1_max += cs * (unsigned long long)(loc.lt1_max - x0);
        }
        #pragma omp critical
        {
            tot.wsep += loc.wsep; tot.wlt1_sum += loc.wlt1_sum;
            tot.weq1_sum += loc.weq1_sum; tot.wlt1_max += loc.wlt1_max;
            tot.pairs += loc.pairs; tot.sep_pairs += loc.sep_pairs;
            tot.lt1_sum += loc.lt1_sum; tot.lt1_max += loc.lt1_max; tot.eq1_sum += loc.eq1_sum;
            for (int i = 0; i <= n; i++) {
                if (loc.env_sum[i] < tot.env_sum[i]) tot.env_sum[i] = loc.env_sum[i];
                if (loc.env_max[i] < tot.env_max[i]) tot.env_max[i] = loc.env_max[i];
            }
            if ((long long)loc.best_sum_num * tot.best_sum_den < (long long)tot.best_sum_num * loc.best_sum_den) {
                tot.best_sum_num = loc.best_sum_num; tot.best_sum_den = loc.best_sum_den;
                memcpy(tot.bs_a, loc.bs_a, n); memcpy(tot.bs_b, loc.bs_b, n);
            }
            if ((long long)loc.best_max_num * tot.best_max_den < (long long)tot.best_max_num * loc.best_max_den) {
                tot.best_max_num = loc.best_max_num; tot.best_max_den = loc.best_max_den;
                memcpy(tot.bm_a, loc.bm_a, n); memcpy(tot.bm_b, loc.bm_b, n);
            }
        }
    }
    printf("n=%d partitions=%d pairs=%lld separating_pairs=%lld\n", n, npart, tot.pairs, tot.sep_pairs);
    printf("weighted_over_all_pairs: separating=%llu sum<mc=%llu sum==mc=%llu max<mc=%llu\n",
           tot.wsep, tot.wlt1_sum, tot.weq1_sum, tot.wlt1_max);
    printf("min_rho_sum=%d/%d  pairs_with_sum<mc=%lld  pairs_with_sum==mc=%lld\n",
           tot.best_sum_num, tot.best_sum_den, tot.lt1_sum, tot.eq1_sum);
    printf("min_rho_max=%d/%d  pairs_with_max<mc=%lld\n", tot.best_max_num, tot.best_max_den, tot.lt1_max);
    printf("argmin_sum A=");
    for (int i = 0; i < n; i++) printf("%d%s", tot.bs_a[i], i + 1 < n ? "," : "");
    printf(" B=");
    for (int i = 0; i < n; i++) printf("%d%s", tot.bs_b[i], i + 1 < n ? "," : "");
    printf("\nargmin_max A=");
    for (int i = 0; i < n; i++) printf("%d%s", tot.bm_a[i], i + 1 < n ? "," : "");
    printf(" B=");
    for (int i = 0; i < n; i++) printf("%d%s", tot.bm_b[i], i + 1 < n ? "," : "");
    printf("\nenvelope mc: min(m1+m2) min(max(m1,m2))\n");
    for (int i = 1; i <= n; i++)
        if (tot.env_sum[i] < 1000) printf("  mc=%d: %d %d\n", i, tot.env_sum[i], tot.env_max[i]);
    return 0;
}
