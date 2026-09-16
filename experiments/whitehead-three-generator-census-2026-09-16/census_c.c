/* census_c.c -- independent C re-implementation of census.py (same search space, same filters,
 * same symmetry reduction, same certificates C2/C3/C6).  Written separately from census.py so that
 * the per-class counts and residue lists of the two programs can be compared (they must agree
 * exactly for every total length both can reach), and so that totals 16 and 17 are feasible.
 *
 * Words: arrays of letters in {-3,-2,-1,1,2,3} (x1 = 1, x2 = 2, x3 = 3, negative = inverse),
 * ordered as integers, exactly as in census.py, so the canonical representatives coincide.
 *
 * Usage: census_c N NMIN L1 outprefix
 *   tests every pair (r1, r2) with NMIN <= |r1| + |r2| <= N, |r1| <= |r2|, r1 a representative
 *   of a cyclic word up to rotation, inversion and the 48 signed permutations, r2 a cyclic word
 *   up to rotation and inversion; L1 = 0 means every |r1| in 5..N/2, otherwise only |r1| = L1.
 *   Writes outprefix_summary.txt and outprefix_residue.txt.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXL 16
typedef signed char letter;

typedef struct {
    int l;
    size_t n, cap;
    letter *w; /* n * l letters */
} wordlist;

static void wl_push(wordlist *L, const letter *w) {
    if (L->n == L->cap) {
        L->cap = L->cap ? 2 * L->cap : 1024;
        L->w = realloc(L->w, L->cap * L->l);
        if (!L->w) { fprintf(stderr, "out of memory\n"); exit(1); }
    }
    memcpy(L->w + L->n * L->l, w, L->l);
    L->n++;
}

/* compare w (length l) with rotation s of v: <0, 0, >0 */
static int cmp_rot(const letter *w, int l, const letter *v, int s) {
    for (int i = 0; i < l; i++) {
        letter a = w[i], b = v[(s + i) % l];
        if (a != b) return a < b ? -1 : 1;
    }
    return 0;
}

/* w is the least word among the rotations of w and of w^-1 */
static int is_canon(const letter *w, int l) {
    letter inv[MAXL];
    for (int i = 0; i < l; i++) inv[i] = -w[l - 1 - i];
    for (int s = 1; s < l; s++) if (cmp_rot(w, l, w, s) > 0) return 0;
    for (int s = 0; s < l; s++) if (cmp_rot(w, l, inv, s) > 0) return 0;
    return 1;
}

/* out = least word among the rotations of w and of w^-1 */
static void canon_ri(const letter *w, int l, letter *out) {
    letter inv[MAXL], cand[MAXL];
    for (int i = 0; i < l; i++) inv[i] = -w[l - 1 - i];
    memcpy(out, w, l);
    for (int t = 0; t < 2; t++) {
        const letter *v = t ? inv : w;
        for (int s = 0; s < l; s++) {
            for (int i = 0; i < l; i++) cand[i] = v[(s + i) % l];
            int c = 0;
            for (int i = 0; i < l; i++) if (cand[i] != out[i]) { c = cand[i] < out[i] ? -1 : 1; break; }
            if (c < 0) memcpy(out, cand, l);
        }
    }
}

/* F1/F2/F3: at least two generators, each present generator at least twice, some odd count */
static int admissible(const letter *w, int l) {
    int c[4] = {0, 0, 0, 0};
    for (int i = 0; i < l; i++) c[abs(w[i])]++;
    int present = 0, odd = 0;
    for (int g = 1; g <= 3; g++) {
        if (c[g] == 0) continue;
        present++;
        if (c[g] < 2) return 0;
        if (c[g] % 2) odd = 1;
    }
    return present >= 2 && odd;
}

static letter cur[MAXL];
static void rec(wordlist *L, int i) {
    int l = L->l;
    if (i == l) {
        if (cur[l - 1] == -cur[0]) return;
        if (is_canon(cur, l) && admissible(cur, l)) wl_push(L, cur);
        return;
    }
    static const letter letters[6] = {-3, -2, -1, 1, 2, 3};
    for (int k = 0; k < 6; k++) {
        letter x = letters[k];
        if (i > 0 && x == -cur[i - 1]) continue;
        if (i > 0 && (x < cur[0] || -x < cur[0])) continue;
        cur[i] = x;
        rec(L, i + 1);
    }
}

static int SP[48][7]; /* SP[k][x+3] = image of letter x */
static void make_sp(void) {
    int perms[6][3] = {{1, 2, 3}, {1, 3, 2}, {2, 1, 3}, {2, 3, 1}, {3, 1, 2}, {3, 2, 1}};
    int k = 0;
    for (int p = 0; p < 6; p++)
        for (int s1 = 1; s1 >= -1; s1 -= 2)
            for (int s2 = 1; s2 >= -1; s2 -= 2)
                for (int s3 = 1; s3 >= -1; s3 -= 2) {
                    int sg[3] = {s1, s2, s3};
                    for (int g = 1; g <= 3; g++) {
                        SP[k][g + 3] = sg[g - 1] * perms[p][g - 1];
                        SP[k][-g + 3] = -sg[g - 1] * perms[p][g - 1];
                    }
                    k++;
                }
}

static int L_len_cmp;
static int cmp_words(const void *a, const void *b) {
    const letter *x = a, *y = b;
    for (int i = 0; i < L_len_cmp; i++) if (x[i] != y[i]) return x[i] < y[i] ? -1 : 1;
    return 0;
}

static void make_reps(const wordlist *src, wordlist *dst) {
    int l = src->l;
    dst->l = l; dst->n = dst->cap = 0; dst->w = NULL;
    letter img[MAXL], c[MAXL], best[MAXL];
    for (size_t j = 0; j < src->n; j++) {
        const letter *w = src->w + j * l;
        for (int k = 0; k < 48; k++) {
            for (int i = 0; i < l; i++) img[i] = (letter)SP[k][w[i] + 3];
            canon_ri(img, l, c);
            if (k == 0) {
                memcpy(best, c, l);
            } else {
                int cc = 0;
                for (int i = 0; i < l; i++) if (c[i] != best[i]) { cc = c[i] < best[i] ? -1 : 1; break; }
                if (cc < 0) memcpy(best, c, l);
            }
        }
        wl_push(dst, best);
    }
    L_len_cmp = l;
    qsort(dst->w, dst->n, l, cmp_words);
    size_t u = 0;
    for (size_t j = 0; j < dst->n; j++)
        if (u == 0 || memcmp(dst->w + (u - 1) * l, dst->w + j * l, l) != 0) {
            memmove(dst->w + u * l, dst->w + j * l, l);
            u++;
        }
    dst->n = u;
}

static void ivalues(const letter *w, int l, const long *phi, long *out) {
    long p = 0;
    for (int i = 0; i < l; i++) {
        long d = w[i] > 0 ? phi[w[i] - 1] : -phi[-w[i] - 1];
        long q = p + d;
        out[i] = p < q ? p : q;
        p = q;
    }
    if (p != 0) { fprintf(stderr, "phi does not kill a relator\n"); exit(2); }
}

static int test_c2(const letter *w, int l, const long *phi) {
    long iv[MAXL];
    ivalues(w, l, phi, iv);
    long m = iv[0];
    for (int i = 1; i < l; i++) if (iv[i] < m) m = iv[i];
    int c[4] = {0, 0, 0, 0};
    for (int i = 0; i < l; i++) if (iv[i] == m) c[abs(w[i])]++;
    for (int g = 1; g <= 3; g++) if (c[g] == 1) return g;
    return 0;
}

static int test_c3(const letter *w, int l, const long *phi) {
    long iv[MAXL];
    ivalues(w, l, phi, iv);
    for (int a = 1; a <= 3; a++) {
        int seen = 0, cnt = 0;
        long mv = 0;
        for (int i = 0; i < l; i++) {
            if (abs(w[i]) != a) continue;
            if (!seen || iv[i] < mv) { mv = iv[i]; cnt = 1; seen = 1; }
            else if (iv[i] == mv) cnt++;
        }
        if (!seen || cnt != 1) continue;
        for (int c = 1; c <= 3; c++) if (c != a && phi[c - 1] != 0) return a;
    }
    return 0;
}

/* support and good sets of m_phi(w) as bitmasks (bit g for generator g) */
static void weak_info(const letter *w, int l, const long *phi, int *supp, int *good) {
    long iv[MAXL];
    ivalues(w, l, phi, iv);
    long m = iv[0];
    for (int i = 1; i < l; i++) if (iv[i] < m) m = iv[i];
    int plus[4] = {0, 0, 0, 0}, minus[4] = {0, 0, 0, 0};
    for (int i = 0; i < l; i++) {
        if (iv[i] != m) continue;
        int g = abs(w[i]);
        int sg = w[i] > 0 ? 1 : -1;
        if (phi[g - 1] < 0) sg = -sg;
        if (sg > 0) plus[g]++; else minus[g]++;
    }
    *supp = *good = 0;
    for (int g = 1; g <= 3; g++) {
        if (plus[g] + minus[g] > 0) *supp |= 1 << g;
        if (plus[g] != minus[g]) *good |= 1 << g;
    }
}

/* returns 0 (residue), 2 (C2), 3 (C3) or 6 (C6) */
static int certify(const letter *r1, int l1, const letter *r2, int l2, const long *phi0) {
    long phi[3];
    for (int s = 1; s >= -1; s -= 2) {
        for (int g = 0; g < 3; g++) phi[g] = s * phi0[g];
        if (test_c2(r1, l1, phi) || test_c2(r2, l2, phi)) return 2;
    }
    for (int s = 1; s >= -1; s -= 2) {
        for (int g = 0; g < 3; g++) phi[g] = s * phi0[g];
        if (test_c3(r1, l1, phi) || test_c3(r2, l2, phi)) return 3;
    }
    for (int s = 1; s >= -1; s -= 2) {
        for (int g = 0; g < 3; g++) phi[g] = s * phi0[g];
        int s1, g1, s2, g2;
        weak_info(r1, l1, phi, &s1, &g1);
        weak_info(r2, l2, phi, &s2, &g2);
        if ((g1 && (g2 & ~s1)) || (g2 && (g1 & ~s2))) return 6;
    }
    return 0;
}

static long gcdl(long a, long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: census_c N NMIN L1 outprefix\n"); return 64; }
    int N = atoi(argv[1]), NMIN = atoi(argv[2]), L1 = atoi(argv[3]);
    const char *prefix = argv[4];
    if (N - 5 >= MAXL) { fprintf(stderr, "N too large\n"); return 64; }
    make_sp();
    int need[MAXL + 1] = {0};
    for (int l1 = 5; l1 <= N / 2; l1++) {
        if (L1 && l1 != L1) continue;
        need[l1] = 1;
        for (int l2 = (l1 > NMIN - l1 ? l1 : NMIN - l1); l2 <= N - l1; l2++) need[l2] = 1;
    }
    wordlist necks[MAXL + 1], reps[MAXL + 1];
    memset(necks, 0, sizeof necks);
    memset(reps, 0, sizeof reps);
    for (int l = 5; l <= MAXL; l++) {
        if (!need[l]) continue;
        necks[l].l = l;
        rec(&necks[l], 0);
    }
    char fn[4096];
    snprintf(fn, sizeof fn, "%s_residue.txt", prefix);
    FILE *fr = fopen(fn, "w");
    snprintf(fn, sizeof fn, "%s_summary.txt", prefix);
    FILE *fs = fopen(fn, "w");
    if (!fr || !fs) { perror("fopen"); return 1; }
    fprintf(fs, "N %d NMIN %d L1 %d\n", N, NMIN, L1);
    for (int l = 5; l <= MAXL; l++) if (need[l]) fprintf(fs, "necks %d %zu\n", l, necks[l].n);
    long total_residue = 0;
    for (int l1 = 5; l1 <= N / 2; l1++) {
        if (L1 && l1 != L1) continue;
        make_reps(&necks[l1], &reps[l1]);
        fprintf(fs, "reps %d %zu\n", l1, reps[l1].n);
        for (int l2 = (l1 > NMIN - l1 ? l1 : NMIN - l1); l2 <= N - l1; l2++) {
            long pairs = 0, c0 = 0, h1z = 0, c2 = 0, c3 = 0, c6 = 0, res = 0;
            for (size_t a = 0; a < reps[l1].n; a++) {
                const letter *r1 = reps[l1].w + a * l1;
                long e1[3] = {0, 0, 0};
                int g1 = 0;
                for (int i = 0; i < l1; i++) {
                    e1[abs(r1[i]) - 1] += r1[i] > 0 ? 1 : -1;
                    g1 |= 1 << abs(r1[i]);
                }
                for (size_t b = 0; b < necks[l2].n; b++) {
                    const letter *r2 = necks[l2].w + b * l2;
                    pairs++;
                    long e2[3] = {0, 0, 0};
                    int g2 = g1;
                    for (int i = 0; i < l2; i++) {
                        e2[abs(r2[i]) - 1] += r2[i] > 0 ? 1 : -1;
                        g2 |= 1 << abs(r2[i]);
                    }
                    if (g2 != 14) { c0++; continue; }
                    long c[3] = {e1[1] * e2[2] - e1[2] * e2[1], e1[2] * e2[0] - e1[0] * e2[2],
                                 e1[0] * e2[1] - e1[1] * e2[0]};
                    if (gcdl(gcdl(c[0], c[1]), c[2]) != 1) continue;
                    h1z++;
                    int t = certify(r1, l1, r2, l2, c);
                    if (t == 2) c2++;
                    else if (t == 3) c3++;
                    else if (t == 6) c6++;
                    else {
                        res++;
                        for (int i = 0; i < l1; i++) fprintf(fr, i ? " %d" : "%d", r1[i]);
                        fprintf(fr, " | ");
                        for (int i = 0; i < l2; i++) fprintf(fr, i ? " %d" : "%d", r2[i]);
                        fprintf(fr, " | phi0=%ld %ld %ld\n", c[0], c[1], c[2]);
                    }
                }
            }
            fprintf(fs, "class %d+%d pairs %ld C0 %ld H1Z %ld C2 %ld C3 %ld C6 %ld residue %ld\n", l1, l2,
                    pairs, c0, h1z, c2, c3, c6, res);
            fflush(fs);
            total_residue += res;
        }
    }
    fprintf(fs, "total_residue %ld\n", total_residue);
    fclose(fs);
    fclose(fr);
    return 0;
}
