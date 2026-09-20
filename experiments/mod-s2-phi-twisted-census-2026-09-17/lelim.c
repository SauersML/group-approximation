/* Sparse unit elimination over Lam = (Z/Q)[t]/(t^3 - 1), Q = 3^m.
 *
 * Input (text, stdin):  ngen nrels nvec Q
 *   then nrels + nvec rows, each "len  c a0 a1 a2  c a0 a1 a2 ...".
 * The first nrels rows are relations (may be pivots); the last nvec rows
 * are target vectors (reduced, never pivots).
 * A pivot is an entry whose augmentation a0+a1+a2 is prime to 3 (Lam is
 * local); each step replaces every other row q by q - q[j] piv[j]^-1 piv
 * and deletes piv and column j, an exact isomorphism of the quotient
 * Lam^gens / rows (and of the images of the target vectors).
 * Pivot choice: a currently shortest row with a unit (bucket queue), and in
 * it the unit entry whose column occurs in the fewest rows.
 * Output (stdout): alive columns, surviving nonzero relation rows, the
 * reduced target vectors, same row format.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { int32_t c; uint16_t a[3]; } ent;
typedef struct { ent *e; int32_t len, cap; } row;
typedef struct { int32_t *r; int32_t len, cap; } clist;

static uint32_t Q;
static int32_t ngen, nrels, nvec, nrows;
static row *R;
static clist *C;
static char *rdead, *cdead;
static int32_t *bnext, *bprev, *bkt, *head;   /* bucket queue by length */
static int32_t minb;
static long long nent = 0, peak = 0;

static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n);
    if (!q && n) { fprintf(stderr, "out of memory (%zu)\n", n); exit(3); }
    return q;
}

static void mul(const uint16_t *x, const uint16_t *y, uint16_t *z) {
    for (int k = 0; k < 3; k++) {
        uint64_t s = 0;
        for (int i = 0; i < 3; i++) s += (uint64_t)x[i] * y[(k - i + 3) % 3];
        z[k] = (uint16_t)(s % Q);
    }
}

static int is_unit(const uint16_t *x) { return ((uint32_t)x[0] + x[1] + x[2]) % 3 != 0; }

static long long egcd_inv(long long a, long long m) {
    long long g = m, x = 0, x1 = 1, a1 = a % m;
    while (a1) { long long q = g / a1, t = g - q * a1; g = a1; a1 = t;
                 t = x - q * x1; x = x1; x1 = t; }
    return ((x % m) + m) % m;
}

static void inv(const uint16_t *u, uint16_t *out) {
    uint16_t x[3] = {0, 0, 0}, ux[3], two[3];
    x[0] = (uint16_t)egcd_inv(((uint32_t)u[0] + u[1] + u[2]) % Q, Q);
    for (int it = 0; it < 10; it++) {
        mul(u, x, ux);
        two[0] = (uint16_t)((2 + 2 * Q - ux[0]) % Q);
        two[1] = (uint16_t)((Q - ux[1]) % Q);
        two[2] = (uint16_t)((Q - ux[2]) % Q);
        uint16_t nx[3];
        mul(x, two, nx);
        memcpy(x, nx, sizeof x);
    }
    mul(u, x, ux);
    if (ux[0] != 1 || ux[1] || ux[2]) { fprintf(stderr, "inverse failed\n"); exit(4); }
    memcpy(out, x, sizeof x);
}

static void clist_add(int32_t c, int32_t r) {
    clist *L = &C[c];
    if (L->len == L->cap) { L->cap = L->cap ? 2 * L->cap : 4;
                            L->r = xrealloc(L->r, sizeof(int32_t) * L->cap); }
    L->r[L->len++] = r;
}

static void bucket_remove(int32_t r) {
    int32_t b = bkt[r];
    if (b < 0) return;
    if (bprev[r] >= 0) bnext[bprev[r]] = bnext[r]; else head[b] = bnext[r];
    if (bnext[r] >= 0) bprev[bnext[r]] = bprev[r];
    bkt[r] = -1;
}

static void bucket_insert(int32_t r) {
    int32_t b = R[r].len;
    if (b == 0 || r >= nrels) return;
    bnext[r] = head[b]; bprev[r] = -1;
    if (head[b] >= 0) bprev[head[b]] = r;
    head[b] = r; bkt[r] = b;
    if (b < minb) minb = b;
}

static int32_t find(const row *w, int32_t c) {
    int32_t lo = 0, hi = w->len - 1;
    while (lo <= hi) { int32_t m = (lo + hi) / 2;
        if (w->e[m].c == c) return m;
        if (w->e[m].c < c) lo = m + 1; else hi = m - 1; }
    return -1;
}

/* q <- q - f * p ; register new columns of q in the column lists */
static void axpy(int32_t qi, const uint16_t *f, const row *p) {
    row *q = &R[qi];
    ent *out = xrealloc(NULL, sizeof(ent) * (q->len + p->len));
    int32_t i = 0, j = 0, n = 0;
    while (i < q->len || j < p->len) {
        if (j >= p->len || (i < q->len && q->e[i].c < p->e[j].c)) {
            out[n++] = q->e[i++];
        } else {
            uint16_t fb[3];
            mul(f, p->e[j].a, fb);
            ent e; e.c = p->e[j].c;
            int have = (i < q->len && q->e[i].c == p->e[j].c);
            for (int k = 0; k < 3; k++) {
                uint32_t a = have ? q->e[i].a[k] : 0;
                e.a[k] = (uint16_t)((a + Q - fb[k]) % Q);
            }
            if (e.a[0] || e.a[1] || e.a[2]) {
                out[n++] = e;
                if (!have) clist_add(e.c, qi);
            }
            if (have) i++;
            j++;
        }
    }
    nent += n - q->len;
    free(q->e);
    q->e = xrealloc(out, sizeof(ent) * (n ? n : 1));
    q->len = q->cap = n;
    if (nent > peak) peak = nent;
}

static void read_row(row *w) {
    int32_t len;
    if (scanf("%d", &len) != 1) exit(2);
    w->e = xrealloc(NULL, sizeof(ent) * (len ? len : 1));
    w->len = w->cap = 0;
    for (int32_t k = 0; k < len; k++) {
        long c, a0, a1, a2;
        if (scanf("%ld %ld %ld %ld", &c, &a0, &a1, &a2) != 4) exit(2);
        ent e; e.c = (int32_t)c;
        e.a[0] = (uint16_t)(((a0 % (long)Q) + Q) % Q);
        e.a[1] = (uint16_t)(((a1 % (long)Q) + Q) % Q);
        e.a[2] = (uint16_t)(((a2 % (long)Q) + Q) % Q);
        if (e.a[0] || e.a[1] || e.a[2]) w->e[w->len++] = e;
    }
    /* insertion sort by column (rows are short) and merge duplicates */
    for (int32_t i = 1; i < w->len; i++) {
        ent e = w->e[i]; int32_t j = i - 1;
        while (j >= 0 && w->e[j].c > e.c) { w->e[j + 1] = w->e[j]; j--; }
        w->e[j + 1] = e;
    }
    int32_t n = 0;
    for (int32_t i = 0; i < w->len; i++) {
        if (n && w->e[n - 1].c == w->e[i].c) {
            for (int k = 0; k < 3; k++)
                w->e[n - 1].a[k] = (uint16_t)((w->e[n - 1].a[k] + w->e[i].a[k]) % Q);
        } else w->e[n++] = w->e[i];
    }
    int32_t m = 0;
    for (int32_t i = 0; i < n; i++)
        if (w->e[i].a[0] || w->e[i].a[1] || w->e[i].a[2]) w->e[m++] = w->e[i];
    w->len = w->cap = m;
    nent += m;
}

static void print_row(const row *w) {
    printf("%d", w->len);
    for (int32_t k = 0; k < w->len; k++)
        printf(" %d %u %u %u", w->e[k].c, w->e[k].a[0], w->e[k].a[1], w->e[k].a[2]);
    printf("\n");
}

static int has_unit(const row *w) {
    for (int32_t k = 0; k < w->len; k++) if (is_unit(w->e[k].a)) return 1;
    return 0;
}

int main(void) {
    unsigned q;
    if (scanf("%d %d %d %u", &ngen, &nrels, &nvec, &q) != 4) return 2;
    Q = q;
    nrows = nrels + nvec;
    R = calloc(nrows, sizeof(row));
    C = calloc(ngen, sizeof(clist));
    rdead = calloc(nrows, 1);
    cdead = calloc(ngen, 1);
    bnext = malloc(sizeof(int32_t) * nrows);
    bprev = malloc(sizeof(int32_t) * nrows);
    bkt = malloc(sizeof(int32_t) * nrows);
    head = malloc(sizeof(int32_t) * (ngen + 2));
    for (int32_t b = 0; b <= ngen + 1; b++) head[b] = -1;
    minb = ngen + 1;
    for (int32_t r = 0; r < nrows; r++) {
        read_row(&R[r]);
        bkt[r] = -1;
        for (int32_t k = 0; k < R[r].len; k++) clist_add(R[r].e[k].c, r);
        if (r < nrels && R[r].len && has_unit(&R[r])) bucket_insert(r);
    }
    fprintf(stderr, "read %d rows, %lld entries\n", nrows, nent);
    long long npiv = 0;
    int32_t *todo = NULL; int32_t tcap = 0;
    for (;;) {
        while (minb <= ngen && head[minb] < 0) minb++;
        if (minb > ngen) break;
        int32_t r = head[minb];
        bucket_remove(r);
        row *p = &R[r];
        /* choose pivot column */
        int32_t best = -1, bestc = 0x7fffffff;
        for (int32_t k = 0; k < p->len; k++) {
            if (!is_unit(p->e[k].a)) continue;
            int32_t cl = C[p->e[k].c].len;
            if (cl < bestc) { bestc = cl; best = k; }
        }
        if (best < 0) continue;          /* no unit: parked until modified */
        int32_t j = p->e[best].c;
        uint16_t pinv[3];
        inv(p->e[best].a, pinv);
        rdead[r] = 1;
        /* rows containing j */
        clist *L = &C[j];
        if (tcap < L->len) { tcap = L->len; todo = xrealloc(todo, sizeof(int32_t) * tcap); }
        int32_t nt = 0;
        for (int32_t k = 0; k < L->len; k++) {
            int32_t qi = L->r[k];
            if (qi == r || rdead[qi]) continue;
            if (find(&R[qi], j) < 0) continue;
            todo[nt++] = qi;
        }
        /* dedupe todo (a row can be listed twice) */
        for (int32_t k = 0; k < nt; k++) {
            int32_t qi = todo[k];
            if (qi < 0) continue;
            int32_t pos = find(&R[qi], j);
            if (pos < 0) continue;       /* already reduced (duplicate entry) */
            uint16_t f[3];
            mul(R[qi].e[pos].a, pinv, f);
            int was = (qi < nrels) && bkt[qi] >= 0;
            if (qi < nrels) bucket_remove(qi);
            axpy(qi, f, p);
            (void)was;
            if (qi < nrels && R[qi].len && has_unit(&R[qi])) bucket_insert(qi);
        }
        free(L->r); L->r = NULL; L->len = L->cap = 0;
        cdead[j] = 1;
        nent -= p->len;
        free(p->e); p->e = NULL; p->len = 0;
        npiv++;
        if (npiv % 5000 == 0)
            fprintf(stderr, "%lld pivots, minlen %d, entries %lld (peak %lld)\n",
                    npiv, minb, nent, peak);
    }
    fprintf(stderr, "done: %lld pivots, entries %lld, peak %lld\n", npiv, nent, peak);
    int32_t na = 0;
    for (int32_t c = 0; c < ngen; c++) if (!cdead[c]) na++;
    printf("%d\n", na);
    for (int32_t c = 0; c < ngen; c++) if (!cdead[c]) printf("%d\n", c);
    int32_t nr = 0;
    for (int32_t r = 0; r < nrels; r++) if (!rdead[r] && R[r].len) nr++;
    printf("%d\n", nr);
    for (int32_t r = 0; r < nrels; r++) if (!rdead[r] && R[r].len) print_row(&R[r]);
    printf("%d\n", nvec);
    for (int32_t r = nrels; r < nrows; r++) print_row(&R[r]);
    return 0;
}
