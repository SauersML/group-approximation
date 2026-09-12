/* Planar reduced ribbon pairings for length-six relators with one relator.
 *
 * Lane kl-curvature-redistribution, 2026-09-12.  Usage:
 *   pairings <class> <area> > out.txt
 * class 0 = +++++- (letters t t t t t t^-1), class 1 = ++++-- (t t t t t^-1 t^-1).
 * area = number of relator discs (even; half positive, half negative).
 *
 * A disc is a vertex with six half-edges in clockwise order.  A positive disc
 * carries the letters L_0..L_5 of w; a negative disc reads w^-1 clockwise, so
 * its half-edge j carries the letter L_(5-j)^-1.  Arcs pair a letter t with a
 * letter t^-1.  An arc joining half-edge i of a positive disc to half-edge j of
 * a negative disc with i + j = 5 joins inverse occurrences of the same letter,
 * so the two discs form a dipole; such pairings are not reduced and are skipped.
 * A pairing is kept when it is connected and its ribbon surface is a sphere:
 * V - E + F = 2 with E = 3V, i.e. F = 2 + 2V faces, where faces are the cycles
 * of h -> rot(alpha(h)) and rot moves one step clockwise at the same disc.
 * Output is one line per pairing up to relabelling the positive discs among
 * themselves and the negative discs among themselves: "V a_0 ... a_(6V-1)".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int V, H, np, nn, keep_dipoles = 0;
static int sgn[6], hsign[24], orient[4], alpha[24], used[24];
static int P[24], N[24];
static long long leaves = 0, planar = 0, emitted = 0;

static int findp(int *p, int x) {
    while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; }
    return x;
}

static void relabel(const int *perm, int *out) {
    for (int h = 0; h < H; h++) {
        int a = alpha[h];
        int hh = 6 * perm[h / 6] + h % 6;
        out[hh] = 6 * perm[a / 6] + a % 6;
    }
}

static int is_canonical(void) {
    int perms[4][4];
    int count = 0;
    if (V == 2) {
        perms[0][0] = 0; perms[0][1] = 1; count = 1;
    } else {
        int base[4][4] = {{0, 1, 2, 3}, {1, 0, 2, 3}, {0, 1, 3, 2}, {1, 0, 3, 2}};
        memcpy(perms, base, sizeof base); count = 4;
    }
    int img[24];
    for (int k = 1; k < count; k++) {
        relabel(perms[k], img);
        for (int h = 0; h < H; h++) {
            if (img[h] < alpha[h]) return 0;
            if (img[h] > alpha[h]) break;
        }
    }
    return 1;
}

static void leaf(void) {
    leaves++;
    int par[4];
    for (int i = 0; i < V; i++) par[i] = i;
    for (int h = 0; h < H; h++) {
        int a = findp(par, h / 6), b = findp(par, alpha[h] / 6);
        if (a != b) par[a] = b;
    }
    int r = findp(par, 0);
    for (int i = 1; i < V; i++) if (findp(par, i) != r) return;
    char seen[24];
    memset(seen, 0, sizeof seen);
    int F = 0;
    for (int h = 0; h < H; h++) {
        if (seen[h]) continue;
        F++;
        int x = h;
        while (!seen[x]) {
            seen[x] = 1;
            int y = alpha[x];
            x = 6 * (y / 6) + (y % 6 + 1) % 6;
        }
    }
    if (F != 2 + 2 * V) return;
    planar++;
    if (!is_canonical()) return;
    emitted++;
    printf("%d", V);
    for (int h = 0; h < H; h++) printf(" %d", alpha[h]);
    printf("\n");
}

static void rec(int k) {
    if (k == np) { leaf(); return; }
    int hp = P[k], vp = hp / 6, jp = hp % 6;
    for (int i = 0; i < nn; i++) {
        if (used[i]) continue;
        int hn = N[i], vn = hn / 6, jn = hn % 6;
        if (!keep_dipoles && orient[vp] != orient[vn]) {
            int ipos = orient[vp] == 1 ? jp : jn;
            int ineg = orient[vp] == 1 ? jn : jp;
            if (ipos + ineg == 5) continue;
        }
        used[i] = 1;
        alpha[hp] = hn;
        alpha[hn] = hp;
        rec(k + 1);
        used[i] = 0;
    }
}

int main(int argc, char **argv) {
    if (argc != 3 && argc != 4) { fprintf(stderr, "usage: pairings <class> <area> [keep-dipoles]\n"); return 2; }
    int cls = atoi(argv[1]);
    V = atoi(argv[2]);
    keep_dipoles = argc == 4;  /* control run: dipoles kept, so the complete gluing of w to w^-1 appears */
    if ((V != 2 && V != 4) || (cls != 0 && cls != 1)) { fprintf(stderr, "bad args\n"); return 2; }
    int s0[6] = {1, 1, 1, 1, 1, -1}, s1[6] = {1, 1, 1, 1, -1, -1};
    memcpy(sgn, cls == 0 ? s0 : s1, sizeof sgn);
    H = 6 * V;
    for (int v = 0; v < V; v++) orient[v] = v < V / 2 ? 1 : -1;
    np = nn = 0;
    for (int h = 0; h < H; h++) {
        int v = h / 6, j = h % 6;
        hsign[h] = orient[v] == 1 ? sgn[j] : -sgn[5 - j];
        if (hsign[h] == 1) P[np++] = h; else N[nn++] = h;
    }
    if (np != nn) { fprintf(stderr, "unbalanced signs\n"); return 2; }
    rec(0);
    fprintf(stderr, "class=%d area=%d leaves=%lld planar=%lld emitted=%lld\n",
            cls, V, leaves, planar, emitted);
    return 0;
}
