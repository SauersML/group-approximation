/* Folded single-flip local search (1-opt) for weighted Min-2Lin(2)-deletion on folded reps.
 * half reps; edge e joins reps rx[e], ry[e] with parity par[e] (1 iff exactly one end is
 * a negated rep), weight w[e]; e is cut iff b[rx] ^ b[ry] ^ par == 1 ... here b = 1 means +1
 * and f(x) = b[rep] xor (x is negated), so cut iff b[rx] ^ b[ry] ^ par.
 * inc_ptr/inc_idx: CSR list of incident edges per rep.  fixed[r] = 1 for pinned reps.
 * Flips any rep with positive gain, sweeping until a sweep makes no flip.  b is updated
 * in place.  Returns the final weighted cut.
 * Build: gcc -O2 -shared -fPIC -o hadk_ls.so hadk_ls.c
 */
double local_search(int half, int E, const int *rx, const int *ry, const unsigned char *par,
                    const double *w, const int *inc_ptr, const int *inc_idx,
                    const unsigned char *fixed, unsigned char *b, int max_sweeps) {
    for (int s = 0; s < max_sweeps; s++) {
        int flips = 0;
        for (int r = 0; r < half; r++) {
            if (fixed[r]) continue;
            double g = 0;
            for (int t = inc_ptr[r]; t < inc_ptr[r + 1]; t++) {
                int e = inc_idx[t];
                int cut = b[rx[e]] ^ b[ry[e]] ^ par[e];
                g += cut ? w[e] : -w[e];
            }
            if (g > 1e-13) { b[r] ^= 1; flips++; }
        }
        if (!flips) break;
    }
    double tot = 0;
    for (int e = 0; e < E; e++)
        if (b[rx[e]] ^ b[ry[e]] ^ par[e]) tot += w[e];
    return tot;
}
