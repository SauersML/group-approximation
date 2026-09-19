#!/usr/bin/env python3
"""Independent check of every OPEN line of bs_search.py output (read from stdin).
For each line  OPEN w |w| p q U V [X..] seq  it checks, without reusing bs_search.py:
 1. BASIS: (U, V, X..) is a free basis of F(a_0..a_n).  Certificate: greedy Nielsen reduction
    (replace an element by its product with another element or its inverse whenever that
    shortens the total length) ends at single letters, one per a_h.  The reversed moves are an
    explicit automorphism of F(a_0..a_n) taking a basis of letters to (U, V, X..).
 2. MAGNUS: the Magnus rewriting of w (census.magnus, heights normalised to min 0) is, as a cyclic
    word in the a_h, exactly U^-1 V^p U V^-q (cyclically reduced).
 3. SLICE: t-exponent 0; unit Alexander polynomial (exactly one level with non-zero exponent sum,
    equal to +-1); a singular extreme level; both extreme levels unpeelable; |p - q| = 1.
 4. CENSUS: census.cert_word fails on w (so no landed PEEL/PP/R1/CYC certificate applies).
Prints a summary; any failure prints the line and exits 1."""
import sys
sys.path.insert(0, '/home/user/group-approximation/research/artifacts/or-unpeelable-census-scripts-2026-09-12')
import census as C
from ast import literal_eval


def red(w):
    o = []
    for x in w:
        if o and o[-1] == -x: o.pop()
        else: o.append(x)
    return o


def inv(w): return [-x for x in reversed(w)]


def cred(w):
    w = red(w)
    while len(w) >= 2 and w[0] == -w[-1]: w = w[1:-1]
    return w


def nielsen_to_letters(B):
    B = [red(list(b)) for b in B]
    while True:
        tot = sum(map(len, B)); best = None
        for i in range(len(B)):
            for j in range(len(B)):
                if i == j: continue
                for y in (B[j], inv(B[j])):
                    for nw in (red(B[i] + y), red(y + B[i])):
                        if len(nw) < len(B[i]) and (best is None or len(nw) < best[1]):
                            best = (i, len(nw), nw)
        if best is None: break
        B[best[0]] = best[2]
    return sorted(abs(b[0]) for b in B if len(b) == 1) == list(range(1, len(B) + 1)) and all(len(b) == 1 for b in B)


def cyc_equal(u, v):
    if len(u) != len(v): return False
    return any(u[r:] + u[:r] == v for r in range(len(u))) or (not u)


def main():
    n = bad = 0; lens = {}
    for line in sys.stdin:
        f = line.split()
        if not f or f[0] != 'OPEN': continue
        ws, L, p, q = f[1], int(f[2]), int(f[3]), int(f[4])
        U, V, X = literal_eval(f[5]), literal_eval(f[6]), literal_eval(f[7])
        w = [{'a': 1, 'A': -1, 't': 2, 'T': -2}[c] for c in ws]
        errs = []
        if len(w) != L: errs.append('length')
        if not nielsen_to_letters([U, V] + X): errs.append('basis')
        seq = C.magnus(w)
        W0 = []
        for h, e in seq: W0 += C.power(h + 1, e)
        target = cred(inv(U) + red((V if p > 0 else inv(V)) * abs(p)) + U + red((inv(V) if q > 0 else V) * abs(q)))
        if not cyc_equal(cred(W0), target): errs.append('magnus')
        N = max(h for h, _ in seq)
        if C.expsums(w)[1] != 0: errs.append('texp')
        sums = [sum(e for h, e in seq if h == l) for l in range(N + 1)]
        nz = [s for s in sums if s]
        if not (len(nz) == 1 and abs(nz[0]) == 1): errs.append('alexander')
        top = [e for h, e in seq if h == N]; bot = [e for h, e in seq if h == 0]
        if C.peelable(top) or C.peelable(bot): errs.append('peelable')
        if not (sums[0] == 0 or sums[N] == 0): errs.append('singular')
        if abs(p - q) != 1: errs.append('pq')
        C.BUDGET[0] = 4000
        if C.cert_word(w, 0)[0]: errs.append('census-cert')
        n += 1; lens.setdefault((p, q), []).append(L)
        if errs:
            bad += 1; print('FAIL', errs, line.strip())
    print('checked', n, 'failed', bad)
    for k in sorted(lens):
        print('BS%s: %d relators, min length %d' % (k, len(lens[k]), min(lens[k])))
    sys.exit(1 if bad else 0)


main()
