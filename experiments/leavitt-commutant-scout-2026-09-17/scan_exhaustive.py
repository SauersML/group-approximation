"""Exhaustive census: every A in the box V_{1,2} of L_{F_2}(1,2) (depth-1 tables,
output words of length <= 2; 2^14 elements).  For each A that is transcendental
on test vectors, compute the exact commutant of A inside V_{NB,LB} and test every
commutant basis vector (and random combinations) for super-linear joint growth
of {A^i B^j : i+j<k}.  Linear growth in k (<= c*k) is the signature of an
algebraically dependent pair (commutant = finite module over F[A]); an
algebraically independent pair must have growth ~ k^2/2.

Usage: python3 scan_exhaustive.py [NB LB k1 k2 procs]
Prints a histogram of (max growth at k1, max growth at k2) and any flagged A.
"""
import sys, random, itertools
from multiprocessing import Pool
from l2 import El, words, ONE, ZERO
from commutant import commutant, growth, randz

OUTS = [w for l in range(3) for w in words(l)]  # 7 words of length <= 2
ZS = [randz(400, 1000 + i) for i in range(3)]
CFG = {}

def el_of(code):
    T = {}
    for bi, m in enumerate(words(1)):
        T[m] = frozenset(w for j, w in enumerate(OUTS) if code >> (7 * bi + j) & 1)
    return El(1, T).reduce()

def work(code):
    NB, LB, k1, k2 = CFG['p']
    A = el_of(code)
    if growth(A, ONE, k2, ZS) < k2:
        return (code, 'alg', 0, 0, 0)
    C = commutant(A, NB, LB)
    # powers of A lying in the box are automatically in C (and independent,
    # since A is transcendental); if they exhaust C the commutant in the box is
    # just F[A] ∩ box and no growth test is needed.
    npow, P = 0, ONE
    for _ in range(NB + 2):
        R = P.reduce()
        if R.N <= NB and all(len(w) + (NB - R.N) <= LB for S in R.T.values() for w in S):
            npow += 1
        P = P * A
    if len(C) == npow:
        return (code, 'tr', len(C), -1, -1)
    rng = random.Random(code)
    cands = list(C)
    for _ in range(6):
        B = ZERO
        for c in C:
            if rng.random() < 0.5:
                B = B + c
        cands.append(B)
    g1 = max(growth(A, B, k1, ZS) for B in cands)
    g2 = max(growth(A, B, k2, ZS) for B in cands)
    return (code, 'tr', len(C), g1, g2)

def init(p):
    CFG['p'] = p

def main(NB=2, LB=4, k1=5, k2=7, procs=4):
    p = (NB, LB, k1, k2)
    hist = {}
    dims = {}
    flagged = []
    nalg = 0
    with Pool(procs, initializer=init, initargs=(p,)) as pool:
        for code, kind, d, g1, g2 in pool.imap_unordered(work, range(1 << 14), chunksize=64):
            if kind == 'alg':
                nalg += 1
                continue
            hist[(g1, g2)] = hist.get((g1, g2), 0) + 1
            dims[d] = dims.get(d, 0) + 1
            # quadratic signature: growth increment from k1 to k2 exceeds what
            # a rank-r module over F[A] (growth ~ r*k) could give with r = g1/k1
            if g2 - g1 > (k2 - k1) * max(1, -(-g1 // k1)) + 2:
                flagged.append((code, g1, g2))
                print('FLAG', code, el_of(code), g1, g2, flush=True)
    print('algebraic-on-test-vectors A:', nalg)
    print('commutant dims (in box) -> count:', sorted(dims.items()))
    print('(growth k1, growth k2) -> count:', sorted(hist.items()))
    print('flagged:', len(flagged))

if __name__ == '__main__':
    args = [int(a) for a in sys.argv[1:]]
    main(*args)
