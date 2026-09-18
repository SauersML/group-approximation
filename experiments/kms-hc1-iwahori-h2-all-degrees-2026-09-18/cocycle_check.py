#!/usr/bin/env python3
"""Check that the triples used in the hand proof already force H^2(L_p)_{-mu}.

usage: cocycle_check.py MAXDEG P1 P2 ...

For each weight mu = nu + m delta of Lambda^2(L) with degree <= MAXDEG and each prime p,
compute over F_p
    dim (ker of the cocycle conditions of the SELECTED triples on Lambda^2_mu) - rank(coboundaries)
where the selected triples are those used in the proof for the type of nu:
    nu = 0          : triples with an imaginary factor (T1), and three real factors
                      with pairwise non-opposite finite parts (T3);
    nu a root       : triples with an imaginary factor (Ta, Tb), and three real factors
                      two of which have opposite finite parts (Tc);
    Q(nu) = 3 or 4  : triples with an imaginary factor only.
The proof says this number is 1 at n delta with p | n and 0 otherwise (for m >= 4).  The script
reports every weight where it differs; since the selected conditions are a subset of all
cocycle conditions, the number is always >= dim H^2(L_p)_{-mu}.
"""
import sys, os
MAXDEG = int(sys.argv[1]); PR = [int(x) for x in sys.argv[2:]]
sys.argv = [sys.argv[0], str(MAXDEG)]
H2Z = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'kms-hc1-iwahori-integral-h2-2026-09-17', 'h2z.py')
exec(open(H2Z).read().split("if __name__ == '__main__':")[0])
from flint import nmod_mat

def fin(n):
    w = W[n]
    return (w[1] - w[0], w[2] - w[0])

def is_imag(n):
    return basis[n][0] == 'h'

def neg(u, v):
    return u[0] == -v[0] and u[1] == -v[1]

def rank_mod(rows, ncols, p):
    if not rows or ncols == 0:
        return 0
    return nmod_mat(rows, p).rank()

bad = 0; tested = 0
for w in weights_upto(MAXDEG):
    x, y = w[1] - w[0], w[2] - w[0]
    Q = x * x - x * y + y * y
    m = w[0]
    if m < 4:
        continue
    P = pairs_at(w); Lw = byw.get(w, [])
    pidx = {pr: n for n, pr in enumerate(P)}
    lidx = {b: n for n, b in enumerate(Lw)}
    rows3 = []
    for (a, b, c) in triples_at(w):
        im = any(is_imag(t) for t in (a, b, c))
        if not im:
            fa, fb, fc = fin(a), fin(b), fin(c)
            opp = neg(fa, fb) or neg(fa, fc) or neg(fb, fc)
            if Q == 0 and opp: continue
            if Q == 1 and not opp: continue
            if Q in (3, 4): continue
        row = [0] * len(P)
        for (u, v, s, cc) in ((a, b, -1, c), (a, c, 1, b), (b, c, -1, a)):
            for k, co in bracket(u, v).items():
                wv = wedge2(k, cc)
                if wv is None: continue
                sg, pr = wv
                row[pidx[pr]] += s * sg * co
        if any(row): rows3.append(row)
    rows2 = []
    for (a, b) in P:
        row = [0] * len(Lw)
        for k, v in bracket(a, b).items():
            row[lidx[k]] -= v
        rows2.append(row)
    for p in PR:
        r3 = rank_mod([[v % p for v in r] for r in rows3], len(P), p)
        r2 = rank_mod([[v % p for v in r] for r in rows2], len(Lw), p) if Lw else 0
        val = len(P) - r3 - r2
        exp = 1 if (Q == 0 and w[0] % p == 0) else 0
        tested += 1
        if val != exp:
            bad += 1
            print("DIFF", w, "Q", Q, "p", p, "got", val, "expected", exp, flush=True)
print(f"tested {tested} (weight, p) pairs with m >= 4 and degree <= {MAXDEG}; {bad} differ")
