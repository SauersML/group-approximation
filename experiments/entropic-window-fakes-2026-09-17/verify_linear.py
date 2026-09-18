#!/usr/bin/env python3
"""Exact check that an F_2-linear configuration on a minimal window is an entropic fake.

usage: verify_linear.py GROUP 'E' 'F' rep.json
  GROUP: an integer n (cyclic Z/n, E and F comma lists) or a torsion2_scan group name (Python literals).
  rep.json: {"d": block size, "W": [[row, ...] for each y in build order]}, rows as hex strings.

Random variables: x_g (g in X = FE u {1}) independent uniform on F_2^d, the coordinate blocks of
F_2^(|X| d); y_f = W_f . x, a linear map whose rows are supported on the blocks of x_(fE).  All entropies
are ranks over F_2 (in bits); we normalise by d, so k log q = 1.  The script checks, using integer arithmetic only:
  (I) rank(x_g) = d, rank(x_X) = |X| d                         [true by construction; checked anyway]
  (D) every row of W_f is supported on the blocks of fE         [functional dependence y_f = psi_f(x_(fE))]
  (T) rank(S) = rank(tS) for every translation t = p q^-1 of ground sites and every S with S, tS in the ground set
and prints Phi*d = rank(y_f0) + rank(x_1 y_F) - rank(y_F), exiting 0 iff all checks pass and Phi < 1.
Entropy vectors of genuine random variables satisfy every valid information inequality, so no
information inequality whatsoever, combined with (I), (D), (T), derives Phi >= 1 on this window.
"""
import sys, os, json, ast
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-window-certificates-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'promislow-shannon-windows-2026-09-17'))
from random_scan import Cyc


def rank2(rows):
    basis = []
    for v in rows:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return len(basis)


def main():
    if sys.argv[1].isdigit():
        n = int(sys.argv[1]); G = Cyc(n)
        E = [int(t) for t in sys.argv[2].split(',')]; F = [int(t) for t in sys.argv[3].split(',')]
    else:
        from torsion2_scan import group
        G = group(sys.argv[1])[0]; E = ast.literal_eval(sys.argv[2]); F = ast.literal_eval(sys.argv[3])
    rep = json.load(open(sys.argv[4]))
    d = rep['d']
    Y = list(dict.fromkeys(F))
    X = [G.one]
    for f in Y:
        for e in E:
            X.append(G.mul(f, e))
    X = list(dict.fromkeys(X))
    items = [('x', g) for g in X] + [('y', g) for g in Y]
    idx = {it: i for i, it in enumerate(items)}
    nvar = len(items)
    W = [[int(v, 16) for v in rows] for rows in rep['W']]
    assert len(W) == len(Y)
    ok = True
    # (D) support
    for j, f in enumerate(Y):
        allowed = 0
        for e in E:
            gi = X.index(G.mul(f, e))
            allowed |= ((1 << d) - 1) << (gi * d)
        for v in W[j]:
            if v & ~allowed:
                ok = False; print('FAIL (D) support of y_%s' % (f,))
    cache = {}
    def rk(S):
        if S not in cache:
            rows = []
            for i, (kind, g) in enumerate(items):
                if S >> i & 1:
                    rows += [1 << (i * d + b) for b in range(d)] if kind == 'x' else W[i - len(X)]
            cache[S] = rank2(rows)
        return cache[S]
    # (I)
    for i in range(len(X)):
        if rk(1 << i) != d:
            ok = False; print('FAIL (I) x_%s' % (X[i],))
    if rk((1 << len(X)) - 1) != len(X) * d:
        ok = False; print('FAIL (I) x_X')
    # (T)
    sites = list(dict.fromkeys(X + Y))
    trans = {G.mul(p, G.inv(q)) for p in sites for q in sites} - {G.one}
    neq = 0
    for t in trans:
        im = [idx.get((kind, G.mul(t, g)), -1) for (kind, g) in items]
        for S in range(1, 1 << nvar):
            T = 0; good = True
            for i in range(nvar):
                if S >> i & 1:
                    if im[i] < 0:
                        good = False; break
                    T |= 1 << im[i]
            if not good:
                continue
            neq += 1
            if rk(S) != rk(T):
                ok = False; print('FAIL (T) t=%s S=%s' % (t, bin(S)))
    yF = sum(1 << idx[('y', f)] for f in Y)
    x1 = 1 << idx[('x', G.one)]
    phid = rk(1 << idx[('y', Y[0])]) + rk(yF | x1) - rk(yF)
    phi = Fr(phid, d)
    print('ground set %d, block size d=%d, %d translation equalities checked, all ranks exact' % (nvar, d, neq))
    print('rank(y_f) =', [rk(1 << idx[('y', f)]) for f in Y], ' Phi = %s' % phi)
    print('ALL EXACT' if ok else 'CHECK FAILED')
    sys.exit(0 if ok and phi < 1 else 1)


main()
