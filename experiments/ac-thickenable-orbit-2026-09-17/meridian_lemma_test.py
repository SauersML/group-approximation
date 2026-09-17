#!/usr/bin/env python3
"""Falsification test for the meridian lemma (research/thickenable-balanced-presentations-have-meridional-relators).
For torus relators r1 = x^p Y^q (p, q >= 2 coprime) and every cyclically reduced r2 of length <= LMAX:
  thick  = Neuwirth test on (r1, r2)      (thick2.c)
  merid  = exact meridian test of meridian.py (r2 conjugate to mu^{+-1} in T(p,q))
The lemma predicts: thick and (group trivial) => merid.  For every pair with thick and not merid and
exponent sum q*e_x + p*e_y = +-1 we look for a transitive permutation representation onto S_k, k <= KMAX,
showing the group is nontrivial.  Output: counts and any unexplained pair (a counterexample to the lemma
or a hole in the representation search).
Usage: meridian_lemma_test.py LMAX KMAX
"""
import sys, itertools
import thickc, meridian as M

def words(L):
    out = []
    def rec(w):
        if len(w) == L:
            if M.cred(w) == w:
                out.append(w)
            return
        for c in 'xXyY':
            if w and w[-1] == c.swapcase():
                continue
            rec(w + c)
    rec('')
    return out

def perm_mul(a, b):  # apply a then b
    return tuple(b[i] for i in a)

def perm_inv(a):
    r = [0] * len(a)
    for i, j in enumerate(a):
        r[j] = i
    return tuple(r)

def evalw(w, X, Y):
    n = len(X); cur = tuple(range(n))
    XI, YI = perm_inv(X), perm_inv(Y)
    for c in w:
        cur = perm_mul(cur, {'x': X, 'X': XI, 'y': Y, 'Y': YI}[c])
    return cur

def nontrivial_rep(rels, kmax):
    for k in range(2, kmax + 1):
        perms = list(itertools.permutations(range(k)))
        idp = tuple(range(k))
        for X in perms:
            for Y in perms:
                if X == idp and Y == idp:
                    continue
                if all(evalw(r, X, Y) == idp for r in rels):
                    return (k, X, Y)
    return None

if __name__ == "__main__":
    LMAX = int(sys.argv[1]); KMAX = int(sys.argv[2])
    for p, q in ((2, 3), (3, 2), (3, 4), (2, 5), (3, 5)):
        r1 = 'x' * p + 'Y' * q
        n_thick = n_merid = n_tm = n_explained = 0; bad = []
        for L in range(1, LMAX + 1):
            for r2 in words(L):
                ex = r2.count('x') - r2.count('X'); ey = r2.count('y') - r2.count('Y')
                # abelianization of T(p,q): x -> q, y -> p
                if abs(q * ex + p * ey) != 1:
                    continue
                t = thickc.thick2([r1, r2]); m = M.torus_meridian_ok(r1, r2)
                n_thick += t; n_merid += m; n_tm += (t and m)
                if t and not m:
                    rep = nontrivial_rep([r1, r2], KMAX)
                    if rep:
                        n_explained += 1
                    else:
                        bad.append(r2)
        print("T(%d,%d) r1=%s LMAX=%d: thick=%d merid=%d thick&merid=%d thick&!merid=%d (nontrivial group shown for %d) UNEXPLAINED=%s"
              % (p, q, r1, LMAX, n_thick, n_merid, n_tm, n_thick - n_tm, n_explained, bad[:20]))
        sys.stdout.flush()
