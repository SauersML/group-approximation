#!/usr/bin/env python3
"""Rule S (pro-unipotent Magnus step) for two-generator one-relator groups.

Usage:  prounipotent_step_certify.py WORDFILE [DEGREE]

WORDFILE holds words over a, b (A = a^-1, B = b^-1), one per line; only the first
token of each line that is a word is used, so census/frontier files can be passed
directly.  DEGREE (default 6) is the truncation degree of the explicit check.

For each word r and each letter t of exponent sum 0 in r, the Magnus rewrite
r' in F(a_0, ..., a_m) (a_i = t^-i a t^i, indices shifted so the lowest is 0) and its
exponent vector e = (e_0, ..., e_m) are computed.  Rule S applies when

  (S1)  m >= 1 and e_0 != 0 != e_m, and
  (S2)  the Magnus base B = <a_0, ..., a_m | r'> is free, witnessed by a letter a_j
        that occurs exactly once in the cyclic word r'.

Then G = <a, t | r> is in H: G is the HNN extension of B along the free window
A = <a_0, ..., a_{m-1}>, and the homomorphism G -> Fhat_m(Q) x|_T Z given by
a -> x_0, t -> s, with T(x_i) = x_{i+1} (i < m-1) and T(x_{m-1}) = z, where z is the
unique solution of r'(x_0, ..., x_{m-1}, z) = 1 in the rational pro-unipotent
completion Fhat_m(Q) of F(x_0, ..., x_{m-1}), is injective on A (it sends A's basis
to a basis of the free group).  The target is residually torsion-free nilpotent by
Z, hence in H.  See the node pro-unipotent-magnus-steps-put-one-relators-in-h.

The explicit check: z is computed in the free associative algebra Q<X_0..X_{m-1}>
truncated above DEGREE, as z = exp(Z) with Z solved degree by degree from
log r'(e^X_0, ..., e^X_{m-1}, e^Z) = 0; the script then re-evaluates log r' and
confirms it vanishes through DEGREE, confirms Z is a Lie element (it is primitive:
checked by the coproduct test in degrees <= DEGREE), and confirms det M != 0 for
the matrix M of T on H_1, so that T is an automorphism.
"""
import sys
from fractions import Fraction
from itertools import product


def parse(s):
    return [(c.lower(), 1 if c.islower() else -1) for c in s]


def rewrites(s):
    w = parse(s)
    out = []
    for t in 'ab':
        if sum(e for c, e in w if c == t) != 0:
            continue
        a = 'b' if t == 'a' else 'a'
        p, r = 0, []
        for c, e in w:
            if c == t:
                p += e
            else:
                r.append((-p, e))
        lo = min(i for i, _ in r)
        r = [(i - lo, e) for i, e in r]
        # free cyclic reduction of r' (as a cyclic word in the a_i)
        changed = True
        while changed and r:
            changed = False
            for k in range(len(r)):
                i1, e1 = r[k]
                i2, e2 = r[(k + 1) % len(r)]
                if len(r) >= 2 and i1 == i2 and e1 == -e2:
                    if k + 1 < len(r):
                        del r[k:k + 2]
                    else:
                        r = r[1:-1]
                    changed = True
                    break
        if not r:
            continue
        lo = min(i for i, _ in r)
        r = [(i - lo, e) for i, e in r]
        m = max(i for i, _ in r)
        ev = [0] * (m + 1)
        occ = [0] * (m + 1)
        for i, e in r:
            ev[i] += e
            occ[i] += 1
        out.append((t, r, ev, occ))
    return out


# ---- truncated free associative algebra over Q -------------------------------

class Alg:
    def __init__(self, ngen, deg):
        self.n, self.D = ngen, deg

    def mul(self, u, v):
        out = {}
        for w1, c1 in u.items():
            for w2, c2 in v.items():
                if len(w1) + len(w2) > self.D:
                    continue
                w = w1 + w2
                out[w] = out.get(w, 0) + c1 * c2
        return {w: c for w, c in out.items() if c != 0}

    def add(self, u, v, s=1):
        out = dict(u)
        for w, c in v.items():
            out[w] = out.get(w, 0) + s * c
        return {w: c for w, c in out.items() if c != 0}

    def scal(self, u, s):
        return {w: s * c for w, c in u.items() if s * c != 0}

    def exp(self, X):  # X without constant term
        out, term = {(): Fraction(1)}, {(): Fraction(1)}
        for k in range(1, self.D + 1):
            term = self.scal(self.mul(term, X), Fraction(1, k))
            out = self.add(out, term)
        return out

    def log(self, g):  # g = 1 + Y
        Y = self.add(g, {(): Fraction(1)}, -1)
        out, term = {}, {(): Fraction(1)}
        for k in range(1, self.D + 1):
            term = self.mul(term, Y)
            out = self.add(out, self.scal(term, Fraction((-1) ** (k + 1), k)))
        return out

    def inv_exp(self, X):
        return self.exp(self.scal(X, -1))


def homog(u, d):
    return {w: c for w, c in u.items() if len(w) == d}


def is_primitive(u, n, D):
    """u is primitive (a Lie element) iff Delta(u) = u(x)1 + 1(x)u.  For a
    homogeneous-by-degree truncation we test the equivalent shuffle criterion:
    for every split of each word the coefficient sums vanish, via Friedrichs'
    criterion  sum over words w of c_w * (w1 shuffle w2 coefficient) = 0  for all
    nonempty w1, w2.  Implemented directly: Delta(w) = sum over subsets S of
    positions of (w|S) (x) (w|S^c)."""
    delta = {}
    for w, c in u.items():
        L = len(w)
        for mask in range(1 << L):
            w1 = tuple(w[i] for i in range(L) if mask >> i & 1)
            w2 = tuple(w[i] for i in range(L) if not mask >> i & 1)
            if w1 and w2:
                delta[(w1, w2)] = delta.get((w1, w2), 0) + c
    return all(v == 0 for v in delta.values())


def eval_word(A, r, imgs, invs):
    g = {(): Fraction(1)}
    for i, e in r:
        g = A.mul(g, imgs[i] if e == 1 else invs[i])
    return g


def solve_top(r, m, D):
    """Solve r'(x_0..x_{m-1}, z) = 1 for z = exp(Z) in Q<X_0..X_{m-1}>/deg>D."""
    A = Alg(m, D)
    X = [{(i,): Fraction(1)} for i in range(m)]
    em = sum(e for i, e in r if i == m)
    Z = {}
    for d in range(1, D + 1):
        imgs = [A.exp(x) for x in X] + [A.exp(Z)]
        invs = [A.inv_exp(x) for x in X] + [A.inv_exp(Z)]
        E = homog(A.log(eval_word(A, r, imgs, invs)), d)
        Z = A.add(Z, A.scal(E, Fraction(-1, em)))
    imgs = [A.exp(x) for x in X] + [A.exp(Z)]
    invs = [A.inv_exp(x) for x in X] + [A.inv_exp(Z)]
    resid = A.log(eval_word(A, r, imgs, invs))
    return Z, resid


def det(M):
    n = len(M)
    M = [[Fraction(x) for x in row] for row in M]
    d = Fraction(1)
    for c in range(n):
        p = next((k for k in range(c, n) if M[k][c] != 0), None)
        if p is None:
            return Fraction(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for k in range(c + 1, n):
            f = M[k][c] / M[c][c]
            M[k] = [M[k][j] - f * M[c][j] for j in range(n)]
    return d


def main():
    fn = sys.argv[1]
    D = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    words = []
    for line in open(fn):
        for tok in line.split():
            if tok and set(tok) <= set('abAB') and len(tok) > 1:
                words.append(tok)
                break
    ncert = 0
    for s in words:
        verdict, info = 'open', ''
        for t, r, ev, occ in rewrites(s):
            m = len(ev) - 1
            if m < 1 or ev[0] == 0 or ev[m] == 0:
                info = info or 'S1 fails: e=%s' % ev
                continue
            once = [j for j in range(m + 1) if occ[j] == 1]
            if not once:
                info = 'S1 ok, base not visibly free: e=%s occ=%s' % (ev, occ)
                continue
            Z, resid = solve_top(r, m, D)
            ok_rel = not resid
            ok_lie = is_primitive(Z, m, D)
            # matrix of T on H_1 = Q^m, basis x_0..x_{m-1}: x_i -> x_{i+1}, x_{m-1} -> z
            z1 = [-Fraction(ev[i], ev[m]) for i in range(m)]
            M = [[0] * m for _ in range(m)]
            for i in range(m - 1):
                M[i + 1][i] = 1
            for i in range(m):
                M[i][m - 1] = z1[i]
            dM = det(M)
            if ok_rel and ok_lie and dM != 0:
                verdict = 'CERT'
                info = ('rule-S t=%s e=%s occ=%s free-letter=a_%d detT=%s '
                        'relation-checked-to-degree=%d' % (t, ev, occ, once[0], dM, D))
                break
            info = 'CHECK-FAILED rel=%s lie=%s det=%s' % (ok_rel, ok_lie, dM)
        ncert += verdict == 'CERT'
        print(s, verdict, info)
    print('# %s: %d words, rule S certifies %d, degree %d' % (fn, len(words), ncert, D))


if __name__ == '__main__':
    main()
