#!/usr/bin/env python3
"""Put each open word in commutator-root normal form.

For a cyclically reduced relator w in F(a, b) with exponent sums (e_a, e_b) != 0, search Nielsen
substitutions a -> A(t, y), b -> B(t, y), with A, B of length <= 3 in t, y and {A, B} a basis of
F(t, y) of the explicit shape {t^{+-1}, t^i y^{+-1} t^j} (or {y^{+-1} ..., t^{+-1}} with the roles of a, b
exchanged), such that y has height 0 under the map G -> Z.  The substituted relator is Magnus-rewritten
with y_i = t^{-i} y t^i and tested for the shape

    y_1^K = [y_0^alpha, y_2^beta]      ([g, h] = g^-1 h^-1 g h),   alpha, beta = +-1.

Each hit is checked by substituting back: the relator rebuilt from the normal form must equal a rotation
of w or of w^-1 after the inverse substitution (the substitution is an automorphism of F_2, so the
groups are isomorphic).  (K, alpha, beta) is normalised by y -> y^-1 (all signs flip) to K > 0 and by
t -> t^-1 ((alpha, beta) -> (-beta, -alpha)) to the lexicographically largest of the two.

Usage: commutator_normal_form.py WORDFILE
"""
import itertools
import sys
from math import gcd

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b', 'y': 'Y', 'Y': 'y', 't': 'T', 'T': 't'}


def red(w):
    s = []
    for c in w:
        if s and s[-1] == INV[c]:
            s.pop()
        else:
            s.append(c)
    return s


def cred(w):
    s = red(w)
    while len(s) > 1 and s[0] == INV[s[-1]]:
        s = s[1:-1]
    return s


def inv(w):
    return [INV[c] for c in reversed(w)]


def esum(w, x):
    return sum(1 if c == x else -1 if c == INV[x] else 0 for c in w)


def magnus(wty):
    """cyclic syllables (i, e) of the Magnus rewrite, y at prefix t-height H is y_{-H}."""
    H, out = 0, []
    for c in wty:
        if c in 'tT':
            H += 1 if c == 't' else -1
        else:
            out.append((-H, 1 if c == 'y' else -1))
    mn = min(i for i, _ in out)
    s = []
    for i, e in out:
        i -= mn
        if s and s[-1][0] == i:
            s[-1] = (i, s[-1][1] + e)
            if s[-1][1] == 0:
                s.pop()
        else:
            s.append((i, e))
    while len(s) > 1 and s[0][0] == s[-1][0]:
        s[0] = (s[0][0], s[0][1] + s[-1][1])
        s.pop()
    return s


def pattern(s):
    if len(s) != 5:
        return None
    for r in range(5):
        u = s[r:] + s[:r]
        if u[0][0] != 1:
            continue
        k, X = u[0][1], u[1:]
        idx = [i for i, _ in X]
        s1, s2 = X[0][1], X[1][1]
        if abs(s1) != 1 or abs(s2) != 1 or X[2][1] != -s1 or X[3][1] != -s2:
            return None
        # y_1^k X = 1, X = g h g^-1 h^-1  =>  y_1^k = X^-1 = [h^-1, g^-1]
        if idx == [0, 2, 0, 2]:     # g = y_0^s1, h = y_2^s2: y_1^-k = [y_0^-s1, y_2^-s2]
            K, A, B = -k, -s1, -s2
        elif idx == [2, 0, 2, 0]:   # g = y_2^s1, h = y_0^s2: y_1^k = [y_0^-s2, y_2^-s1]
            K, A, B = k, -s2, -s1
        else:
            return None
        if K < 0:
            K, A, B = -K, -A, -B
        return max((K, A, B), (K, -B, -A))
    return None


def expand(s):
    """word in t, y for prod y_i^e with y_i = t^-i y t^i."""
    out = []
    for i, e in s:
        out += ['T'] * i + (['y'] * e if e > 0 else ['Y'] * (-e)) + ['t'] * i
    return out


def main():
    words = open(sys.argv[1]).read().split()
    tally = {}
    cands = []
    for L in range(1, 4):
        for tup in itertools.product('tTyY', repeat=L):
            if all(INV[tup[i]] != tup[i + 1] for i in range(L - 1)):
                cands.append(list(tup))
    for w in words:
        ea, eb = esum(w, 'a'), esum(w, 'b')
        g = gcd(ea, eb)
        h = {'a': eb // g, 'b': -ea // g}
        found = None
        for A in cands:
            for B in cands:
                if esum(A, 't') != h['a'] or esum(B, 't') != h['b']:
                    continue
                # explicit bases only: one image is t^{+-1}, the other t^i y^{+-1} t^j
                imgs = (A, B)
                okb = False
                for P, Qw in (imgs, imgs[::-1]):
                    if P in (['t'], ['T']) and sum(c in 'yY' for c in Qw) == 1:
                        okb = True
                if not okb:
                    continue
                sub = {'a': A, 'A': inv(A), 'b': B, 'B': inv(B)}
                wty = cred(sum((sub[c] for c in w), []))
                if not any(c in 'yY' for c in wty):
                    continue
                s = magnus(wty)
                p = pattern(s)
                if p is None:
                    continue
                # back-substitution check: expand the normal form and compare cyclic words in F(t, y)
                back = ''.join(cred(expand(s)))
                tw = ''.join(wty)
                twi = ''.join(inv(wty))
                rots = [tw[j:] + tw[:j] for j in range(len(tw))] + [twi[j:] + twi[:j] for j in range(len(twi))]
                # the Magnus normal form is the relator up to conjugation by a power of t
                ok = any(''.join(cred(['T'] * m + list(back) + ['t'] * m)) in rots or
                         ''.join(cred(['t'] * m + list(back) + ['T'] * m)) in rots for m in range(0, 4))
                if ok:
                    found = (p, ''.join(A), ''.join(B), ' '.join('y%d^%d' % x for x in s))
                    break
            if found:
                break
        tally.setdefault(found[0] if found else None, []).append(w)
        print(w, 'a->%s b->%s' % (found[1], found[2]) if found else '-',
              found[3] if found else '-', 'K,alpha,beta=%s' % (found[0],) if found else 'no form', flush=True)
    print()
    for k in sorted(tally, key=str):
        print('pattern', k, len(tally[k]), ' '.join(tally[k]))


if __name__ == '__main__':
    main()
