#!/usr/bin/env python3
"""alex.py -- Alexander polynomials of the two one-relator quotients of each state.

For a state (r1, r2) of a balanced presentation of the trivial group in F_2 = <x, y>, each
one-relator group G_i = <x, y | r_i> has abelianization Z (the exponent-sum vector of r_i is
primitive because the abelianized relator matrix has determinant +-1).  Its Alexander
polynomial is the gcd of the two Fox derivatives of r_i pushed to Z[t, t^-1] along
G_i -> Z; for a two-generator one-relator group this gcd equals D_y (t - 1)/(t^a - 1) when
x -> t^a with a != 0 (and D_x (t - 1)/(t^b - 1) otherwise), by the fundamental formula
D_x (t^a - 1) + D_y (t^b - 1) = 0.

Output: histogram of the unordered pair {Delta_1, Delta_2} (normalised up to +-t^k and
t -> t^-1) over the states read from stdin (lines "r1 r2", words over xyXY).
usage: alex.py < dump.txt [> hist.txt]
"""
import sys
from collections import Counter
from math import gcd

def ab(w):
    p = w.count('x') - w.count('X'); q = w.count('y') - w.count('Y')
    return p, q

def fox(w, gen, a, b):
    """Fox derivative d w / d gen pushed to Z[t^+-1] via x->t^a, y->t^b; dict exp->coeff."""
    G, g = gen, gen.upper()
    out = {}; e = 0
    for c in w:
        if c == G:
            out[e] = out.get(e, 0) + 1
        elif c == g:
            out[e - (a if G == 'x' else b)] = out.get(e - (a if G == 'x' else b), 0) - 1
        e += {'x': a, 'X': -a, 'y': b, 'Y': -b}[c]
    return {k: v for k, v in out.items() if v}

def tolist(d):
    if not d: return []
    lo = min(d); hi = max(d)
    return [d.get(k, 0) for k in range(lo, hi + 1)]

def mul_tm1(p):   # p * (t - 1), coefficient lists low->high
    r = [0] * (len(p) + 1)
    for i, c in enumerate(p):
        r[i + 1] += c; r[i] -= c
    return r

def div_tn_m1(p, n):  # exact division by (t^n - 1), n >= 1
    p = p[:]; q = [0] * max(len(p) - n, 0)
    for i in range(len(p) - 1, n - 1, -1):
        c = p[i]
        if c:
            q[i - n] += c; p[i] -= c; p[i - n] += c
    if any(p):
        raise ValueError("not divisible")
    return q

def norm(p):
    while p and p[0] == 0: p = p[1:]
    while p and p[-1] == 0: p = p[:-1]
    if not p: return ()
    if p[-1] < 0: p = [-c for c in p]
    r = p[::-1]
    if r[-1] < 0: r = [-c for c in r]
    return min(tuple(p), tuple(r))

def alexander(w):
    p, q = ab(w)
    if gcd(p, q) != 1:
        raise ValueError("non-primitive exponent vector %s" % w)
    a, b = q, -p            # phi(x) = t^a, phi(y) = t^b, phi(w) = t^(a p + b q) = 1
    if a != 0:
        D = tolist(fox(w, 'y', a, b)); n = abs(a)
    else:
        D = tolist(fox(w, 'x', a, b)); n = abs(b)
    return norm(div_tn_m1(mul_tm1(D), n))

def show(p):
    return ','.join(map(str, p))

def main():
    hist = Counter(); nst = 0; trivial_some = 0
    for line in sys.stdin:
        f = line.split()
        if len(f) < 2: continue
        d1, d2 = alexander(f[0]), alexander(f[1])
        nst += 1
        if d1 == (1,) or d2 == (1,): trivial_some += 1
        hist[tuple(sorted((d1, d2)))] += 1
    print("states %d; with some Delta_i = 1: %d; distinct pairs %d" % (nst, trivial_some, len(hist)))
    for k, v in hist.most_common():
        print(v, show(k[0]), '|', show(k[1]))

if __name__ == '__main__':
    main()
