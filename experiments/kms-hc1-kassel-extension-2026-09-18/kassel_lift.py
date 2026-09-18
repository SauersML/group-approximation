"""Explicit degree-15 test elements of F_5<X_a,X_b,X_c> (all of multidegree (5,5,5)).

a = E12, b = E23, c = t E31 (Lie bracket [x,y] = xy - yx, the image of X_a, X_b, X_c in u(L_5)).
  H1 = [[a,b],c]  = (E11-E33) t          H2 = [[b,c],a] = (E22-E11) t
  E12_k = (ad H1)^(k-1) [H1,a]  = E12 t^k     E21_k = -(ad H1)^(k-1)... (sign (-1)^(k-1)) [b,c] = E21 t^k
  E23_k = (ad H1)^(k-1) [H1,b]  = E23 t^k     E32_k = (-1)^(k-1) (ad H1)^(k-1) [c,a] = E32 t^k
vectors written (usage: python3 kassel_lift.py out.vec):
  0  K  = [E12_1, E21_4] - [E12_4, E21_1]       Lie lift of the Kassel class: 0 in L_5, 2z in N
  1  C1 = H1^5 - [E12_1,E21_4] - [E23_1,E32_4]   restricted Cartan relation (H1)^[5] = (E11-E33) t^5
  2  C2 = H2^5 + [E12_1,E21_4]                   restricted Cartan relation (H2)^[5] = (E22-E11) t^5
  3  K' = [E23_1, E32_4] - [E23_4, E32_1]       second Kassel lift (tr(E23 E32) = 1)
"""
import sys
from collections import defaultdict
p = 5


def mul(f, g):
    h = defaultdict(int)
    for u, x in f.items():
        for v, y in g.items():
            h[u + v] = (h[u + v] + x * y) % p
    return {w: c for w, c in h.items() if c}


def add(f, g, s=1):
    h = defaultdict(int, f)
    for w, c in g.items():
        h[w] = (h[w] + s * c) % p
    return {w: c for w, c in h.items() if c}


def br(f, g):
    return add(mul(f, g), mul(g, f), -1)


def sc(f, s):
    return {w: c * s % p for w, c in f.items() if c * s % p}


a, b, c = {'a': 1}, {'b': 1}, {'c': 1}
H1 = br(br(a, b), c)
H2 = br(br(b, c), a)


def tower(start, sign):
    E = {1: start}
    for k in range(2, 5):
        E[k] = sc(br(H1, E[k - 1]), sign)
    return E


E12 = tower(br(H1, a), 1)
E21 = tower(br(b, c), -1)
E23 = tower(br(H1, b), 1)
E32 = tower(br(c, a), -1)


def pw(f, n):
    r = {'': 1}
    for _ in range(n):
        r = mul(r, f)
    return r


K = add(br(E12[1], E21[4]), br(E12[4], E21[1]), -1)
C1 = add(add(pw(H1, 5), br(E12[1], E21[4]), -1), br(E23[1], E32[4]), -1)
C2 = add(pw(H2, 5), br(E12[1], E21[4]))
K2 = add(br(E23[1], E32[4]), br(E23[4], E32[1]), -1)
vecs = [K, C1, C2, K2]
for v in vecs:
    assert all((w.count('a'), w.count('b'), w.count('c')) == (5, 5, 5) for w in v)
with open(sys.argv[1], 'w') as fo:
    fo.write('%d\n' % len(vecs))
    for v in vecs:
        fo.write('%d\n' % len(v))
        for w, x in sorted(v.items()):
            fo.write('%s %d\n' % (w, x))
print('terms', [len(v) for v in vecs])
