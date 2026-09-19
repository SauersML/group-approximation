# ZG for G = F_4 x|_phi <y>: group elements (u, m) = u y^m, u reduced fibre word.
from fbc import apply, PHI, PHII, red, inv, xj
from functools import lru_cache
@lru_cache(maxsize=None)
def phipow(u, m):
    for _ in range(abs(m)): u = apply(PHI if m > 0 else PHII, u)
    return u
def mul(g, h): return (red(g[0] + phipow(h[0], g[1])), g[1] + h[1])
def ginv(g): return (phipow(inv(g[0]), -g[1]), -g[1])
E = ('', 0)
X = (xj(0), 0); Y = ('', 1)
def elt(word):
    g = E
    for ch in word:
        h = {'x': X, 'y': Y, 'X': ginv(X), 'Y': ginv(Y)}[ch]
        g = mul(g, h)
    return g
# ring elements: dict elt -> int
def rmul(a, b):
    out = {}
    for g, s in a.items():
        for h, t in b.items():
            k = mul(g, h); out[k] = out.get(k, 0) + s * t
    return {k: v for k, v in out.items() if v}
def radd(a, b, s=1):
    out = dict(a)
    for k, v in b.items(): out[k] = out.get(k, 0) + s * v
    return {k: v for k, v in out.items() if v}
BAS = {'a': 'XyxYx', 'b': 'Xyyyx', 'c': 'XYxyx', 'd': 'y', 'e': 'xyX'}
def bword_to_x(u):
    return ''.join(BAS[ch] if ch.islower() else inv_x(BAS[ch.lower()]) for ch in u)
def inv_x(w): return ''.join(c.swapcase() for c in reversed(w))
def fox(u, z):
    # left Fox derivative d_z(u) in ZG, u a word in basis letters
    out = {}; pre = ''
    for ch in u:
        if ch == z: k = elt(bword_to_x(pre)); out[k] = out.get(k, 0) + 1
        pre += ch
        if ch == z.upper(): k = elt(bword_to_x(pre)); out[k] = out.get(k, 0) - 1
    return {k: v for k, v in out.items() if v}
u0 = 'dEbcBADDed'; u1 = 'bcBAAbDcBd'
g = elt('Xy')
W = 'yxYXXyyxYXYxYYxyXy'
if __name__ == '__main__':
    i0, i1 = elt(bword_to_x(u0)), elt(bword_to_x(u1))
    print('iota u0', i0, 'iota u1', i1, 'w', elt(W))
    print('u1 = g u0 g^-1 ?', mul(mul(g, i0), ginv(g)) == i1)
    C = {z: radd(rmul({g: 1}, fox(u0, z)), fox(u1, z), -1) for z in 'abcde'}
    for z in 'abcde': print(z, len(C[z]), sorted(C[z].items(), key=lambda t: t[0][1]))
