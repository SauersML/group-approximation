# Self-contained check that the cylinder row c of configuration (C2) is unimodular over ZG:
#     c_a d_a + c_b d_b + c_c d_c + c_d d_d + c_e d_e = 1   in ZG,  G = <x, y | w>.
# No imports from the other scripts. Group elements are put in the normal form of
# G = F_4 x|_phi <y> (F_4 = <p,q,r,s> = <x_-2, x_-1, x_0, x_1>, x_j = y^j x y^-j), which is a
# solution of the word problem because G is this semidirect product (Magnus; proof section 1).
W = 'yxYXXyyxYXYxYYxyXy'
BAS = {'a': 'XyxYx', 'b': 'Xyyyx', 'c': 'XYxyx', 'd': 'y', 'e': 'xyX'}
U0, U1, G_ = 'dEbcBADDed', 'bcBAAbDcBd', 'Xy'     # cells u_0, u_1 and g = t_1 (v_0 = 3, v_1 = 0)
D = {  # the certificate, as signed words in x, y
    'a': [(+1, 'Xyx'), (+1, 'XyxYXyx'), (-1, 'xyXYYxYXyyXyxy'),
          (-1, 'YYxyXyyxYXXyxYxYYxyXyyxYXYXyyXYxxyXYYxYXyyXyxyy')],
    'b': [(+1, 'Xyx')],
    'c': [(-1, '')],
    'd': [(+1, 'YXyx'), (-1, 'Xyx'), (+1, 'x')],
    'e': [(+1, 'YXyx'), (-1, 'yXYxxyXYYxYXyyXyxy'), (+1, 'x'), (+1, 'xYXyx'),
          (-1, 'xyXYXyx'), (+1, 'xx'), (-1, 'yx')],
}
def inv(u): return ''.join(c.swapcase() for c in reversed(u))
def fred(u):
    out = []
    for c in u:
        if out and out[-1] == c.swapcase(): out.pop()
        else: out.append(c)
    return ''.join(out)
# --- the fibre relation from w: w = prod x_{j_i}^{e_i}; levels -2..2 occur, extreme ones once
def levels(u):
    lev, out = 0, []
    for c in u:
        if c == 'y': lev += 1
        elif c == 'Y': lev -= 1
        else: out.append((lev, 1 if c == 'x' else -1))
    return lev, out
lw, LW = levels(W)
assert lw == 0
js = [j for j, _ in LW]
lo, hi = min(js), max(js)
assert [j for j in js].count(lo) == 1 and js.count(hi) == 1
# normalise levels so the fibre basis is x_{lo..hi-1} after shifting (lo = -2 here, basis -2..1)
NAME = {-2: 'p', -1: 'q', 0: 'r', 1: 's'}
def lvl_word(seq):  # list of (level, sign) -> symbolic word over levels
    return seq
def solve_top(seq, top):
    # w = A x_top^e B = 1  =>  x_top^e = A^-1 B^-1
    i = [k for k, (j, _) in enumerate(seq) if j == top][0]
    e = seq[i][1]
    A, B = seq[:i], seq[i + 1:]
    rhs = [(j, -s) for j, s in reversed(A)] + [(j, -s) for j, s in reversed(B)]
    return rhs if e == 1 else [(j, -s) for j, s in reversed(rhs)]
TOP = solve_top(LW, hi)   # x_hi in terms of x_{lo..hi-1}
BOT = solve_top(LW, lo)   # x_lo in terms of x_{lo+1..hi}
from functools import lru_cache
@lru_cache(maxsize=None)
def xj(j):
    # x_j as a reduced word in p, q, r, s  (levels -2..1)
    if j in NAME: return NAME[j]
    if j > 1:
        k = j - hi
        return fred(''.join(xj(l + k) if s == 1 else inv(xj(l + k)) for l, s in TOP))
    k = j - lo
    return fred(''.join(xj(l + k) if s == 1 else inv(xj(l + k)) for l, s in BOT))
def nf(u):
    # word in x, y -> (reduced fibre word, y exponent)
    lev, seq = levels(u)
    return fred(''.join(xj(j) if s == 1 else inv(xj(j)) for j, s in seq)), lev
def ring(terms):
    out = {}
    for s, u in terms:
        k = nf(u); out[k] = out.get(k, 0) + s
    return {k: v for k, v in out.items() if v}
def tox(bw): return ''.join(BAS[c] if c.islower() else inv(BAS[c.lower()]) for c in bw)
def fox(u, z):
    # left Fox derivative d_z u, as signed x,y words (prefixes mapped to G)
    out, pre = [], ''
    for c in u:
        if c == z: out.append((+1, tox(pre)))
        pre += c
        if c == z.upper(): out.append((-1, tox(pre)))
    return out
def fibmul(u, m, v, n):
    # (u y^m)(v y^n) = u (y^m v y^-m) y^(m+n); y^m v y^-m shifts every level by m
    return nf(fromfib(u) + 'y' * m + 'Y' * (-m) + fromfib(v) + 'y' * n + 'Y' * (-n))
REV = {v: k for k, v in NAME.items()}
def fromfib(u):
    w = ''
    for c in u:
        j = REV[c.lower()]; core = 'x' if c.islower() else 'X'
        w += ('y' * j if j > 0 else 'Y' * (-j)) + core + ('Y' * j if j > 0 else 'y' * (-j))
    return w
def rmul(A, B):
    out = {}
    for (u, m), s in A.items():
        for (v, n), t in B.items():
            k = fibmul(u, m, v, n); out[k] = out.get(k, 0) + s * t
    return {k: v for k, v in out.items() if v}
if __name__ == '__main__':
    # setting of the criterion: phi(u_0) = w, phi(u_1) = g w g^-1 in the free group F(x, y)
    assert fred(tox(U0)) == W, fred(tox(U0))
    assert fred(tox(U1)) == fred(G_ + W + inv(G_))
    print('phi(u_0) = w and phi(u_1) = g w g^-1 in F(x,y), with g = x^-1 y')
    total = {}
    for z in 'abcde':
        cz = ring([(s, G_ + u) for s, u in fox(U0, z)] + [(-s, u) for s, u in fox(U1, z)])
        dz = ring(D[z])
        for k, v in rmul(cz, dz).items(): total[k] = total.get(k, 0) + v
        print('c_%s has %d terms, d_%s has %d terms' % (z, len(cz), z, len(dz)))
    total = {k: v for k, v in total.items() if v}
    print('sum_x c_x d_x =', total)
    assert total == {('', 0): 1}
    print('CONCLUSION: c is unimodular over ZG, so (C2) is admissible (pd I_{G/H} <= 1)')
