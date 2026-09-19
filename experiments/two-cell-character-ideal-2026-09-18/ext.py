# Finite G-sets extending the folded graph Gamma of a configuration: permutations x, y of {0..n-1}
# extending the partial maps of Gamma (vertices 0..|Gamma|-1) with w(x,y) = 1.  If one exists, the
# stabiliser K of v0 has finite index, H <= K, and g = t_1 is not in H (v0^g = v1 != v0).
# usage: python3 ext.py NMAX   (candidate 2 hard-wired)
import sys, itertools
from fc import LET
E = [(0, 0, 0), (0, 1, 1), (1, 1, 0), (1, 2, 1), (2, 0, 1), (2, 3, 0), (3, 3, 1), (3, 4, 0), (4, 4, 1)]
W = 'yxYXXyyxYXYxYYxyXy'
m = 5


def check(X, Y, n):
    P = {'x': X, 'y': Y, 'X': [X.index(i) for i in range(n)], 'Y': [Y.index(i) for i in range(n)]}
    for v in range(n):
        u = v
        for ch in W: u = P[ch][u]
        if u != v: return False
    return True


def extend(part, n):
    """all permutations of range(n) extending the partial injection part (dict)."""
    dom = [i for i in range(n) if i not in part]; img = [j for j in range(n) if j not in part.values()]
    for p in itertools.permutations(img):
        f = dict(part); f.update(zip(dom, p)); yield [f[i] for i in range(n)]


NMAX = int(sys.argv[1])
px = {a: b for a, b, l in E if l == 0}; py = {a: b for a, b, l in E if l == 1}
for n in range(m, NMAX + 1):
    cnt = 0
    for X in extend(px, n):
        for Y in extend(py, n):
            if check(X, Y, n):
                cnt += 1
                if cnt <= 3: print('n', n, 'X', X, 'Y', Y, flush=True)
    print('n', n, 'extensions', cnt, flush=True)
