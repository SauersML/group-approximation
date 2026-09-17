"""Exact word length in F over X_n = {x0..xn} by A* with the admissible, consistent heuristic
l_inf (number of non-right carets of the reduced tree pair = length over {x_i : i >= 0}).

Element syntax: tokens like x3 (x_3) or X3 (x_3^-1), code convention of geocomb_sat.py
(x_{j+1} = x_i x_j x_i^-1, products read left to right as 'then').
usage: lengthF.py n token...
"""
import sys, heapq
from fastF import rmul, inv, ID, X0, X1, ONE

_gens = [X0, X1]


def gen(i):
    while len(_gens) <= i:
        _gens.append(rmul(rmul(X0, _gens[-1]), inv(X0)))
    return _gens[i]


def elem(tokens):
    f = ID
    for t in tokens:
        g = gen(int(t[1:]))
        f = rmul(f, g if t[0] == "x" else inv(g))
    return f


def _eval(f, t):
    from fastF import _ev
    return _ev(f, t)


def leaves(f):
    """reduced tree-pair leaves: list of (domain interval) on which f is affine with dyadic image"""
    bps = [x for x, _ in f[1:-1]]
    out = []
    stack = [(0, ONE)]
    while stack:
        lo, hi = stack.pop()
        inside = any(lo < b < hi for b in bps)
        ok = False
        if not inside:
            ylo, yhi = _eval(f, lo), _eval(f, hi)
            w = yhi - ylo
            if w & (w - 1) == 0 and ylo % w == 0:
                ok = True
        if ok:
            out.append((lo, hi))
        else:
            mid = (lo + hi) >> 1
            stack.append((mid, hi))
            stack.append((lo, mid))
    return out


def linf(f):
    L = leaves(f)
    lo, hi = L[-1]
    r1 = (ONE // (hi - lo)).bit_length() - 1
    ylo, yhi = _eval(f, lo), _eval(f, hi)
    r2 = (ONE // (yhi - ylo)).bit_length() - 1
    return 2 * (len(L) - 1) - r1 - r2


def length(f, n, limit=2_000_000):
    """exact l_n(f) via A* towards the identity; returns (length, expanded)"""
    S = []
    for i in range(n + 1):
        S += [gen(i), inv(gen(i))]
    g0 = {f: 0}
    pq = [(linf(f), 0, f)]
    closed = set()
    exp = 0
    while pq:
        fs, gc, x = heapq.heappop(pq)
        if x == ID:
            return gc, exp
        if x in closed:
            continue
        closed.add(x)
        exp += 1
        if exp > limit:
            raise RuntimeError("limit")
        for s in S:
            y = rmul(x, s)
            if y in closed:
                continue
            ng = gc + 1
            if ng < g0.get(y, 1 << 30):
                g0[y] = ng
                heapq.heappush(pq, (ng + linf(y), ng, y))
    raise RuntimeError("unreachable")


if __name__ == "__main__":
    n = int(sys.argv[1])
    f = elem(sys.argv[2:])
    print("l_inf=%d l_%d=%d (expanded %d)" % ((linf(f), n) + length(f, n)))
