"""Bootstrap absorption of c-edges for the Gamma_mal stage pair.

Delta_0 = <a, b>, b = c a c^-2, inside Delta_1 = F(a,c).  Orbit graph of a free
Delta_1-action = Cayley graph (left multiplication).  Graphing: a-edges and
b-edges everywhere; c-edge g -- c g only for g in A (i.i.d. density eps).
Question: is e ~ c (the c-edge at the root absorbed)?  Computed on the ball of
radius R (truncation => lower bound for the infinite graph).
Usage: python3 absorb.py R eps trials seed
"""
import random
import sys

INV = {"a": "A", "A": "a", "c": "C", "C": "c"}


def lmul(s, g):
    """reduce(s + g) for reduced s, g."""
    s = list(s)
    i = 0
    while s and i < len(g) and s[-1] == INV[g[i]]:
        s.pop()
        i += 1
    return "".join(s) + g[i:]


def ball(R):
    layer, out = [""], [""]
    for _ in range(R):
        nxt = []
        for w in layer:
            for x in "aAcC":
                if not w or w[0] != INV[x]:
                    nxt.append(x + w)
        out += nxt
        layer = nxt
    return out


def find(p, x):
    while p[x] != x:
        p[x] = p[p[x]]
        x = p[x]
    return x


def fd(p, x):
    while x in p:
        x = p[x]
    return x


def run(R, eps, trials, seed):
    rng = random.Random(seed)
    V = ball(R)
    idx = {w: i for i, w in enumerate(V)}
    base = []
    for i, w in enumerate(V):
        for s in ("a", "caCC"):
            j = idx.get(lmul(s, w))
            if j is not None:
                base.append((i, j))
    cedge = [idx.get(lmul("c", w)) for w in V]
    e, c = idx[""], idx["c"]
    p0 = list(range(len(V)))
    for i, j in base:
        ri, rj = find(p0, i), find(p0, j)
        if ri != rj:
            p0[ri] = rj
    comp = [find(p0, i) for i in range(len(V))]
    cedge = [None if j is None else (comp[i], comp[j]) for i, j in enumerate(cedge)]
    e, c = comp[e], comp[c]
    root = idx[""]
    hits = 0
    for _ in range(trials):
        p = {}
        for i in range(len(V)):
            if cedge[i] is not None and i != root and rng.random() < eps:
                ri, rj = fd(p, cedge[i][0]), fd(p, cedge[i][1])
                if ri != rj:
                    p[ri] = rj
        hits += fd(p, e) == fd(p, c)
    return hits / trials


if __name__ == "__main__":
    R, eps, T, seed = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print(R, eps, run(R, eps, T, seed))
