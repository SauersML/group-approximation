# Single-label iid chords on the Bernoulli shift of L = F(a,b) over K = <a, b a b^-2>.
# Points of one orbit = group elements g (point g.x0).  K-class of g = right coset Kg.
# A chord with label h at a point g in D joins the classes Kg and Khg.
# The b-edge at g is derived iff Kg and Kbg are joined by chords (fold exactness
# is not needed: this is the definition of R_K v Phi containing (g, bg)).
# Truncation: only chords at points of the ball B_R are used, so the derived
# fraction is a lower bound for the untruncated value.
import random
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from core import core, red, mul

KC, KB = core([[1], [2, 1, -2, -2]])


def coset(g):
    u = KB
    for i, x in enumerate(g):
        if x in KC[u]:
            u = KC[u][x]
        else:
            return (u, tuple(g[i:]))
    return (u, ())


def ball(R):
    out = [[]]
    layer = [[]]
    for _ in range(R):
        nl = []
        for w in layer:
            for x in (1, -1, 2, -2):
                if w and w[-1] == -x:
                    continue
                nl.append(w + [x])
        out += nl
        layer = nl
    return out


class UF:
    def __init__(self):
        self.p = {}

    def f(self, x):
        p = self.p
        p.setdefault(x, x)
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x

    def u(self, x, y):
        x, y = self.f(x), self.f(y)
        if x != y:
            self.p[max(x, y)] = min(x, y)


def run(labels, p, R, r, seed=0):
    """labels: list of words h; each point of B_R carries each label with prob p/len(labels)."""
    rng = random.Random(seed)
    B = ball(R)
    uf = UF()
    q = p / len(labels)
    for g in B:
        for h in labels:
            if rng.random() < q:
                uf.u(coset(g), coset(mul(h, g)))
    inner = [g for g in B if len(g) <= r]
    ok = sum(uf.f(coset(g)) == uf.f(coset(mul([2], g))) for g in inner)
    return ok / len(inner)


if __name__ == '__main__':
    import ast
    labels = ast.literal_eval(sys.argv[1])
    R = int(sys.argv[2]); r = int(sys.argv[3])
    for p in [float(x) for x in sys.argv[4].split(',')]:
        vals = [run(labels, p, R, r, seed=s) for s in range(int(sys.argv[5]) if len(sys.argv) > 5 else 1)]
        print(labels, 'p=%.4f' % p, 'derived fraction', ' '.join('%.3f' % v for v in vals))
