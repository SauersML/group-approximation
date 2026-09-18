"""Rotation twists of Thompson generators inside T.

Points of T/R_D correspond to elements of F (T = F R_D exactly). The finite set
{R_D, f_2 R_D, ..., f_n R_D} lies in one orbit of a subgroup H <= T iff H contains
elements h_i in f_i R_D.  Here we search small dyadic twists a, b and test
whether A = x0 rho_a and B = x1 rho_b are torsion, commute, or generate a finite group.

Circle PL maps are stored by a lift: sorted nodes x in [0,1) (0 always a node)
and lift values y (strictly increasing, y(x+1) = y(x) + 1).
"""
from fractions import Fraction as Q
import bisect, itertools, json, sys


class PL:
    def __init__(self, xs, ys):
        self.xs, self.ys = list(xs), list(ys)

    def __call__(self, t):
        n = int(t // 1)
        s = t - n
        xs, ys = self.xs, self.ys
        i = bisect.bisect_right(xs, s) - 1
        if i < 0:
            x0, y0 = xs[-1] - 1, ys[-1] - 1
            x1, y1 = xs[0], ys[0]
        else:
            x0, y0 = xs[i], ys[i]
            if i + 1 < len(xs):
                x1, y1 = xs[i + 1], ys[i + 1]
            else:
                x1, y1 = xs[0] + 1, ys[0] + 1
        return y0 + (s - x0) * (y1 - y0) / (x1 - x0) + n

    def inv_nodes(self):
        # nodes of the inverse: images mod 1
        return sorted({(y - (y // 1)) for y in self.ys})

    def inverse(self):
        pts = []
        for x, y in zip(self.xs, self.ys):
            pts.append((y - (y // 1), x - (y // 1)))
        pts.sort()
        ys_ = [p[1] for p in pts]
        xs_ = [p[0] for p in pts]
        m = PL(xs_, ys_)
        return m.normalize()

    def normalize(self):
        # ensure 0 is a node and remove collinear nodes
        if self.xs[0] != 0:
            v = self(Q(0))
            xs = [Q(0)] + self.xs
            ys = [v] + self.ys
        else:
            xs, ys = self.xs, self.ys
        # shift so that value at 0 in [0,1)
        sh = ys[0] // 1
        ys = [y - sh for y in ys]
        m = len(xs)
        keep = [0]
        for i in range(1, m):
            xp, yp = xs[keep[-1]], ys[keep[-1]]
            if i + 1 < m:
                xn, yn = xs[i + 1], ys[i + 1]
            else:
                xn, yn = Q(1), ys[0] + 1
            if (ys[i] - yp) * (xn - xs[i]) != (yn - ys[i]) * (xs[i] - xp):
                keep.append(i)
        return PL([xs[i] for i in keep], [ys[i] for i in keep])

    def key(self):
        return (tuple(self.xs), tuple(self.ys))


def compose(h, g):
    """h o g"""
    ginv = g.inverse()
    nodes = set(g.xs)
    for z in h.xs:
        w = ginv(z)
        nodes.add(w - (w // 1))
    nodes.add(Q(0))
    xs = sorted(nodes)
    ys = [h(g(x)) for x in xs]
    return PL(xs, ys).normalize()


def rot(a):
    return PL([Q(0)], [Q(a) - (Q(a) // 1)])


ID = rot(0)
X0 = PL([Q(0), Q(1, 2), Q(3, 4)], [Q(0), Q(1, 4), Q(1, 2)]).normalize()
X1 = PL([Q(0), Q(1, 2), Q(3, 4), Q(7, 8)], [Q(0), Q(1, 2), Q(5, 8), Q(3, 4)]).normalize()


def is_id(g):
    return g.key() == ID.key()


def order(g, bound):
    p = g
    for q in range(1, bound + 1):
        if is_id(p):
            return q
        p = compose(g, p)
    return None


def group_size(gens, bound):
    seen = {ID.key(): ID}
    frontier = [ID]
    while frontier:
        nf = []
        for u in frontier:
            for s in gens:
                v = compose(s, u)
                k = v.key()
                if k not in seen:
                    seen[k] = v
                    nf.append(v)
                    if len(seen) > bound:
                        return None
        frontier = nf
    return len(seen)


if __name__ == "__main__":
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    OB = int(sys.argv[2]) if len(sys.argv) > 2 else 64
    N = 2 ** K
    tw = [Q(i, N) for i in range(N)]
    torsA = {}
    torsB = {}
    for a in tw:
        torsA[a] = order(compose(X0, rot(a)), OB)
        torsB[a] = order(compose(X1, rot(a)), OB)
    comm = []
    finite = []
    for a in tw:
        A = compose(X0, rot(a))
        for b in tw:
            B = compose(X1, rot(b))
            if compose(A, B).key() == compose(B, A).key():
                comm.append((str(a), str(b)))
            if torsA[a] and torsB[b]:
                s = group_size([A, B], 5000)
                if s:
                    finite.append((str(a), str(b), s))
    out = {
        "K": K,
        "order_bound": OB,
        "x0_twists_torsion": {str(a): o for a, o in torsA.items() if o},
        "x1_twists_torsion": {str(a): o for a, o in torsB.items() if o},
        "commuting_pairs": comm,
        "finite_pairs_(a,b,size)": finite,
    }
    print(json.dumps(out, indent=1))
