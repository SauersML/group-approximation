"""Exact checks for integral-piecewise-projective-groups-are-locally-subgroups-of-f.

Phi is Minkowski's question mark on R, normalised by Phi(x + n) = Phi(x) + n: on [n, n+1] it
sends the Stern-Brocot (Farey mediant) tree to the dyadic midpoint tree.  All arithmetic is exact
(Fractions); Phi is evaluated on rationals and Phi^{-1} on dyadics by the same tree descent.

Checks:
  1. Dictionary: for random gamma in SL2(Z) and random Farey intervals I such that gamma(I) is a
     bounded Farey interval, Phi o gamma o Phi^{-1} is affine on Phi(I), with slope a power of 2 and
     dyadic translation part (tested on all dyadic points of depth <= 7 in Phi(I)).
  2. Reverse dictionary: for random standard dyadic intervals I, J the affine map I -> J pulls back
     to the SL2(Z) matrix [J-Farey basis][I-Farey basis]^{-1} on Phi^{-1}(I).
  3. Breakpoint closure: in the PL picture P (pieces 2^k t + b, b dyadic), random words in
     generators whose breakpoints lie in (1/M) Z[1/2] keep all breakpoints there, and the rescaling
     t -> M t conjugates them to maps with dyadic breakpoints and dyadic translation parts.
  4. Example: h = 2t on [0,1/3], t/2 + 1/2 on [1/3,1] (identity elsewhere) pulls back to an element
     of G_Z with breakpoint Phi^{-1}(1/3) = sqrt(2) - 1, a quadratic irrational (checked: the
     descent path is eventually periodic, and the fixed point of the period matrix is sqrt(2)-1).
Run: python3 question_mark_localization.py   (prints OK lines, raises on failure)
"""
import random
from fractions import Fraction as Q
from math import floor

random.seed(20260919)


def is_dyadic(x):
    d = Q(x).denominator
    return d & (d - 1) == 0


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def qm(x):
    """Minkowski ?(x) for rational x, exact (dyadic result)."""
    x = Q(x)
    n = floor(x)
    if x == n:
        return Q(n)
    p, q, pp, qq = n, 1, n + 1, 1  # Farey pair p/q < pp/qq
    l, r = Q(n), Q(n + 1)
    while True:
        mp, mq = p + pp, q + qq
        m = Q(mp, mq)
        mid = (l + r) / 2
        if x == m:
            return mid
        if x < m:
            pp, qq, r = mp, mq, mid
        else:
            p, q, l = mp, mq, mid


def qm_inv(s):
    """?^{-1}(s) for dyadic s, exact (rational result)."""
    s = Q(s)
    assert is_dyadic(s)
    n = floor(s)
    if s == n:
        return Q(n)
    p, q, pp, qq = n, 1, n + 1, 1
    l, r = Q(n), Q(n + 1)
    while True:
        mp, mq = p + pp, q + qq
        mid = (l + r) / 2
        if s == mid:
            return Q(mp, mq)
        if s < mid:
            pp, qq, r = mp, mq, mid
        else:
            p, q, l = mp, mq, mid


def farey_interval_of(l, r):
    """Farey basis ((p,q),(pp,qq)) of the Farey interval Phi^{-1}([l,r]), [l,r] standard dyadic."""
    a, b = qm_inv(l), qm_inv(r)
    return (a.numerator, a.denominator), (b.numerator, b.denominator)


def mob(M, x):
    (a, b), (c, d) = M
    den = c * x + d
    assert den != 0
    return Q(a * x + b, 1) / den if not isinstance(x, Q) else (a * x + b) / den


def matmul(A, B):
    return ((A[0][0]*B[0][0] + A[0][1]*B[1][0], A[0][0]*B[0][1] + A[0][1]*B[1][1]),
            (A[1][0]*B[0][0] + A[1][1]*B[1][0], A[1][0]*B[0][1] + A[1][1]*B[1][1]))


def random_sl2z(length=6):
    S = ((0, -1), (1, 0))
    T = ((1, 1), (0, 1))
    Ti = ((1, -1), (0, 1))
    M = ((1, 0), (0, 1))
    for _ in range(length):
        M = matmul(M, random.choice([S, T, Ti, T]))
    return M


def random_standard_dyadic(depth_max=6, span=3):
    n = random.randint(-span, span)
    k = random.randint(1, depth_max)
    j = random.randint(0, 2**k - 1)
    return Q(n) + Q(j, 2**k), Q(n) + Q(j + 1, 2**k)


def dyadic_points(l, r, depth=7):
    w = r - l
    return [l + w * Q(i, 2**depth) for i in range(2**depth + 1)]


def check1(trials=300):
    done = 0
    while done < trials:
        g = random_sl2z(random.randint(1, 8))
        l, r = random_standard_dyadic()
        (p, q), (pp, qq) = farey_interval_of(l, r)
        # image basis: columns g(p,q), g(pp,qq); bounded and oriented iff both denominators > 0
        (a, b), (c, d) = g
        ip, iq = a*p + b*q, c*p + d*q
        jp, jq = a*pp + b*qq, c*pp + d*qq
        if iq <= 0 or jq <= 0:
            continue  # gamma(I) contains infinity or reverses; the dictionary only uses good I
        pts = dyadic_points(l, r)
        vals = [qm(mob(g, qm_inv(s))) for s in pts]
        slope = (vals[-1] - vals[0]) / (r - l)
        for s, v in zip(pts, vals):
            assert v == vals[0] + slope * (s - l), "not affine"
        assert slope > 0 and slope.denominator & (slope.denominator - 1) == 0
        assert slope.numerator & (slope.numerator - 1) == 0, "slope not a power of 2"
        assert is_dyadic(vals[0] - slope * l), "translation part not dyadic"
        done += 1
    print(f"OK 1: Phi gamma Phi^-1 is dyadic affine on Phi(I) for {trials} good Farey intervals")


def check2(trials=200):
    for _ in range(trials):
        l, r = random_standard_dyadic()
        l2, r2 = random_standard_dyadic()
        (p, q), (pp, qq) = farey_interval_of(l, r)
        (u, v), (uu, vv) = farey_interval_of(l2, r2)
        assert pp*q - p*qq == 1 and uu*v - u*vv == 1
        # gamma = [[u,uu],[v,vv]] [[p,pp],[q,qq]]^{-1}; the inverse of a det-1 matrix is integral
        inv = ((qq, -pp), (-q, p))
        g = matmul(((u, uu), (v, vv)), inv)
        assert g[0][0]*g[1][1] - g[0][1]*g[1][0] == 1
        for s in dyadic_points(l, r, 6):
            aff = l2 + (s - l) * (r2 - l2) / (r - l)
            assert qm(mob(g, qm_inv(s))) == aff
    print(f"OK 2: affine maps between standard dyadic intervals pull back to SL2(Z) ({trials} trials)")


class PL:
    """Homeomorphism of R: list of (breakpoint list, pieces) with pieces (slope, intercept)."""

    def __init__(self, bps, pieces):
        assert len(pieces) == len(bps) + 1
        self.bps, self.pieces = list(bps), list(pieces)
        for x, (k1, b1), (k2, b2) in zip(self.bps, self.pieces, self.pieces[1:]):
            assert k1 * x + b1 == k2 * x + b2

    def piece_at(self, x, side=+1):
        i = 0
        while i < len(self.bps) and (x > self.bps[i] or (side > 0 and x == self.bps[i])):
            i += 1
        return self.pieces[i]

    def __call__(self, x):
        k, b = self.piece_at(x)
        return k * x + b

    def inverse(self):
        img = [self(x) for x in self.bps]
        return PL(img, [(1 / k, -b / k) for (k, b) in self.pieces])

    def compose(self, other):  # self o other
        cand = set(other.bps) | {other.inverse()(x) for x in self.bps}
        cand = sorted(cand)
        pieces = []
        probes = [cand[0] - 1] + [(a + c) / 2 for a, c in zip(cand, cand[1:])] + [cand[-1] + 1] if cand else [Q(0)]
        for x in probes:
            k2, b2 = other.piece_at(x)
            k1, b1 = self.piece_at(other(x))
            pieces.append((k1 * k2, k1 * b2 + b1))
        bps, merged = [], [pieces[0]]
        for x, pc in zip(cand, pieces[1:]):
            if pc != merged[-1]:
                bps.append(x)
                merged.append(pc)
        return PL(bps, merged)

    def conj_scale(self, M):  # t -> M t conjugation: sigma f sigma^{-1}
        return PL([M * x for x in self.bps], [(k, M * b) for (k, b) in self.pieces])


def bump(a, c, m):
    """2t-type bump on [a, c] with interior breakpoint m (slopes 2 then 1/2), identity outside."""
    # f = t on (-inf,a], 2t - a on [a,m], t/2 + e on [m,c], t on [c,inf); continuity fixes m, e
    e = c / 2
    assert 2 * m - a == m / 2 + e and m / 2 + e <= c
    return PL([a, m, c], [(Q(1), Q(0)), (Q(2), -a), (Q(1, 2), e), (Q(1), Q(0))])


def check3(trials=60):
    M = 15
    A_ok = lambda x: is_dyadic(Q(x) * M)
    # generators with breakpoints in (1/15)Z[1/2], dyadic translation parts
    gens = []
    for a, c in [(Q(0), Q(1)), (Q(1, 2), Q(3, 2)), (Q(-1), Q(2)), (Q(1, 4), Q(5, 4))]:
        m = (2 * c / 2 + 2 * a) / 3  # solves 2m - a = m/2 + c/2
        gens.append(bump(a, c, m))
    shift = PL([], [(Q(1), Q(1))])
    gens.append(shift)
    # a bump with breakpoint 1/5-type: a=0, c=2/5? c must keep dyadic intercept c/2: choose a, c dyadic.
    for g in gens:
        for (k, b) in g.pieces:
            assert is_dyadic(b)
        assert all(A_ok(x) for x in g.bps), g.bps
    allg = gens + [g.inverse() for g in gens]
    for _ in range(trials):
        w = random.choice(allg)
        for _ in range(random.randint(1, 7)):
            w = random.choice(allg).compose(w)
        assert all(A_ok(x) for x in w.bps)
        assert all(is_dyadic(b) for (_, b) in w.pieces)
        v = w.conj_scale(M)
        assert all(is_dyadic(x) for x in v.bps), v.bps
        assert all(is_dyadic(b) for (_, b) in v.pieces)
    nondyadic = sum(1 for g in gens for x in g.bps if not is_dyadic(x))
    assert nondyadic > 0
    print(f"OK 3: {trials} random words keep breakpoints in (1/{M})Z[1/2]; t->{M}t makes them dyadic "
          f"({nondyadic} non-dyadic generator breakpoints)")


def check4():
    h = bump(Q(0), Q(1), Q(1, 3))
    assert h.bps == [0, Q(1, 3), 1]
    # descent path of 1/3 = 0.010101..._2 is L R L R ...: eventually periodic, period matrix LR
    # Stern-Brocot: L = [[1,0],[1,1]], R = [[1,1],[0,1]] acting on the Farey basis; the descent point
    # x = Phi^{-1}(1/3) is the fixed point in (0,1) of the period, x = LR(x) with LR = [[1,1],[1,2]].
    LR = matmul(((1, 0), (1, 1)), ((1, 1), (0, 1)))
    assert LR == ((1, 1), (1, 2))
    # 1/3 = 0.0(10)^inf in binary, so ?^{-1}(1/3) = [0;2,1,1,1,...] = 1/phi^2 = (3 - sqrt 5)/2,
    # a quadratic irrational (NOT sqrt2 - 1: ?(sqrt2 - 1) = ?([0;2,2,2,..]) = 2/5).
    target = (3 - 5 ** 0.5) / 2
    for n in range(5, 40):
        cf = [0, 2] + [1] * n
        v = Q(cf[-1])
        for a in reversed(cf[:-1]):
            v = a + 1 / v
        last = v
    assert abs(float(last) - target) < 1e-12
    assert abs(float(qm(last)) - 1 / 3) < 1e-9
    v = Q(0)
    for n in range(1, 40):
        cf = [0] + [2] * n
        v = Q(cf[-1])
        for a in reversed(cf[:-1]):
            v = a + 1 / v
    assert abs(float(qm(v)) - 2 / 5) < 1e-9
    h3 = h.conj_scale(3)
    assert all(is_dyadic(x) for x in h3.bps) and all(is_dyadic(b) for (_, b) in h3.pieces)
    print("OK 4: breakpoint 1/3 of h pulls back to (3-sqrt5)/2; t->3t conjugate of h has breakpoints",
          [str(x) for x in h3.bps])


if __name__ == "__main__":
    check1()
    check2()
    check3()
    check4()
