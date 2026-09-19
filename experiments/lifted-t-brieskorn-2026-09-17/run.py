"""Compute the lifted Lochak-Schneps relation (beta~ alpha~)^5 = z^k in T-bar,
and check that alpha, beta generate T (by writing the Cannon-Floyd-Parry
generators A, B, C as words in alpha, beta)."""
from fractions import Fraction as Q
from pl import Lift, ID, Z

h = Q(1, 2)
alpha = Lift([(0, Q(1, 4)), (1, Q(5, 4))])                      # rotation by 1/4
beta = Lift([(0, h), (h, Q(3, 4)), (Q(3, 4), 1), (1, Q(3, 2))])  # triangle 0 -> 1/2 -> 3/4 -> 0

# Cannon-Floyd-Parry generators, canonical lifts
A = Lift([(0, 0), (h, Q(1, 4)), (Q(3, 4), h), (1, 1)])
B = Lift([(0, 0), (h, h), (Q(3, 4), Q(5, 8)), (Q(7, 8), Q(3, 4)), (1, 1)])
C = Lift([(0, Q(3, 4)), (h, 1), (Q(3, 4), Q(3, 2)), (1, Q(7, 4))])


def order_and_shift(g, nmax=60):
    p = g
    for n in range(1, nmax + 1):
        s = p.shift()
        if s is not None:
            return n, s
        p = g * p
    return None, None


for name, g in [("alpha", alpha), ("beta", beta), ("beta*alpha", beta * alpha),
                ("alpha*beta", alpha * beta), ("C", C)]:
    n, s = order_and_shift(g)
    print(f"{name}: order {n} in T, lift^{n} = z^{s}, translation number {Q(s, n) if n else None}")

# Lochak-Schneps commutator relations, lifted: must hold exactly (m = 0)
a, b = alpha, beta
def w(*fs):
    r = ID
    for f in fs:
        r = r * f
    return r
X = w(b, a, b)
Y1 = w(a, a, b, a, b, a, a)
Y2 = w(a, a, b, b, a, a, b, a, b, a, a, b, b, a, a)
for nm, Y in [("Y1", Y1), ("Y2", Y2)]:
    comm = X * Y * X.inverse() * Y.inverse()
    print(f"[beta alpha beta, {nm}] lifted =", "identity" if comm == ID else comm.pts)
