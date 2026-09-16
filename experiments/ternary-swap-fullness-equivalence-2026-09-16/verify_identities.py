#!/usr/bin/env python3
"""Sanity checks for research/artifacts/anti-central-swap-fullness-gives-projective-2026-09-16.md.

These checks support the hand proof. They do not replace it.

Part A  Finite subgroup Q = <w, d, h> of G = L_(F_3)(1,2)^x, seen through the depth-1 chart
        (scalar 2x2 matrices over F_3). Checks the chart relations, Lemma 7.2 of the
        2026-09-12 artifact (e_- [d] e_- = 0, [d] e_- [d] = eps_- - e_-) in F_3[Q], and the
        Klein/Hadamard idempotent relations of Lemma 2 in F_3[Q/{+-1}].
Part B  The tensor map Psi_0([g] (x) [h]) = [mu(g,h) mod +-1], restricted to the finite
        subgroup Q x Q of G x G. In the depth-2 chart mu(g,h) = diag(g,h), w = [[0,I],[I,0]],
        d = diag(I,-I), and h = [[I,I],[I,-I]]. Checks multiplicativity on random elements,
        Psi_0(eps_- (x) 1) = Psi_0(1 (x) eps_-) = f, and the flip [wbar] Psi_0(x (x) y) [wbar]
        = Psi_0(y (x) x).
Part C  An operator model on a vector space with a basis indexed by (Klein sector, n), in which
        all hypotheses of Theorem 5 hold (Y_i X_j = delta_ij f, Y X = f, Y [wbar] X = 0,
        X, Y, X_i, Y_i in f A f, Klein group and Hadamard involution). Checks the explicit
        witnesses b, c of Theorem 5: e_w b = b, c e_w = c, and c b = 1 on basis vectors.
        This catches typos in the formulas. It is not a universal model.

Run: timeout 600 python3 verify_identities.py
"""
import itertools
import random

P = 3
random.seed(20260916)


# ---------- matrices over F_3 ----------
def mmul(A, B):
    n = len(A)
    m = len(B[0])
    k = len(B)
    return tuple(tuple(sum(A[i][r] * B[r][j] for r in range(k)) % P for j in range(m)) for i in range(n))


def mneg(A):
    return tuple(tuple((-x) % P for x in row) for row in A)


def eye(n):
    return tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n))


def block(A, B, C, D):
    top = tuple(ra + rb for ra, rb in zip(A, B))
    bot = tuple(rc + rd for rc, rd in zip(C, D))
    return top + bot


def zero(n):
    return tuple(tuple(0 for _ in range(n)) for _ in range(n))


def diag2(g, h):
    n = len(g)
    return block(g, zero(n), zero(n), h)


def proj(A):
    """Canonical representative of A modulo {+-1}."""
    return min(A, mneg(A))


# ---------- group algebra over F_3 ----------
def ga(d):
    return {k: v % P for k, v in d.items() if v % P}


def gadd(x, y, s=1):
    out = dict(x)
    for k, v in y.items():
        out[k] = (out.get(k, 0) + s * v) % P
    return ga(out)


def gscale(x, c):
    return ga({k: c * v for k, v in x.items()})


def gmul(x, y, mul, norm=lambda g: g):
    out = {}
    for g, a in x.items():
        for h, b in y.items():
            k = norm(mul(g, h))
            out[k] = (out.get(k, 0) + a * b) % P
    return ga(out)


def closure(gens, mul, one):
    elems = {one}
    frontier = [one]
    while frontier:
        new = []
        for g in frontier:
            for s in gens:
                k = mul(g, s)
                if k not in elems:
                    elems.add(k)
                    new.append(k)
        frontier = new
    return sorted(elems)


def check(name, cond):
    print(("PASS  " if cond else "FAIL  ") + name)
    if not cond:
        raise SystemExit(1)


# ---------- Part A ----------
I2 = eye(2)
Z2 = mneg(I2)
w1 = ((0, 1), (1, 0))
d1 = ((1, 0), (0, 2))
h1 = ((1, 1), (1, 2))
check("A: w^2 = 1", mmul(w1, w1) == I2)
check("A: d^2 = 1", mmul(d1, d1) == I2)
check("A: d w d = -w", mmul(mmul(d1, w1), d1) == mneg(w1))
check("A: h^2 = -1", mmul(h1, h1) == Z2)
hinv = mneg(h1)
check("A: h w h^-1 = d", mmul(mmul(h1, w1), hinv) == d1)
check("A: h d h^-1 = w", mmul(mmul(h1, d1), hinv) == w1)

Q = closure([w1, d1, h1], mmul, I2)
print("     |Q| =", len(Q))
one = {I2: 1}
eps_m = ga({I2: 2, Z2: -2})
eps_p = ga({I2: 2, Z2: 2})
e = ga({I2: 2, w1: 2})
e_m = gmul(eps_m, e, mmul)
D = {d1: 1}
check("A: eps_- idempotent", gmul(eps_m, eps_m, mmul) == eps_m)
check("A: eps_+ + eps_- = 1", gadd(eps_p, eps_m) == one)
check("A: e_- idempotent", gmul(e_m, e_m, mmul) == e_m)
check("A: [d] e_- [d] = eps_- - e_-", gmul(gmul(D, e_m, mmul), D, mmul) == gadd(eps_m, e_m, -1))
check("A: e_- [d] e_- = 0", gmul(gmul(e_m, D, mmul), e_m, mmul) == {})

# Cohn family in the finite shadow: gamma_i beta_j = delta_ij eps_- holds formally for
# beta_1 = e_- b, beta_2 = [d] e_- b, gamma_1 = c e_-, gamma_2 = c e_- [d] whenever c e_- b = eps_-.
# Here only the cross term identity is testable: c e_- [d] e_- b = 0 for arbitrary b, c.
for _ in range(5):
    b = ga({random.choice(Q): random.randrange(3) for _ in range(6)})
    c = ga({random.choice(Q): random.randrange(3) for _ in range(6)})
    lhs = gmul(gmul(gmul(gmul(c, e_m, mmul), D, mmul), e_m, mmul), b, mmul)
    check("A: c e_- [d] e_- b = 0 (random b, c)", lhs == {})

# Klein / Hadamard relations in F_3[Q/+-1]
pm = lambda A, B: mmul(A, B)
nproj = proj
W = {proj(w1): 1}
Dd = {proj(d1): 1}
H = {proj(h1): 1}
ONE = {proj(I2): 1}


def pmul(x, y):
    return gmul(x, y, mmul, nproj)


def q(a, bb):
    return pmul(gadd(gscale(ONE, 2), gscale(W, 2 * a)), gadd(gscale(ONE, 2), gscale(Dd, 2 * bb)))


qs = {(a, bb): q(a, bb) for a in (1, -1) for bb in (1, -1)}
for s1, s2 in itertools.product(qs, repeat=2):
    prod = pmul(qs[s1], qs[s2])
    check("A: q%s q%s = delta q" % (s1, s2), prod == (qs[s1] if s1 == s2 else {}))
tot = {}
for s in qs:
    tot = gadd(tot, qs[s])
check("A: sum q_ab = 1", tot == ONE)
e_w = gadd(gscale(ONE, 2), gscale(W, 2))
f = gadd(gscale(ONE, 2), gscale(Dd, -2))
check("A: e_w = q_++ + q_+-", e_w == gadd(qs[(1, 1)], qs[(1, -1)]))
check("A: f = q_+- + q_--", f == gadd(qs[(1, -1)], qs[(-1, -1)]))
check("A: f e_w = q_+-", pmul(f, e_w) == qs[(1, -1)])
check("A: 2 e_w = 1 + [wbar]", gscale(e_w, 2) == gadd(ONE, W))
check("A: H^2 = 1", pmul(H, H) == ONE)
for (a, bb) in qs:
    check("A: H q_(%d,%d) H = q_(%d,%d)" % (a, bb, bb, a), pmul(pmul(H, qs[(a, bb)]), H) == qs[(bb, a)])
u = pmul(H, qs[(-1, 1)])
v = pmul(qs[(-1, 1)], H)
check("A: u = H q_-+ = q_+- H", u == pmul(qs[(1, -1)], H))
check("A: u in q_+- A q_-+", pmul(pmul(qs[(1, -1)], u), qs[(-1, 1)]) == u)
check("A: v u = q_-+", pmul(v, u) == qs[(-1, 1)])

# ---------- Part B ----------
I4 = eye(4)
w2 = block(zero(2), I2, I2, zero(2))
d2 = block(I2, zero(2), zero(2), Z2)
h2 = block(I2, I2, I2, Z2)
check("B: mu(1,1) = 1", diag2(I2, I2) == I4)
check("B: mu(-1,1) = -d", diag2(Z2, I2) == mneg(d2))
check("B: mu(1,-1) = d", diag2(I2, Z2) == d2)
check("B: depth-2 chart of w, d, h equals w (x) I, d (x) I, h (x) I",
      w2 == block(zero(2), I2, I2, zero(2)) and d2 == block(I2, zero(2), zero(2), Z2) and h2 == block(I2, I2, I2, Z2))
for g, hh, g2, hh2 in [tuple(random.choice(Q) for _ in range(4)) for _ in range(20)]:
    check("B: mu multiplicative", mmul(diag2(g, hh), diag2(g2, hh2)) == diag2(mmul(g, g2), mmul(hh, hh2)))
    check("B: w mu(g,h) w = mu(h,g)", mmul(mmul(w2, diag2(g, hh)), w2) == diag2(hh, g))


def psi0(x, y):
    """Psi_0(x (x) y) for x, y in F_3[Q]."""
    out = {}
    for g, a in x.items():
        for hh, b in y.items():
            k = proj(diag2(g, hh))
            out[k] = (out.get(k, 0) + a * b) % P
    return ga(out)


def p4mul(x, y):
    return gmul(x, y, mmul, proj)


ONE4 = {proj(I4): 1}
W4 = {proj(w2): 1}
D4 = {proj(d2): 1}
f4 = gadd(gscale(ONE4, 2), gscale(D4, -2))
check("B: Psi_0(eps_- (x) 1) = f", psi0(eps_m, one) == f4)
check("B: Psi_0(1 (x) eps_-) = f", psi0(one, eps_m) == f4)
check("B: Psi_0(eps_- (x) eps_-) = f", psi0(eps_m, eps_m) == f4)
check("B: Psi_0(1 (x) 1) = 1", psi0(one, one) == ONE4)


def rnd():
    return ga({random.choice(Q): random.randrange(1, 3) for _ in range(4)})


for _ in range(8):
    x, y, x2, y2 = rnd(), rnd(), rnd(), rnd()
    lhs = psi0(gmul(x, x2, mmul), gmul(y, y2, mmul))
    rhs = p4mul(psi0(x, y), psi0(x2, y2))
    check("B: Psi_0 multiplicative on random tensors", lhs == rhs)
    check("B: flip [wbar] Psi_0(x (x) y) [wbar] = Psi_0(y (x) x)", p4mul(p4mul(W4, psi0(x, y)), W4) == psi0(y, x))
H4 = {proj(h2): 1}
check("B: H conjugates wbar to dbar at depth 2", p4mul(p4mul(H4, W4), H4) == D4)

# ---------- Part C ----------
# Basis vectors: (sector, n) with sector in {'++','+-','-+','--'} (first sign: wbar, second: dbar).
SECT = ['++', '+-', '-+', '--']


def vec_add(a, b, s=1):
    out = dict(a)
    for k, val in b.items():
        out[k] = (out.get(k, 0) + s * val) % P
    return {k: val for k, val in out.items() if val}


class Op:
    def __init__(self, fn):
        self.fn = fn

    def __call__(self, vec):
        out = {}
        for k, val in vec.items():
            out = vec_add(out, {kk: (vv * val) % P for kk, vv in self.fn(k).items()})
        return out

    def __mul__(self, other):
        return Op(lambda k: self(other.fn(k)))

    def __add__(self, other):
        return Op(lambda k: vec_add(self.fn(k), other.fn(k)))

    def scale(self, c):
        return Op(lambda k: {kk: (c * vv) % P for kk, vv in self.fn(k).items()})


def qop(sect):
    return Op(lambda k: {k: 1} if k[0] == sect else {})


Wop = Op(lambda k: {k: 1 if k[0][0] == '+' else 2})
Dop = Op(lambda k: {k: 1 if k[0][1] == '+' else 2})
Hmap = {'++': '++', '--': '--', '+-': '-+', '-+': '+-'}
Hop = Op(lambda k: {(Hmap[k[0]], k[1]): 1})
Iop = Op(lambda k: {k: 1})
fop = qop('+-') + qop('--')
ewop = qop('++') + qop('+-')


# enumeration of the f-sectors: kappa(m) = ('+-', m//2) if m even, ('--', m//2) if m odd
def kappa(m):
    return ('+-', m // 2) if m % 2 == 0 else ('--', m // 2)


def iota(k):
    return 2 * k[1] if k[0] == '+-' else 2 * k[1] + 1


def in_f(k):
    return k[0] in ('+-', '--')


X1 = Op(lambda k: {kappa(2 * iota(k)): 1} if in_f(k) else {})
X2 = Op(lambda k: {kappa(2 * iota(k) + 1): 1} if in_f(k) else {})
Y1 = Op(lambda k: ({kappa(iota(k) // 2): 1} if iota(k) % 2 == 0 else {}) if in_f(k) else {})
Y2 = Op(lambda k: ({kappa(iota(k) // 2): 1} if iota(k) % 2 == 1 else {}) if in_f(k) else {})
Xop = Op(lambda k: {('+-', iota(k)): 1, ('--', iota(k)): 1} if in_f(k) else {})
Yop = Op(lambda k: {kappa(k[1]): 2} if in_f(k) else {})

basis = [(s, n) for s in SECT for n in range(40)]


def same(A, B):
    return all(A({k: 1}) == B({k: 1}) for k in basis)


check("C: H W H = D", same(Hop * Wop * Hop, Dop))
check("C: W D = D W", same(Wop * Dop, Dop * Wop))
check("C: 2 e_w = 1 + W", same(ewop.scale(2), Iop + Wop))
check("C: f = 2(1 - D)", same(fop, (Iop + Dop.scale(2)).scale(2)))
for nm, op in [('X1', X1), ('X2', X2), ('Y1', Y1), ('Y2', Y2), ('X', Xop), ('Y', Yop)]:
    check("C: %s in f A f" % nm, same(fop * op * fop, op))
check("C: Y1 X1 = f", same(Y1 * X1, fop))
check("C: Y2 X2 = f", same(Y2 * X2, fop))
check("C: Y1 X2 = 0", same(Y1 * X2, Op(lambda k: {})))
check("C: Y2 X1 = 0", same(Y2 * X1, Op(lambda k: {})))
check("C: Y X = f", same(Yop * Xop, fop))
check("C: Y W X = 0", same(Yop * Wop * Xop, Op(lambda k: {})))

qpp, qmp = qop('++'), qop('-+')
b_op = qpp + ewop * Xop * (X1 * Hop * qmp + X2)
c_op = qpp + ((qmp * Hop * Y1 + Y2) * Yop * ewop).scale(2)
check("C: e_w b = b", same(ewop * b_op, b_op))
check("C: c e_w = c", same(c_op * ewop, c_op))
check("C: c b = 1", same(c_op * b_op, Iop))
check("C: c e_w b = 1", same(c_op * ewop * b_op, Iop))
print("ALL CHECKS PASSED")
