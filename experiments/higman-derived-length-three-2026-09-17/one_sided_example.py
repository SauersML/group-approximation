"""Calibration script for higman-one-sided-span-bound-fails-at-derived-length-three.

Group: G = L x| G_1 with G_1 = T x| H, H = BS(1,2) = <a,b>, T = Ind_<b>^H Q (b acts by 1/2),
L = Q[G_1] / Q[G_1] x, x = 1 - b - b c.  Generators a' = (0,a), b' = (0,b), c' = ([1], c).
We check numerically (t = 1.7, 60 digits) that the functional
    f(tau, h) = t^lambda(tau) F(h)
kills Q[G_1] x, is left A_1'-invariant, is c-equivariant, gives a homomorphism A' -> C killing A'',
and sends z' = [c', a'] and its c'-conjugates to t^{-1}, t^{-2}, ...  (so the Y-span of zbar in
A'/A'' (x) Q is infinite-dimensional).
"""
from fractions import Fraction as Fr
import math, random
import mpmath as mp

mp.mp.dps = 60
TT = mp.mpf("1.7")
random.seed(1)

# ---------- H = BS(1,2) as affine maps x -> 2^p x + s ----------
def hmul(h, k):
    p, s = h; q, r = k
    return (p + q, Fr(2) ** p * r + s)

def hinv(h):
    p, s = h
    return (-p, -s / Fr(2) ** p)

ID = (0, Fr(0))
A = (-1, Fr(0))
B = (0, Fr(1))

def hpow(h, n):
    out = ID
    base = h if n >= 0 else hinv(h)
    for _ in range(abs(n)):
        out = hmul(out, base)
    return out

def coset(h):
    """h = rep o b^n with rep = (p, s0), 0 <= s0 < 2^p."""
    p, s = h
    n = math.floor(s / Fr(2) ** p)
    return (p, s - Fr(2) ** p * n), n

# ---------- T = Ind module, stored as {rep: coeff} ----------
def tnorm(d):
    return frozenset((k, v) for k, v in d.items() if v != 0)

def tact(h, tau):
    out = {}
    for rep, q in tau:
        r2, n = coset(hmul(h, rep))
        out[r2] = out.get(r2, 0) + q / Fr(2) ** n   # rep b^n (x) q = rep (x) q/2^n
    return tnorm(out)

def tadd(t1, t2):
    out = dict(t1)
    for k, v in t2:
        out[k] = out.get(k, 0) + v
    return tnorm(out)

def lam(tau):
    q = sum((v for _, v in tau), Fr(0))
    return mp.mpf(q.numerator) / q.denominator

# ---------- G_1 = T x| H ----------
def gmul(g, k):
    return (tadd(g[0], tact(g[1], k[0])), hmul(g[1], k[1]))

def ginv(g):
    hi = hinv(g[1])
    return (tnorm({k: -v for k, v in tact(hi, g[0])}), hi)

G_ID = (frozenset(), ID)
ga, gb = (frozenset(), A), (frozenset(), B)
gc = (tnorm({(0, Fr(0)): Fr(1)}), ID)

def gpow(g, n):
    out = G_ID
    base = g if n >= 0 else ginv(g)
    for _ in range(abs(n)):
        out = gmul(out, base)
    return out

def conj(x, y):  # x^y = y^-1 x y
    return gmul(gmul(ginv(y), x), y)

# ---------- the functional ----------
def Frep(rep):
    if rep == (0, Fr(0)):
        return mp.mpf(0)
    if rep == (1, Fr(0)):   # a^-1
        return mp.mpf(1)
    return mp.mpf(1 + (hash(rep) % 5))

def Fh(h):
    rep, n = coset(h)
    val = Frep(rep)
    if n >= 0:
        for j in range(n):
            val /= (1 + TT ** (mp.mpf(2) ** (-j) / 2))
    else:
        for j in range(n, 0):
            val *= (1 + TT ** (mp.mpf(2) ** (-j) / 2))
    return val

def f_g(g):
    return TT ** lam(g[0]) * Fh(g[1])

def f_L(r):  # r = {g: coeff}
    return sum(((mp.mpf(Fr(v).numerator) / Fr(v).denominator) * f_g(g) for g, v in r.items()), mp.mpf(0))

# ---------- L x| G_1 ----------
def lact(g, r):
    out = {}
    for k, v in r.items():
        gk = gmul(g, k)
        out[gk] = out.get(gk, 0) + v
    return out

def ladd(r, s, sign=1):
    out = dict(r)
    for k, v in s.items():
        out[k] = out.get(k, 0) + sign * v
    return {k: v for k, v in out.items() if v != 0}

def emul(x, y):
    return (ladd(x[0], lact(x[1], y[0])), gmul(x[1], y[1]))

def einv(x):
    gi = ginv(x[1])
    return ({k: -v for k, v in lact(gi, x[0]).items()}, gi)

def ecomm(x, y):
    return emul(emul(einv(x), einv(y)), emul(x, y))

def econj(x, y):
    return emul(emul(einv(y), x), y)

Ea, Eb = ({}, ga), ({}, gb)
Ec = ({G_ID: 1}, gc)

def close(u, v, tol=mp.mpf("1e-40")):
    return abs(u - v) <= tol * (1 + abs(u) + abs(v))

def rand_g(steps=6):
    g = G_ID
    for _ in range(steps):
        g = gmul(g, random.choice([ga, gb, gc, ginv(ga), ginv(gb), ginv(gc)]))
    return g

def main():
    out = []
    # relations of H and G_1
    assert hmul(hmul(hinv(A), B), A) == hmul(B, B)
    assert conj(gb, ga) == gmul(gb, gb)
    assert conj(gc, gb) == gmul(gc, gc)
    out.append("relations b^a=b^2, c^b=c^2 hold in G_1")
    # relation c'^b' = c'^2 in L x| G_1 holds modulo Q[G_1]x: translation difference is b^-1 x
    lhs, rhs = econj(Ec, Eb), emul(Ec, Ec)
    assert lhs[1] == rhs[1]
    diff = ladd(lhs[0], rhs[0], -1)
    assert close(f_L(diff), 0)
    out.append("c'^b' and c'^2 agree in G_1 and their translation parts differ by b^-1 x (f-value 0)")
    # f kills g x
    for _ in range(40):
        g = rand_g(8)
        gbx, gbcx = gmul(g, gb), gmul(gmul(g, gb), gc)
        assert close(f_g(g), f_g(gbx) + f_g(gbcx))
    out.append("f(g) = f(gb) + f(gbc) on 40 random g")
    # A_1' invariance and c-equivariance
    z1 = gmul(ginv(gc), conj(gc, ga))  # [c,a]
    for _ in range(40):
        g = rand_g(8)
        u = conj(z1, gmul(gpow(ga, random.randint(-3, 3)), gpow(gc, random.randint(-2, 2))))
        assert close(f_g(gmul(u, g)), f_g(g))
        assert close(f_g(gmul(gc, g)), TT * f_g(g))
    out.append("f(u g) = f(g) for u in A_1', f(c g) = t f(g), 40 random g")
    # z' and Y-span
    zp = ecomm(Ec, Ea)
    vals = []
    for j in range(5):
        v = f_L(econj(zp, einv(gpow_E(Ec, j)))[0]) if j else f_L(zp[0])
        vals.append(v)
    for j, v in enumerate(vals):
        assert close(v, TT ** (-1 + j)), (j, v)
    out.append("f(pi(z'^(c'^-j))) = t^(j-1) for j=0..4 (nonzero, t-scaled): Y-span infinite")
    # homomorphism on A' and vanishing on A''
    elems = [zp]
    for _ in range(6):
        w = random.choice(elems)
        y = random.choice([Ea, Ec, einv(Ea), einv(Ec)])
        elems.append(econj(w, y))
    for _ in range(15):
        x, y = random.choice(elems), random.choice(elems)
        assert close(f_L(emul(x, y)[0]), f_L(x[0]) + f_L(y[0]))
        assert close(f_L(ecomm(x, y)[0]), 0)
    out.append("f o pi is additive on A' and kills commutators of A' elements (15 random pairs)")
    print("\n".join(out))

def gpow_E(x, n):
    out = ({}, G_ID)
    for _ in range(n):
        out = emul(out, x)
    return out

if __name__ == "__main__":
    main()
