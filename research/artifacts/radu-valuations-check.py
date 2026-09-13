# Exact tr^2/det in F = Q(w) for products of pairs of letters, and their 2-adic valuations at the
# two primes above 2: q (w with v_2(w) = -1, the horizontal tree) and q' (v_2(w) = +1).
# An element of PGL_2(Q_2) is hyperbolic on the tree iff v(tr^2/det) < 0.
from fractions import Fraction as Fr
exec(open("radu-quaternion-invariants-check.py").read().split('print("DONE")')[0])

inv_m1sq = mul(inv_m1, inv_m1)
detinv = {"a": neg(inv_m), "b": neg(inv_m), "x": const(-1), "z": const(-1),
          "y": mul(const(Fr(1, 4)), inv_m1sq),
          "c": neg(mul(const(Fr(1, 16)), mul(inv_m, mul(inv_m1sq, inv_m1sq))))}
L6 = {"a": a, "b": b, "c": c, "x": x, "y": y, "z": z}

PREC = 80
MOD = 1 << PREC
def root_w(vw):
    # 2w^2 - w - 2 = 0. v(w) = 1: w = 2u, 4u^2 - u - 1 = 0 (simple root mod 2, u odd).
    # v(w) = -1: w = u/2, u^2 - u - 4 = 0 (simple root mod 2, u odd).
    if vw == 1:
        G = lambda u: 4 * u * u - u - 1
        u = 1
        for k in range(1, PREC + 2):
            if G(u) % (1 << (k + 1)):
                u += 1 << k
        return ("w=2u", u % MOD)
    G = lambda u: u * u - u - 4
    u = 1
    for k in range(1, PREC + 2):
        if G(u) % (1 << (k + 1)):
            u += 1 << k
    return ("w=u/2", u % MOD)

def v2_frac(q):
    if q == 0:
        return 10**9
    n, d = q.numerator, q.denominator
    v = 0
    while n % 2 == 0:
        n //= 2; v += 1
    while d % 2 == 0:
        d //= 2; v -= 1
    return v

def val_at(p, vw):
    # valuation of alpha + beta w at the chosen 2-adic root
    alpha, beta = p
    kind, u = root_w(vw)
    # write alpha = A/2^e, beta = Bt/2^e with integers; w = 2u or u/2
    e = 0
    for q in (alpha, beta):
        e = max(e, -v2_frac(q) if q != 0 else 0)
    e += 2
    def scaled(q):
        n, d = q.numerator, q.denominator
        k = 0
        while d % 2 == 0:
            d //= 2; k += 1
        return (n * (1 << (e - k)) * pow(d, -1, MOD)) % MOD
    A = scaled(alpha)
    Bt = scaled(beta)
    if kind == "w=2u":
        val = (A + Bt * 2 * u) % MOD
        shift = e
    else:
        val = (2 * A + Bt * u) % MOD
        shift = e + 1
    if val == 0:
        return ">= %d" % (PREC - shift)
    v = 0
    while val % 2 == 0:
        val //= 2; v += 1
    return v - shift

words = ["ab", "bc", "ca", "xy", "yz", "zx", "ax", "ay", "az", "bx", "by", "bz", "cx", "cy", "cz", "xyz", "abc", "axby"]
for wd in words:
    M = [[const(1), {}], [{}, const(1)]]
    dinv = const(1)
    for ch in wd:
        M = mmul(M, L6[ch])
        dinv = mul(dinv, detinv[ch])
    t = mul(mul(tr(M), tr(M)), dinv)
    p = in_F(t)
    if p is None:
        print(wd, "tr^2/det not in F")
        continue
    print("%-5s tr^2/det = %s + %s w ; v at q (horizontal): %s ; v at q': %s" % (wd, p[0], p[1], val_at(p, -1), val_at(p, 1)))
print("DONE3")
