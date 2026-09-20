"""Swap toy: an abstract D-shaped Laplacian system where Novikov surjectivity
holds at depth 1 but level-0 surjectivity fails, for both chi and -chi.

G = Z^2 x| Z, H = <a,b> = Z^2, t a t^-1 = b, t b t^-1 = a (theta = swap).
chi = t-exponent.  sigma_1 = 1+a = S_2(a), sigma_2 = 1+b+b^2 = S_3(b).
p_1 = ab*t, p_2 = t (level 1).  g_rho = sigma_rho (p_rho - 1).
System: the left ideal sum_rho N g_rho of the Novikov ring N = N_chi.

Checks
 (A) L_0 not onto: J_0 = (1+a, 1+b+b^2) != Z[H]  (F_7 point a=-1, b=2).
 (B) depth-1 certificate for chi: lambda_rho = mu_rho + nu_rho t^-1 with
     sum lambda_rho g_rho = 1 + M, M supported at level 1 (so 1+M is a unit of N).
 (C) same for -chi, with generators t^-1 g_rho, whose level-0 ideal is theta(J_0),
     also not onto (F_7 point b=-1, a=2).
 (D) theta-stable hull T(J_0) = J_0 + theta(J_0) = Z[H]: the ring obstruction vanishes.
 (E) the Artin constraint fails: conj by p_1 moves a^2 (and every a^n, n != 0).
Elements of Z[G]: dict {(i, j, n): coeff} for a^i b^j t^n.
"""
import sympy as sp

A, B = sp.symbols("a b")


def th(i, j, n):
    return (j, i) if n % 2 else (i, j)


def mul(x, y):
    out = {}
    for (i, j, n), c in x.items():
        for (k, l, m), d in y.items():
            k2, l2 = th(k, l, n)
            key = (i + k2, j + l2, n + m)
            out[key] = out.get(key, 0) + c * d
    return {k: v for k, v in out.items() if v}


def add(*xs):
    out = {}
    for x in xs:
        for k, v in x.items():
            out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}


def scal(c, x):
    return {k: c * v for k, v in x.items() if c * v}


def from_poly(p, n=0):
    """sympy polynomial in a, b -> element of Z[H] t^n."""
    out = {}
    for (i, j), c in sp.Poly(sp.expand(p), A, B).terms():
        out[(int(i), int(j), n)] = int(c)
    return {k: v for k, v in out.items() if v}


def T(n):
    return {(0, 0, n): 1}


ONE = T(0)
sig1, sig2 = 1 + A, 1 + B + B**2
p1 = mul(from_poly(A * B), T(1))
p2 = T(1)
g1 = mul(from_poly(sig1), add(p1, scal(-1, ONE)))
g2 = mul(from_poly(sig2), add(p2, scal(-1, ONE)))


def levels(x):
    return sorted({k[2] for k in x})


def split_ideal(E, s1, v1, s2, v2):
    """E = q1*s1 + q2*s2: divide by s2 (monic in v2), then the remainder by s1 (in v1)."""
    q2, r = sp.div(sp.expand(E), s2, v2)
    q1, r1 = sp.div(sp.expand(r), s1, v1)
    assert sp.expand(r1) == 0, r1
    assert sp.expand(q1 * s1 + q2 * s2 - E) == 0
    return sp.expand(q1), sp.expand(q2)


def report(tag, x):
    print(tag, "levels", levels(x), "level-0 part", {k: v for k, v in x.items() if k[2] == 0})


def point_kills(polys, pt, p):
    return all(int(sp.expand(q).subs(pt)) % p == 0 for q in polys)


def flip(x):
    """re-index by -chi level = minus the t-exponent"""
    return {(i, j, -n): v for (i, j, n), v in x.items()}


def certify(tag, gens, lev, lam_neg, s1, v1, s2, v2, unit1, sgn):
    """gens: two generators, lev: level function (identity or flip).
    lam_neg: the depth-1 coefficients nu_rho (already placed one level down).
    Level-0 part of gens[k] is sgn[k] * s_k * unit1^{-1 if k==0}.  Solves for mu, checks."""
    print(f"== {tag} ==")
    for k, g in enumerate(gens, 1):
        report(f"g{k}", lev(g))
    part = lev(add(*[mul(l, g) for l, g in zip(lam_neg, gens)]))
    below = {k: v for k, v in part.items() if k[2] < 0}
    print("nu-part below level 0 (must be empty):", below)
    assert not below
    l0 = {k: v for k, v in part.items() if k[2] == 0}
    E = sp.expand(1 - sum(v * A**i * B**j for (i, j, _), v in l0.items()))
    q1, q2 = split_ideal(E, s1, v1, s2, v2)
    mu1 = mul(scal(sgn[0], from_poly(q1)), unit1)
    mu2 = scal(sgn[1], from_poly(q2))
    total = lev(add(*[mul(l, g) for l, g in zip(lam_neg, gens)], mul(mu1, gens[0]), mul(mu2, gens[1])))
    lv = levels(total)
    t0 = {k: v for k, v in total.items() if k[2] == 0}
    print("mu1 =", sgn[0], "*", unit1, "*", q1)
    print("mu2 =", sgn[1], "*", q2)
    print("sum lambda g: levels", lv, " level-0 part", t0)
    assert lv[0] == 0 and t0 == {(0, 0, 0): 1} and lv[-1] == 1
    print(f"{tag}: sum lambda_rho g_rho = 1 + M with M at level 1, 1+M a unit -> Novikov onto at depth 1")


if __name__ == "__main__":
    ident = lambda x: x
    # (A)
    assert point_kills([sig1, sig2], {A: -1, B: 2}, 7)
    print("(A) a=-1, b=2 over F_7 kills 1+a and 1+b+b^2: J_0 != Z[H], L_0(chi) not onto")
    # (B) chi: level-0 part of g_rho is -sigma_rho; nu_1 = c(1+a+a^2), nu_2 = -c(1+b), c = -b^2
    c = -B**2
    lam = [mul(from_poly(c * (1 + A + A**2)), T(-1)), mul(from_poly(-c * (1 + B)), T(-1))]
    certify("chi", [g1, g2], ident, lam, sig1, A, sig2, B, ONE, [-1, -1])
    # (C) -chi: generators t^-1 g_rho, level-0 parts (1+b)ab and 1+a+a^2
    h1, h2 = mul(T(-1), g1), mul(T(-1), g2)
    th1, th2 = 1 + B, 1 + A + A**2
    assert point_kills([th1, th2], {A: 2, B: -1}, 7)
    print("(C) b=-1, a=2 over F_7 kills 1+b and 1+a+a^2: theta(J_0) != Z[H], L_0(-chi) not onto")
    cp = -A**2
    lam2 = [mul(from_poly(cp * (1 + B + B**2)), T(1)), mul(from_poly(-cp * (1 + A) * A * B), T(1))]
    certify("-chi", [h1, h2], flip, lam2, th1, B, th2, A, {(-1, -1, 0): 1}, [1, 1])
    # (D) theta-stable two-sided hull
    assert sp.expand((1 + B + B**2) - B * (1 + B) - 1) == 0
    print("(D) 1 = (1+b+b^2) - b(1+b) lies in J_0 + theta(J_0): T(J_0) = Z[H]; ring obstruction vanishes")
    # (E) Artin constraint [p_1, a^2] = 1 fails
    x = {(2, 0, 0): 1}
    p1inv = mul(T(-1), {(-1, -1, 0): 1})
    assert mul(p1, p1inv) == ONE
    conj = mul(mul(p1, x), p1inv)
    print("(E) p_1 a^2 p_1^-1 =", conj, "!= a^2: the Artin constraint [p, x^k] = 1 is violated")
    assert conj != x
    print("ALL CHECKS PASSED")
