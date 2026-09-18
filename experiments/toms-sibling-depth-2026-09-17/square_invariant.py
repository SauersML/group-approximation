"""Square invariant for two sibling swap nodes in Toms's tower.

X_g = { psd Q in M_k : g+1 <= rank Q <= g+2 }, covered by
U = {lambda_(g+1) > lambda_(g+2)} and V = {rank Q = g+2}.
On U cap V: W = span of the top g+1 eigenvectors, y = c_1(range Q / W).
omega = c_1(W) * y^2 in H^6(U cap V); delta(omega) in H^7(X_g).

The model loop on the boundary of the square visits, in cyclic order,
G + L_a (a = 1..4), passing through G + L_a + L_(a+1) on the arcs.
Mayer-Vietoris gives the pulled-back class in H^1(S^1) x H^6(Y):
  V = sum_a [ w(G+L_a, e_(a+1)) - w(G+L_a, e_(a-1)) ],
where e_a = c_1(L_a). This script
  1. evaluates V for Toms-type twists,
  2. checks that classes pulled back from U (functions of c(W)) and from V
     (functions of c(W) (1 + y)) give zero, so V is well defined,
  3. checks the dependence on alpha + beta.
Run: python3 square_invariant.py  (writes results.json next to it).
"""
import itertools
import json
import os

import sympy as sp

u1, u2, al, be = sp.symbols("u1 u2 alpha beta")
g1, g2, g3 = sp.symbols("g1 g2 g3")  # Chern classes of the common bundle G

# cyclic order: bottom L_2^(2), right L_1^(1), top L_1^(2), left L_2^(1)
E = [be * u2, al * u1, al * u2, be * u1]


def trunc(expr, j):
    """Reduce in H^*(CP^j x CP^j): kill u1^(j+1), u2^(j+1)."""
    p = sp.Poly(sp.expand(expr), u1, u2)
    out = 0
    for (a, b), c in p.terms():
        if a <= j and b <= j:
            out += c * u1**a * u2**b
    return sp.expand(out)


def chern_W(a):
    """Total Chern class of W = G + L_a, as a list [c1, c2, c3]."""
    cG = [1, g1, g2, g3]
    cL = [1, E[a]]
    tot = [0, 0, 0, 0]
    for i in range(4):
        for k in range(2):
            if i + k <= 3:
                tot[i + k] += cG[i] * cL[k]
    return [sp.expand(t) for t in tot[1:]]


def loop_value(w):
    """w(c1, c2, c3, y): a class on U cap V. Returns V in H^6(Y)[g]."""
    val = 0
    for a in range(4):
        c = chern_W(a)
        val += w(*c, E[(a + 1) % 4]) - w(*c, E[(a - 1) % 4])
    return sp.expand(val)


def degree6_monomials_from_U():
    # functions of c(W) only, total degree 6 (c1 deg 2, c2 deg 4, c3 deg 6)
    return [lambda c1, c2, c3, y: c1**3, lambda c1, c2, c3, y: c1 * c2,
            lambda c1, c2, c3, y: c3]


def degree6_monomials_from_V():
    # functions of c(W)(1+y): c1' = c1 + y, c2' = c2 + c1 y, c3' = c3 + c2 y
    def cp(c1, c2, c3, y):
        return c1 + y, c2 + c1 * y, c3 + c2 * y
    return [lambda c1, c2, c3, y: cp(c1, c2, c3, y)[0] ** 3,
            lambda c1, c2, c3, y: cp(c1, c2, c3, y)[0] * cp(c1, c2, c3, y)[1],
            lambda c1, c2, c3, y: cp(c1, c2, c3, y)[2]]


def main():
    res = {}
    omega = lambda c1, c2, c3, y: c1 * y**2
    V = sp.factor(loop_value(omega))
    res["V_general"] = str(V)
    res["V_expected"] = str(sp.factor((al - be) ** 2 * (al + be) * (u1 * u2**2 - u1**2 * u2)))
    res["V_matches_expected"] = bool(sp.simplify(
        loop_value(omega) - (al - be) ** 2 * (al + be) * (u1 * u2**2 - u1**2 * u2)) == 0)
    res["V_independent_of_G"] = not any(s in V.free_symbols for s in (g1, g2, g3))
    res["U_classes_vanish"] = all(loop_value(f) == 0 for f in degree6_monomials_from_U())
    res["V_classes_vanish"] = all(loop_value(f) == 0 for f in degree6_monomials_from_V())
    # other degree-6 classes on U cap V: every monomial c1^a c2^b c3^c y^d
    others = {}
    for (a, b, c, d) in itertools.product(range(4), range(2), range(2), range(4)):
        if 2 * a + 4 * b + 6 * c + 2 * d == 6:
            f = lambda c1, c2, c3, y, a=a, b=b, c=c, d=d: c1**a * c2**b * c3**c * y**d
            others[f"c1^{a} c2^{b} c3^{c} y^{d}"] = str(sp.factor(loop_value(f)))
    res["all_degree6_monomials"] = others
    tw = {}
    for name, (A, B) in {"L1=O(-2),L2=O(-1)": (-2, -1), "O(2),O(1)": (2, 1),
                         "O(1),O(-1)": (1, -1), "O(1),O(0)": (1, 0),
                         "untwisted": (0, 0)}.items():
        val = sp.expand(V.subs({al: A, be: B}))
        tw[name] = {j: str(trunc(val, j)) for j in (1, 2, 3)}
    res["twists"] = tw
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")
    with open(out, "w") as fh:
        json.dump(res, fh, indent=2)
    print(json.dumps(res, indent=2))


if __name__ == "__main__":
    main()
