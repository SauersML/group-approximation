---
rg: 2
id: top-cell-commutator-class-is-product-of-adjoint-j-invariants
kind: claim
title: The top-cell component of a nested unitary commutator seed class is exactly a product of adjoint J-invariants of the letters times the top-cell class of the innermost bracket
distinct_from:
  rank-two-trapping-blind-to-depth-four-brackets: That computes the whole stable fivefold commutator of U(2) through its sphere splitting; this is an exact product formula on one summand, the top cell, valid for every compact Lie group and every seed manifold.
  nested-commutators-pull-ko-of-unitary-groups-into-eta-powers: That bounds KO-pullbacks by powers of eta; this gives the exact value of the top-cell component in any ring spectrum.
---

Let H be a compact connected Lie group, G ⊂ H a closed connected normal subgroup of
dimension n (for instance SU(p) ⊂ U(p)), and q: G -> S^n the collapse onto a
small Ad(H)-invariant ball around 1. Then Sigma^∞ q is a stable retraction
onto the top-cell summand of Sigma^∞ G. For a based map g: X -> H let
u_g in pi^0_s(X_+) be the stable class of (x, v) -> Ad_{g(x)} v on
X_+ ∧ S^n, and J_g = u_g − 1 in pi~^0_s(X). Equivalently J_g = J_Ad o
Sigma^∞ g, where J_Ad: Sigma^∞ H -> S^0 is the stable adjoint of
H -> SO(n) -> SG, h -> J(Ad_h) − 1.

(a) *Exact formula.* Let Z be a suspension, k: Z -> G based, and
    g_i: X_i -> H based, i = 2, ..., c − 1. Restricted to
    X_{c−1} ∧ ... ∧ X_2 ∧ Z,

        Sigma^∞ q o [g_{c−1}, [..., [g_2, k]...]]
            = J_{g_{c−1}} ∧ ... ∧ J_{g_2} ∧ (Sigma^∞ q o k).

(b) *Seed classes.* Let E be a ring spectrum, X_2, ..., X_{c−1}, Y closed
    E-oriented manifolds, j >= 1, g_1: S^j -> H, h: Y -> G, and
    f = [g_{c−1}, [..., [g_2, [g_1, h]]...]] on
    M = X_{c−1} x ... x X_2 x S^j x Y. Then the top-cell component of
    [M, f]_red in E~_{dim M}(G) is

        ± x_{c−1} ··· x_2 · beta   in pi_{dim M − n} E,

    where x_i = (J_{g_i})_*[X_i]_E in pi_{dim X_i} E, and beta is the
    top-cell component of the reduced class of [g_1, h] on S^j x Y.
(c) *Ideal and cap.* Every x_i lies in I_{H,E} = (J_Ad)_*(E~_*(H)), an
    ideal of E_*. J_Ad and beta are rationally trivial, so all factors are
    torsion. Top-cell detection of a (c−1)-fold bracket needs a nonzero
    product of c − 1 torsion elements of E_*, c − 2 of them in I_{H,E}.
(d) *Checks.* For H = U(2), G = SU(2) = S^3, q = id: J_Ad sends the circle
    class to eta and the 3-cell to 2 nu, since Ad of SU(2) is the 3-dimensional
    representation with lambda = ±2. So [omega, omega] is 2 nu, and the
    fourfold commutator of three circle letters around [alpha, omega] is
    eta^3, as in simple-ah-algebra-with-class-four-component-group. Also
    I_{U(2),E} ⊆ (eta, 2 nu), whose fourth power vanishes in pi_*^s, in line
    with rank-two-trapping-blind-to-depth-four-brackets.

With lambda-mod-m-bordism-splits-as-string-bordism-in-a-range, a nonzero
product in (b) for E = MString and G = SU(p) gives a simple AH algebra with
a nonzero c-fold commutator. So the top-cell route to class five asks for
x_4·x_3·x_2·beta != 0 in pi_*MString with x_i in I_{U(p),MString}.

Proof: top-cell-adjoint-j-product-proof. Complete argument. Not
independently reviewed.
