---
rg: 2
id: modular-radical-lift-failure-proof
kind: route
title: Grade by lamp degree and run the geometric series
target: modular-radical-does-not-lift-direct-finiteness
requires: [infranormal-nonnormal-has-infinite-compression-orbit]
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

The general statement is proved outright; the single premise is used only to
instantiate it at the Kun--Thom pairs, where the element with an infinite
orbit on `G/Gamma` is not part of the hypotheses of Kun--Thom's Theorem A and
has to be produced.

**The grading.**  Write `a_x` for the lamp generator at `x in X` and
`y_x = a_x - 1`.  In characteristic `p`, `y_x^p = a_x^p - 1 = 0`, so

    k[N] = tensor_(x in X) k[y_x]/(y_x^p)

with basis the monomials `y_S = prod y_x^(e_x)`, `0 <= e_x < p`, finite
support.  Grading by total `y`-degree makes `k[N]` a graded algebra, and `G`
permutes the `y_x`, hence preserves the degree.  So

    k[W] = directSum_(d >= 0) k[W]_d,     k[W]_0 = k[G],

is graded, `omega(k[N])` is the span of the `y_S` with `S` nonempty, it is
`G`-invariant, and `omega(k[N])k[W]` is the two-sided ideal it generates,
with quotient `k[G]`.

**The witness.**  Let `x` lie on an infinite `<g>`-orbit and put `u = y_x g`,
homogeneous of degree one and inside `omega(k[N])k[W]`.  Then

    u^d = y_x y_(gx) y_(g^2 x) ... y_(g^(d-1) x) g^d != 0

for every `d >= 1`: the sites are pairwise distinct, so this is a basis
monomial (each exponent `1 < p` or, for `p = 2`, exactly the squarefree case)
times a group element.

**No inverse.**  Suppose `(1-u)v = 1` with `v = sum_(d <= D) v_d` in graded
components.  Degree `0` gives `v_0 = 1`; degree `d >= 1` gives
`v_d - u v_(d-1) = 0`, so `v_d = u^d` by induction, and `u^d != 0` for all
`d`.  Then `v` has nonzero components in infinitely many degrees, which no
element of `k[W]` has.  So `1 - u` has no right inverse, hence is not
invertible.  An element of `J(k[W])` always has `1 - u` invertible, so
`u not in J(k[W])`, while `u in omega(k[N])k[W]`.  `[]`

**Instantiation.**  For a Kun--Thom pair, `X = G/Gamma` and
`infranormal-nonnormal-has-infinite-compression-orbit` gives `g in P_Gamma`
with `g^k not in Gamma` for all `k >= 1`, so the `<g>`-orbit of the base point
is infinite and the witness exists.  The lamp is `Z/2Z`, so the relevant
characteristic is two.
