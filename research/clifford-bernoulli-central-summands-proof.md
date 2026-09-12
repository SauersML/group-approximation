---
rg: 2
id: clifford-bernoulli-central-summands-proof
kind: route
title: Cut the Clifford lamp group algebra by the central sign projection
target: clifford-bernoulli-central-summands
requires: []
artifacts:
  - notes/TRUE_CLIFFORD_LAMP_CENTRAL_SUMMANDS.md
---

# Cut the Clifford lamp group algebra by the central sign projection

Direct establishment; the complete argument is the Proposition of the cited
note. `requires: []` is a proof commitment.

Every element of `C(X)` is `z^e c_(x₁)···c_(x_k)` for a finite subset and
`e ∈ {0,1}`, so `C(X)` is a central `ℤ/2`-extension of `⊕_X ℤ/2` and
`L(C(X))` splits along `p_± = (1 ± z)/2`. On `p_+` the relation `z = 1` makes
the `c_x` commuting self-adjoint unitaries, so the corner is
`L(⊕_X ℤ/2) = L^∞({±1}^X)` with the product measure. On `p_−` the relation
`z = −1` makes them anticommuting with `tr(c_(x₁)···c_(x_k)) = 0` for `k ≥ 1`,
which is the tracial CAR algebra `Cl(X)`. Both projections are `G`-fixed
because `G` fixes `z`, so the crossed product splits along them.

For the consequence: compressions of Connes-embeddable tracial algebras are
Connes embeddable (`pMp ⊆ pR^ω p ≅ R^ω`), and a direct sum of two of them is
Connes embeddable (place them in complementary corners of `R^ω` with the right
traces). Hence Connes embeddability of `L(W̃)` is exactly the conjunction of
Connes embeddability of the two summands.
