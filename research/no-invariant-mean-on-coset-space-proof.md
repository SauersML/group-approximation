---
rg: 2
id: no-invariant-mean-on-coset-space-proof
kind: route
title: Day's trick plus property (T) on the quasi-regular representation
target: no-invariant-mean-on-coset-space
requires: []
artifacts:
  - notes/TRUE_CHARGE_EXTENSION_NEEDS_COAMENABILITY.md
---

# Day's trick plus property (T) on the quasi-regular representation

Direct establishment; the argument is Proposition 1 of the artifact and is four
lines. A `G`-invariant mean on `ℓ^∞(G/Γ)` yields, by weak-\*-to-norm convexity
(Day), finitely supported probability densities `f_i` with
`‖g·f_i − f_i‖₁ → 0`; the square roots `ξ_i = f_i^{1/2}` are unit vectors of
`ℓ²(G/Γ)` with `‖g·ξ_i − ξ_i‖₂² ≤ ‖g·f_i − f_i‖₁` by `|√a − √b|² ≤ |a − b|`;
property (T) converts almost invariant vectors into a nonzero invariant one;
transitivity makes it a constant function, and a nonzero constant is square
summable only when `G/Γ` is finite. `requires: []` is a proof commitment.

Nothing external is used beyond property (T) of `G`, which comes from Kun–Thom
Theorem E through `wreath-not-sofic`'s citation but is also standard for these
elementary groups (universal lattice plus closure of (T) under extensions, as
recorded in `notes/FALSE_POSITIVE_CORE_IS_SOFIC.md`). The claim is stated for a
general Kazhdan pair of infinite index, so it is reusable outside this subtree.
