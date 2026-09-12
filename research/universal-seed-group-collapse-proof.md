---
rg: 2
id: universal-seed-group-collapse-proof
kind: route
title: Apply the rank-four theorem to the seed and transfer by normal generation
target: universal-seed-group-collapses-elementary-groups
requires:
  - universal-split-pair-seed-ring
  - full-complementary-idempotent-elementary-full-mf-radical
  - elementary-rank-descent-to-two
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
---

## Why sufficient

`C` is countable, unital, and satisfies `t_0s_0 = 1` with `C e C = C` for
`e = 1 - s_0t_0`, by `universal-split-pair-seed-ring`, and `EL_4(C)` is
finitely generated.  So
`full-complementary-idempotent-elementary-full-mf-radical` applies at
`n = 4` and every homomorphism from `B = EL_4(C)` to an MF group is trivial.

Let `R` be nonzero countable unital with a properly infinite unit, and let
`phi : C -> R` be the unital map of `universal-split-pair-seed-ring` clause 4.
Coefficientwise application gives `EL_4(C) -> EL_4(R)`, and
`elementary-rank-descent-to-two` gives `Psi : EL_4(R) -> EL_2(R)` with
`Psi(e_12(1))` normally generating `EL_2(R)`.  Since `1` is in the image of
`phi`, the composite `f` hits that element, so `f(B)` normally generates
`EL_2(R)`, and after the standard block inclusion it normally generates
`EL_n(R)` for every `n >= 2`.

Let `rho : EL_n(R) -> M` with `M` MF.  Then `rho . f` is trivial, so `rho`
kills a normal generating set, so `rho` is trivial.
