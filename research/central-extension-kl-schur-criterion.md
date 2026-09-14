---
rg: 2
id: central-extension-kl-schur-criterion
kind: claim
title: A central extension solves every lifted nonsingular equation when its multiplier kills the Schur kernel
distinct_from:
  kl-simple-failure-leaves-only-the-cyclic-quotient: that describes the whole collapse over a simple coefficient group, which has no center; this is a criterion for coefficient groups that are central extensions of a group whose own adjunction injects.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Let `1 -> Z -> E -> Q -> 1` be central with multiplier `alpha`, let
`w in E * <t>` have `deg_t(w) != 0`, and let `w-` be its image in
`Q * <t>`. Assume `Q -> (Q * <t>)/<<w->>` is injective.

1. If `alpha_H(K_2(Q, w-)) = 0`, then `E -> (E * <t>)/<<w>>` is injective.
   The root lives in a central extension of the quotient adjunction by a
   divisible group containing `E`.
2. `Z` injects into the centralized quotient
   `(E * <t>)/<<w, [Z, t]>>` **if and only if** `alpha_H(K_2(Q, w-)) = 0`.
   The answer depends on `alpha` and `w-` only, not on the lift `w`.

**Consequences.**

* Every Kervaire--Laudenbach failure over such an `E` kills a central
  coefficient and forces `alpha_H(K_2(Q, w-)) != 0`.
* The conjecture holds over every central extension of `Q` at lifts of
  `w-` when `Q` injects and `K_2(Q, w-) = 0`. This covers aspherical
  adjunctions, and hyperlinear `Q` whose Schur multiplier is separated by
  projective unitary multipliers.
* Deligne's triple cover `E_3` satisfies the conjecture at every lift of
  `w-` unless the Schur kernel of `w-` over `Sp_4(Z)` meets the mod-three
  multiplier. That is the question
  `sp4-schur-kernel-meets-the-deligne-triple-class`.

The criterion does not characterize survival in `(E * <t>)/<<w>>` itself.
There the multiplier condition is necessary for a failure, but it is not known
to be sufficient.

DERIVATION
central-extension-kl-schur-criterion-proof
