---
rg: 2
id: sl3z-every-cocompact-quotient-far-from-finite-actions
kind: claim
title: For every cocompact lattice Λ of SL3(R), SL3(Z) on SL3(R)/Λ is uniformly far from every finite action
distinct_from:
  sl3z-cocompact-quotient-uniformly-far-from-finite-actions: that is Theorem E under hypothesis (R), a unipotent-free rational representation of Λ, through Bass-Milnor-Serre; this removes (R), covering every cocompact lattice, through Margulis superrigidity
---

**ESTABLISHED (unreviewed).** Let `Λ <= SL_3(R)` be any cocompact lattice and `X = SL_3(R)/Λ`. There is `ε_E > 0`
such that for every finite `SL_3(Z)`-set `V` and every `y : V → X`, some `v ∈ V` and elementary matrix `s`
satisfy `d̄(y(sv), s·y(v)) >= ε_E`.

**Sharp line.** Lattices commensurable with a conjugate of `SL_3(Z)` have exactly equivariant finite
models: their Hecke orbits (`sl3z-cocompact-wc-iff-weak-limit-of-congruence-quotients`, calibration).
Every cocompact lattice has none, at a uniform scale. Only the non-uniform lattices outside the class
remain undecided. An example is the unitary groups `SU(h, O_E)` of isotropic hermitian forms over real
quadratic fields (recalled). There, unbounded lifts in the cusp break the flat-label normal form.

**Scope of the other results.** The same substitution, replacing (R) by
`sl3z-maps-to-cocompact-lattices-have-finite-image`, extends the following to every cocompact `Λ`:
`sl3z-cocompact-not-factor-of-bernoulli-times-profinite` and the conditional route
`sl3z-cocompact-exclusion-from-almost-cocycle-rounding`. The open claims
`sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions` and
`sl3z-lambda-almost-cocycles-round-to-flat-ones` can therefore be posed for every cocompact `Λ`.

Proof in `sl3z-every-cocompact-quotient-far-from-finite-actions-proof`.
