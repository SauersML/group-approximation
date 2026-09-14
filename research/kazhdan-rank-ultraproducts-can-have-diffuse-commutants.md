---
rg: 2
id: kazhdan-rank-ultraproducts-can-have-diffuse-commutants
kind: claim
title: An ultraproduct of irreducible F_2-representations of a Kazhdan group can have a diffuse relative commutant in rank
distinct_from:
  kazhdan-group-rank-models-admit-no-expander-decomposition: that is the finite-stage failure of rounding, dimension expansion and expander decomposition; this is the ultraproduct form, a continuous chain of commuting idempotents in the relative commutant and invariant right ideals without atoms.
  rank-ultraproduct-compressors-conserve-fixed-right-ideals: that shows compressors conserve pointwise-fixed right ideals; this shows the invariant, not fixed, right ideals of a Kazhdan group can form a diffuse lattice.
  invariant-size-collapse: that is the principle that an invariant size separating proper inclusions forbids strict compression; this exhibits a relative commutant with a continuum of idempotents, where no such size is known.
artifacts:
  - research/artifacts/kazhdan-rank-rounding-counterexample-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma = EL_3(F_2[t])`, and let `rho_k : Gamma -> GL_(3k)(F_2)` be
the irreducible representations of `kazhdan-group-rank-models-admit-no-expander-decomposition`.
Let `sigma = [rho_k] : Gamma -> M^x`, where `M` is the rank ultraproduct of the
`M_(3k)(F_2)`.

* **A chain of idempotents.** For every `beta` in `[0,1]` the degree truncations give an
  idempotent `p_beta` in `sigma(Gamma)' n M` of rank `beta`, with
  `p_beta p_gamma = p_min(beta,gamma)`. Each `rho_k` has only `0` and `1` as idempotents
  in its commutant.
* **No atoms.** Every `sigma(Gamma)`-invariant right ideal `eM` contains invariant right
  ideals of every rank in `[0, rk e]`.

For a Kazhdan group, ultraproducts of transitive actions are ergodic in the Loeb measure.
Ultraproducts of irreducible unitary representations have scalar relative commutant in
the tracial ultraproduct. Both follow from the uniform spectral gap. The rank row is the
one metric of the three where property (T) gives no such rigidity. So the size axiom
(A3) of the ladder artifact's conservation criterion cannot come from atoms of the
invariant lattice.

Proof: Section 4 of the artifact.
