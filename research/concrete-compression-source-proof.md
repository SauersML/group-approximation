---
rg: 2
id: concrete-compression-source-proof
kind: route
title: Britton's lemma on the length-four commutator word
target: concrete-compression-source
requires: []
artifacts:
  - GroupApproximation/Sofic/ConcreteCompressionSource.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean
  - GroupApproximation/Sofic/LiteralAffineFreeProductSource.lean
  - GroupApproximation/Sofic/LiteralAffineFreeProductBassSerreIndependence.lean
---

## Direct proof, formalized

Work in Mathlib's `HNNExtension` of `Base = Gamma x Multiplicative Z`
with associated subgroups the base copy of `Gamma` and of
`alpha(Gamma)`, and isomorphism induced by `alpha` (via
`MonoidHom.ofInjective` on both sides).

- Compression is the defining HNN relation
  (`HNNExtension.equiv_eq_conj`, unpacked through the two
  `ofInjective` coercions): `t (gamma, 1) t^{-1} = (alpha gamma, 1)`.
- (W2) is pure centrality: the witness `c = (1, ofAdd 1)` is central in
  the base, so `t c t^{-1}` commutes with every `t (gamma,1) t^{-1}`
  after conjugating the base identity `c g = g c` by `t`.
- Nontriviality is Britton's lemma, packaged in Mathlib as
  `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`: the
  commutator `[t c t^{-1}, gamma_0]` is the product of the reduced word
  `t c t^{-1} gamma_0 t c^{-1} t^{-1} gamma_0^{-1}` whose chain
  condition holds because `c, c^{-1}` are outside the unmoved subgroup
  (nonzero cyclic coordinate) and `gamma_0` is outside the moved
  subgroup (`gamma_0` not in the image of `alpha`).  If the commutator
  were `1` it would lie in the base copy's range, forcing the reduced
  word's letter list to be empty — but it has four letters.

Packaging: `CompressionSourceData` (the Fournier--Facio defect datum
minus simple subgroup and property (T)), the forgetful map
`ofFournierFacio`, the upgrade `core` to `KazhdanCompressionCore` when
(T) is supplied (with `core_transported`, `core_defectNormal_eq`,
`witness_commutator_mem_defectNormal`), the generic `sourceData`, and
the explicit `integerSource` at the doubling map with
`base_isPowerTorsionFree`.

The later literal affine-congruence specialization closes every source-stage
condition.  It restricts affine translation doubling to
`P = ℤ³ ⋊ Γ(3)`, proves the first translation omitted from the range, invokes
the now-unconditional HNN torsion theorem, and proves finite presentation.
The zero-input endpoint is
`LiteralAffineCongruenceSource.exists_literal_torsionFree_finitelyPresented_bareDefectSource`.
Its free-product amplification and explicit independent crossing pair are
proved in `LiteralAffineFreeProductSource` and
`LiteralAffineFreeProductBassSerreIndependence`; in particular
`amplifiedDefect_isSuitable` and `crossingSuitableCarrier_isSuitable` remove
the formerly literature-shaped suitability input.  These declarations are
audited in `GroupApproximation/Endpoint/Audit.lean`.
