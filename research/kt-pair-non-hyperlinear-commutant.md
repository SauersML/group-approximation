---
rg: 2
id: kt-pair-non-hyperlinear-commutant
kind: route
title: Refute hyperlinearity through the relative commutant instead of the masa
target: non-hyperlinear-group
requires: [kt-centralizer-normalization-hs]
artifacts:
  - notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md
---

# Refute hyperlinearity through the relative commutant

The second rigidity input to the same conclusion as
`kt-pair-non-hyperlinear-rigidity`, along a disjoint path.

Kun–Thom prove Theorem A (nonsoficity of `W`) not from Corollary D but from
Theorem 4.1: the centralizer of a Kazhdan sofic approximation is normalized by
the ambient group. Only three facts are used downstream of it — that `Γ` fixes
the base coset, that lamps at distinct cosets are distinct, and that a strict
compressor exists. All three are statements about `W` and hold verbatim in any
faithful tracial representation. So the Hilbert–Schmidt analogue of Theorem 4.1
(`kt-centralizer-normalization-hs`) alone refutes hyperlinearity of `W`; no
masa, no Cartan completion, and no reference to the coset action's soficity
enters.

That makes the two rigidity routes genuinely independent inputs: one buys the
conclusion from Corollary D plus a lifting theorem about the ambient diagonal,
the other from a normalization theorem about a relative commutant. So a
construction on the flexible side carries a design constraint that
`fiber-masa-free-cocycle` clause 3 does not display: defeating every invariant
diagonal masa is necessary, but a fiber cocycle achieving it may still put
`ρ(a_(tΓ))` in the relative commutant of `σ(Γ)`, and then the commutant route
closes it anyway. Any proposed cocycle should be checked against both.
