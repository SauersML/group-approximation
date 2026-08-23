---
rg: 2
id: concrete-compression-source
kind: claim
title: The bare affine HNN skeleton is an unconditional compression source
distinct_from:
  bespoke-routing-lemma: That claim is the routing QUOTIENT step (small-cancellation common quotient realizing DefectRoutingData); this one is the routing SOURCE step — an explicit group with a protected nontrivial compression defect, needing no routing at all.
artifacts:
  - GroupApproximation/Sofic/ConcreteCompressionSource.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean
  - GroupApproximation/Sofic/LiteralAffineFreeProductSource.lean
  - GroupApproximation/Sofic/LiteralAffineFreeProductBassSerreIndependence.lean
---

Over any injective endomorphism `alpha` of a group `Gamma` with an
element outside its image, the HNN extension of the base
`Gamma x Z` conjugating the `Gamma`-copy onto its `alpha`-image is a
compression source datum: the stable letter compresses the source copy,
the transported central witness `t c t^{-1}` commutes with the whole
compressed copy, and the marked commutator `[t c t^{-1}, gamma_0]` is
nontrivial for every `gamma_0` outside the image of `alpha`.  No
property (T), no simple subgroup, no Clifford kernel, and no torsion
witness are involved; the instance at the doubling map of `Z` is
completely explicit.  This realizes the one-paper program's minimal
source: all obstruction is created later by the routing quotient
(saturation plus partner-(T) makes the normal-Kazhdan hypothesis hold
with the whole quotient), so the source needs nothing beyond a
protectable nontrivial defect.

## Literal unconditional package

The generic HNN constructor is instantiated without hypotheses at

\[
P=\mathbb Z^3\rtimes\Gamma(3),
\]

using the injective endomorphism which doubles translations and fixes the
level-three linear part.  The first translation is outside its image.
`LiteralAffineCongruenceSource.literalBareDefectSourceData` packages the
compression core, while
`exists_literal_torsionFree_finitelyPresented_bareDefectSource` proves, with
no parameters or literature-shaped assumptions, that the Kazhdan base and
HNN envelope are torsion-free and finitely presented.

For the bespoke router, `LiteralAffineFreeProductSource.amplifiedDefectData`
free-product amplifies this envelope by an infinite cyclic factor.
`LiteralAffineFreeProductBassSerre.amplifiedDefect_isSuitable` proves that its
defect is a suitable subgroup for the Bass--Serre action, and
`crossingSuitableCarrier_isSuitable` supplies an explicit two-loxodromic
carrier inside that defect.  Hence the source and suitability stages of the
fully formal torsion-free route are closed; the remaining formal seam is the
small-cancellation routing quotient.
