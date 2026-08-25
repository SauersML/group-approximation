---
rg: 2
id: property-t-free-manuscript-theorem-dependency-audit-proof
kind: route
title: Read every numbered statement and separate retained algebra from Kazhdan machinery
target: property-t-free-manuscript-theorem-dependency-audit
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - research/property-t-free-manuscript-from-leavitt-collapse.md
  - research/artifacts/finite-coordinate-conditional-reduction-2026-08-24.md
  - GroupApproximation/Steinberg/Basic.lean
  - GroupApproximation/KOne/AllRanksElementaryCore.lean
  - GroupApproximation/Leavitt/PrefixCode.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/ResidualCalculus.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/LiteralMFClosure.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/FiniteDimensionalCommutant.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/RankTwelveConfiguration.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/RankTwelveSimplicity.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/PrintedFullKernelPullback.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/UniversalFactorization.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/PrescribedQuotients.lean
---

## Statement census

The manuscript has three main theorems and seventeen numbered supporting
results.  The Property-`(T)`-free replacement keeps the basic MF-radical
proposition, finite-dimensional commutant rigidity, stable finiteness of norm
matrix coronas, the central-corona-corner lemma, the Whitehead/Leavitt
algebra, simplicity, defect, pullback and factorization results.  It replaces
the headline by the same
statement with the Property-`(T)` conjunct deleted.  It removes Theorem A and
the four numbered Kazhdan transport/radical results because their statements,
not merely their current proofs, are Kazhdan-specific.

Within mixed statements, the split is literal.  The Leavitt-compression
proposition retains `tau in H` and `tau L tau^-1 <= L` and deletes only the
Property-`(T)` conjuncts.  Defect saturation retains functoriality, simple
intersection saturation, normal-generation saturation, and the corresponding
surjective-image conclusion, while deleting its two conclusions whose
hypotheses assert Property `(T)`.

## Dependency check

The only new mathematical implication is MF collapse.  Once it is available
for `St_20(R)`, full-radical quotient permanence sends it through the canonical
Steinberg projection to `EL_20(R)`.  Complete binary prefix codes identify
every positive matrix ring over `R` with `R`; the internal all-ranks elementary
theorem identifies `GL_n(R)` with `EL_n(R)` for `n >= 2`.  Hence `EL_20(R)`
and the manuscript's `EL_12(R)` are isomorphic, and full radical transports to
the printed group.

Everything downstream is already algebraic.  The literal radical and closure
are intersections of kernels and quotient pullbacks.  Full-kernel pullback is
factorization through a surjection.  The prescribed quotient is the pushout
`B *_<d> (Q x <d>)`; its vertex injections are proved by the internal pushout
normal form, and its Hom-set universal property is proved directly.  The
reduced-C-star consequence uses the internally constructed faithful canonical
trace and restriction of an MF embedding to the regular group unitaries.

For the two literature-sensitive Leavitt steps, the repository no longer uses
the citations as premises.  `BinaryLeavitt.exists_mul_mul_eq_one`,
`BinaryLeavitt.center_eq_bot`, `BinaryLeavitt.central_units_trivial`, direct
elementary-root extraction, and
`RankTwelveEndpoint.manuscriptPropositionSimple` discharge the sandwich,
center, and simplicity claims internally.  The Preusser classification is not
used.  Ershov--Jaikin-Zapirain, Akemann--Walter, and the amenable-Kazhdan
finiteness citation occur only in the discarded Kazhdan lane.

## Lean boundary

The current closed manuscript wrappers are not a valid final dependency cone:
`HeadlineTheorem` explicitly packages `HasKazhdanPropertyT`,
`RankTwelveEndpoints` builds full radical through `PrintedCriterion`, and
`MFCamouflageRadical` imports the Property-`(T)`-mediated
`HilbertHotelEndpoint` even though its generic first namespace is independent.
The clean endpoint must therefore consume the new collapse theorem directly,
transport it to rank twelve, and repackage only the retained conclusions.

No declaration with a caller-supplied literature package is required after
that split.  The absence of `Unconditional.lean` is therefore caused by the
open MF-collapse theorem and clean-module assembly, not by another hidden
external theorem.
