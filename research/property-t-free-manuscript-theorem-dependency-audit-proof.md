---
rg: 2
id: property-t-free-manuscript-theorem-dependency-audit-proof
kind: route
title: Read every numbered statement and separate retained algebra from Kazhdan machinery
target: property-t-free-manuscript-theorem-dependency-audit
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - metadata/NON_MF_SENTENCE_CENSUS.md
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

## Exact three-way checklist

### Already Property-`(T)`-free

The following numbered statements, or the indicated literal clauses of mixed
statements, are already proved without a Kazhdan hypothesis:

* Proposition `prop:mf-residual-calculus` in full;
* Theorem `thm:commutant` in full, including finite-dimensional and residually
  finite sterility of the compression-centralizer defect;
* Lemma `lem:stable-finite` and Lemma `lem:central-corona-corner` in full;
* Lemma `lem:tau-elementary` and the compressor containment clause
  `tau L tau^-1 <= L` of Proposition `prop:leavitt-compression`;
* Lemmas `lem:normal-generation-transvection` and
  `lem:coefficient-separation`, Propositions `prop:simple` and `prop:defect`;
* the functoriality, simple-intersection, normal-generation, and surjective
  image clauses of Proposition `prop:defect-saturation` before its two
  Property-`(T)` conclusions;
* Proposition `prop:full-kernel-pullback` and Proposition
  `prop:universal-factorization` in full; and
* Theorem `thm:prescribed-quotients` as a theorem conditional on an arbitrary
  supplied full-radical group `B`.

The MF-radical definitions, MF-kernel closure, quotient-MF equivalence,
countability/nontriviality of the literal Leavitt group, exact Whitehead
identities, marked-root nontriviality and normal generation, and the generic
reduced-group-C-star implication are likewise already independent of
Property `(T)`.

### Awaiting only the new MF-radical endpoint

Modulo clean rank transport already established in Cairn, exactly these
retained conclusions wait on direct Property-`(T)`-free full collapse of the
binary-Leavitt group:

* `Rad_MF(EL_12(R)) = EL_12(R)`;
* every homomorphism from `EL_12(R)` to a countable MF group is trivial;
* `EL_12(R)` is non-MF, hence not every countable group is MF;
* `C*_r(EL_12(R))` is a separable stably finite non-MF C-star algebra; and
* the concrete instances of `thm:prescribed-quotients` and the one-word
  quotient test obtained by taking `B = EL_12(R)`.

There are two equivalent live ways to supply the one missing mathematical
input.  A direct `EL_20(R)` collapse uses the already established
`property-t-free-el20-collapse-transfers-to-el12`; an intrinsic `St_20(R)`
collapse uses the already established
`property-t-free-st20-collapse-transfers-to-el12`.  Neither collapse is
established at this audit snapshot.

### Independent work, not supplied by MF collapse

The following tasks do not become theorems merely by closing full MF radical:

* delete, rather than relabel, `thm:compression-criterion`,
  `lem:kazhdan-projection-order`, `thm:transport`, `cor:defect-hs`, and
  `thm:normal-kazhdan`; delete the Property-`(T)` conjuncts of the headline
  and `prop:leavitt-compression`, the two Property-`(T)` terminal clauses of
  `prop:defect-saturation`, and the amenable-plus-Kazhdan remark;
* split the clean algebraic declarations out of modules whose import cones
  currently pass through `PrintedCriterion`, `HeadlineTheorem`,
  `HilbertHotelEndpoint`, or `PropertyTT.RingHypotheses`, and assemble
  `Unconditional.lean` from the split modules;
* rewrite the TeX statement/proof/badge surface and regenerate its sentence
  metadata so no removed Kazhdan section is still advertised; and
* if the demand is literally to prove every historical prose assertion
  in-repository, separately formalize the four non-Kazhdan partial sentences
  in `metadata/NON_MF_SENTENCE_CENSUS.md`: the Blackadar--Kirchberg NF
  converse, the Goldbring--Hart/CEP implication, Shulman's double permanence,
  and the finite-Schatten non-approximability results.  None is used by the
  manuscript's theorem chain.  The remaining fifth partial sentence is the
  EJZ Property-`(T)` theorem and is deleted with the Kazhdan discussion.

Keeping the original Kazhdan-specific numbered statements while forbidding
Property `(T)` from the mathematical language is not a meaningful target:
their hypotheses and conclusions explicitly mention it.  The sound target is
the retained endpoint package listed above.

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
