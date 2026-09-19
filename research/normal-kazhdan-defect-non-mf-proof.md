---
rg: 2
id: normal-kazhdan-defect-non-mf-proof
kind: route
title: Cut the corner with the Kazhdan projection of the normal subgroup
target: normal-kazhdan-defect-non-mf
requires: []
artifacts:
  - GroupApproximation/Sofic/NormalKazhdanCompressionObstruction.lean
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
  - GroupApproximation/Sofic/InternalRadicalGap.lean
---

## Why sufficient

Machine-checked in the repository, with no `sorry`, no `axiom`, and no
tagged literature premise anywhere in `GroupApproximation/`.  The declarations:

- `KazhdanCompressionCore.not_isWeakMF_of_normalKazhdan_le_defect`
  (`NormalKazhdanCompressionObstruction.lean`) — hypotheses
  `[Countable E]`, `K.Normal`, `Nontrivial K`,
  `HasKazhdanPropertyT K`, `K <= C.defectNormal`; conclusion
  `¬ IsWeakMF E`;
- `KazhdanCompressionCore.normalKazhdan_le_normMFResidual`
  (`NormalKazhdanMFRadical.lean`) — same hypotheses, conclusion
  `K <= normMFResidual E`, the elementwise form;
- `normalKazhdan_le_coronaMFResidual` and
  `normalKazhdan_le_normMatrixCStarCoronaKernel` — the same statement in the
  manuscript's cofinite-corona and C-star-corona targets;
- `isOperatorMF_iff_coronaMFResidual_eq_bot` together with
  `isCDEOperatorMF_iff_isOperatorMF` turn a nontrivial residual into failure
  of both MF predicates.

The mathematics, for a reader who wants it without Lean.  Suppose `E` has a
weak-MF approximation.  `InternalRadicalGap.exists_setup` applies property
(T) of `K` inside the model: the Kazhdan projection of `K` is an honest
projection whose range is the `K`-fixed space of the model, and because `K`
is **normal**, conjugation by any ambient element permutes `K` and therefore
preserves that fixed space — the projection is ambient-invariant.  This is
the step that replaces finiteness: the ordinary Kazhdan-corner construction
needs the spectral set to generate the ambient group, and normality is what
removes that need (`InternalRadicalGap` header).
`exists_ambientMovingCornerSchedule` turns this into a schedule of ambient
moving corners, giving an operator-norm almost representation on the corner
and hence a tracial ultraproduct representation in which some element of `K`
survives.  The first Kazhdan compressor, applied to that same corner model,
transports the centralizer and kills every compression defect, hence their
normal closure, hence all of `K` — contradiction.

The elementwise upgrade to the residual runs the same argument inside the
range of an arbitrary corona representation: the range is countable and
embeds in the ultraproduct, so its universal norm-MF residual is trivial and
it is operator-MF; local tensor-power normalization converts that into a
uniformly separated weak-MF approximation, which the obstruction forbids.

Nothing in this chain mentions the order of any element, so it applies
verbatim to torsion-free `E`.  The one thing it does need and the finite
branch does not is property (T) of `K` itself; an infinite cyclic centre is
amenable and can never supply it, which is why the central-mark branch
(`commutant-projection-extraction`) remains a genuinely separate problem.
