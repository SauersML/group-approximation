---
rg: 2
id: normal-kazhdan-defect-non-mf
kind: claim
title: A normal Kazhdan subgroup in the compression defect kills every corona representation
distinct_from:
  finite-normal-compression-obstruction: that claim needs the subgroup finite and cancels by averaging over it; this one needs property (T) of the subgroup instead and needs no finiteness, centrality, or torsion.
  central-sign-corona-obstruction: that claim marks a central involution and cuts the corner from its own two-point spectrum; this one cuts the corner from the Kazhdan fixed-space projection of a normal subgroup.
  corona-corner-detection-criterion: that claim analyses which corners a central mark of arbitrary order can supply; this one obtains the corner from property (T) of the marked subgroup and reaches the non-MF conclusion outright.
  finite-infranormal-subgroup-is-normal: that claim is a group-theoretic normality statement about finite infranormal subgroups; this one is an analytic non-MF obstruction whose subgroup is assumed normal and Kazhdan and may be infinite.
artifacts:
  - GroupApproximation/Sofic/NormalKazhdanCompressionObstruction.lean
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
  - GroupApproximation/Sofic/NormalKazhdanHyperlinearKilled.lean
  - GroupApproximation/Sofic/QuestionTwoReduction.lean
  - GroupApproximation/Sofic/InternalRadicalGap.lean
  - GroupApproximation/Sofic/KazhdanCompressionCore.lean
  - GroupApproximation/Sofic/CoronaImageNormalKazhdan.lean
  - GroupApproximation/Endpoint/ChosenNonMFAudit.lean
---

Let `C : KazhdanCompressionCore Gamma E` with `E` countable — that is,
`iota : Gamma -> E` with `Gamma` Kazhdan, `t` compressing `iota(Gamma)` into
itself, and `c` centralizing `iota(Gamma)` — and put
`defectNormal = normalClosure {[t c t^-1, iota gamma]}`.  If `K` is a
**nontrivial normal subgroup of `E` with property (T)** and
`K <= defectNormal`, then every homomorphism from `E` to the unitary group
of a norm matrix corona kills `K` elementwise.  Consequently `E` is not MF.

**Finiteness, centrality and torsion are all unnecessary.**  This is the
second killing theorem in the repository, it is machine-checked, and it is
the one that survives the passage to torsion-free groups.  The corner that
the finite-normal branch obtains by averaging, and the central branch
obtains from a two-point spectrum, is here the fixed-space projection of the
Kazhdan projection of `K`; normality of `K` is exactly what makes that
projection invariant under the ambient group, hence a legitimate corner.

The root `torsion-free-finitely-presented-non-mf` therefore has no remaining
analytic obstacle on this branch.  What it needs is a torsion-free finitely
presented group whose compression defect contains a nontrivial normal
Kazhdan subgroup — a question of combinatorial group theory.

**LEAN STATUS.**  The moving-corner contradiction is
`KazhdanCompressionCore.not_isWeakMF_of_normalKazhdan_le_defect`; the
elementwise radical theorem is
`KazhdanCompressionCore.normalKazhdan_le_normMFResidual`; and the direct
standard-MF conclusion is
`QuestionTwoReduction.not_isOperatorMF_of_nontrivial_normal_kazhdan_defect`.
The still more general theorem
`normalKazhdan_le_normMFResidual_of_hyperlinear_killed` accepts an arbitrary
tracial-shadow kill proof and assumes no compression structure.  All four are
kernel checked and appear in `Endpoint/ChosenNonMFAudit.lean`.

This completes the analytic route in Lean.  It deliberately does **not** claim
that the separate Fournier--Facio--Hull torsion-free routing input has been
constructed in Lean: `TorsionFreeFullMFRadical.lean` formalizes what follows
from that routing datum, while the suitable-subgroup small-cancellation
existence step remains outside the current formal library.
