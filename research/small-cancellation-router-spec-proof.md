---
rg: 2
id: small-cancellation-router-spec-proof
kind: route
title: Freeze the router interface and machine-check that its conclusion list suffices
target: bespoke-routing-lemma
requires:
  - greendlinger-free-product-lemma
artifacts:
  - GroupApproximation/Sofic/SmallCancellationRouter.lean
---

## The spec-first reduction

`GroupApproximation/Sofic/SmallCancellationRouter.lean` splits the claim
into a machine-checked half and a single open combinatorial half.

**Checked half.**  `RoutingLemmaData` freezes the output of the hoped-for
bespoke lemma for an ARBITRARY source group, designated normal subgroup
`N`, protected element `s`, and finitely presented Kazhdan partner —
decoupled from the Fournier–Facio skeleton.  Two demands are enforced
structurally rather than stored: `route_protected_ne_one` derives
survival of the protected element from `Set.InjOn` on `{1, s}`, and
`kazhdan` derives property (T) of the quotient from the partner's
surjection.  The keystone `RoutingLemmaData.toDefectRoutingData`
instantiates the interface at `N = D.core.defectNormal`, `s = D.s` of any
`FournierFacioDefectData` and produces the `DefectRoutingData` consumed
by the kernel-checked full-MF-radical machine;
`nonempty_defectRoutingData` feeds the frozen public endpoint's single
hypothesis.  The adapter
`RelativeCommonQuotientData.toRoutingLemmaData` shows the abstraction is
faithful to the literature-shaped interface.  So "the conclusion list of
the bespoke lemma suffices for the Main Theorem" is now itself
machine-checked — whoever proves the routing lemma has proved the
theorem.

**Word-level foundation, also checked.**  Over a free group with
Mathlib's reduced words: `symmetrization` (rotations of relators and
formal inverses, honest via `List.rotate` and `FreeGroup.invRev`),
`isConj_mk_rotate` and `normalClosure_symmetrization` (symmetrizing
presents the same group), `IsPiece`, the metric condition
`MetricSmallCancellation` (C'(λ)), the `GreendlingerConclusion`
predicate, and from it — with no gap — `norm_bound_of_greendlinger`
(nontrivial relator-subgroup elements are longer than half of some
relator) and `injOn_mk'_of_greendlinger` (the presented quotient is
injective on any set whose differences are short against the relators:
the protected-set obligation in exactly the interface's shape).

**Open half.**  Exactly one lemma remains, frozen as the hypothesis
`GreendlingerGate`: C'(1/6) families of cyclically reduced relators
satisfy the Greendlinger conclusion — first over a free group, then in
the relative form over free-product syllables
([[greendlinger-free-product-lemma]]) that the final router will apply
to the HNN source and Kazhdan partner.  Per the data-not-axiom doctrine
the gate is consumed only as an explicit hypothesis
(`protected_injOn_of_gate`), never as an axiom.  Beyond the gate, the
router's remaining group-theoretic outputs (defect surjectivity onto the
common quotient, two-generation, torsion preservation, finite
presentation) are the free-product small-cancellation constructions that
the same relative lemma is expected to yield; they are recorded in the
interface but not yet derived from word combinatorics.
