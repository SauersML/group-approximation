---
rg: 2
id: bespoke-routing-lemma
kind: claim
title: A minimal small-cancellation routing lemma suffices for DefectRoutingData
artifacts:
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
  - 999c6320c:GroupApproximation/Sofic/FullMFRadicalEndpoint.lean
---

There is a relative/free-product small-cancellation theorem, provable by
elementary normal-form and Greendlinger arguments without any general
theory of acylindrical hyperbolicity, whose conclusion is exactly the
field list of `DefectRoutingData`: given a finitely presented
torsion-free source `E` with a nontrivial compression defect `N` and a
protected element `s != 1` in `N`, and a finitely presented torsion-free
property-(T) partner `B`, it produces a common quotient
`q : E ->> Q` with `Subgroup.map q N = ⊤`, `q s != 1`, `Q` two-generated,
finitely presented, torsion-free, and (T) inherited from `B`.

This is the decisive open gate of the one-paper program: the analytic
machine (`DefectRoutingData` to full CDE MF radical to hereditary
non-MF-ness of every nontrivial quotient) is already kernel-checked, and
the frozen public endpoint
(`FullMFRadicalEndpoint.exists_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical`)
consumes exactly `Nonempty (DefectRoutingData D)`.  Two design notes fix
the search space.  First, the source needs NO intrinsic obstruction: the
routed quotient satisfies the normal-Kazhdan hypothesis with the normal
(T) subgroup equal to `Q` itself (saturation plus (T) of `Q`), so the
source only has to offer a protectable nontrivial defect — it may itself
be MF.  Second, by the strict-gap theorem
([[mf-vs-tracial-radical-strict-gap]], the infinite-cyclic commuting
lamp is MF), torsion-free commuting-lamp sources are themselves MF,
which is consistent with and irrelevant to this routing architecture:
all obstruction is created by the quotient, none is required of the
source.  The candidate minimal source is the bare HNN skeleton already
recorded in `FournierFacioDefectData` (central witness `c`, Britton
nontriviality of `[tct^{-1}, gamma]`), decoupled from the simple
subgroup used for nonsoficity.

## Attempts

The spec-first attack is recorded in
[[small-cancellation-router-spec-proof]]: the router interface
(`RoutingLemmaData`), its keystone reduction to `DefectRoutingData`, and
the word-level Greendlinger consequences are formalized sorry-free in
`GroupApproximation/Sofic/SmallCancellationRouter.lean`; the single
remaining input is [[greendlinger-free-product-lemma]].
