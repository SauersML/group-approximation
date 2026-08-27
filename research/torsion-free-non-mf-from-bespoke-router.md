---
rg: 2
id: torsion-free-non-mf-from-bespoke-router
kind: route
title: Feed the routed quotient to the frozen full-radical endpoint
target: torsion-free-finitely-presented-non-mf
requires: [bespoke-routing-lemma, concrete-compression-source, hnn-torsion-theorem]
artifacts:
  - 999c6320c:GroupApproximation/Sofic/FullMFRadicalEndpoint.lean
  - GroupApproximation/Sofic/SmallCancellationRouter.lean
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
---

## Why sufficient

The analytic machine is already kernel-checked and frozen.
`FullMFRadicalEndpoint.exists_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical`
consumes exactly `Nonempty (DefectRoutingData D)` and concludes with a
two-generated, finitely presented, torsion-free Kazhdan group whose MF radical
is everything.  Every adjective this root asks for is in that conclusion.

[[bespoke-routing-lemma]] is precisely the statement that the datum exists: from
an unconditional compression source `E` — the bare affine HNN skeleton of
[[concrete-compression-source]], carrying a nontrivial compression defect `N`
and a protected `s != 1` in `N` — together with a finitely presented
torsion-free property-(T) partner `B`, it produces a common quotient
`q : E ->> Q` with `Subgroup.map q N = ⊤`, `q s != 1`, and `Q` two-generated,
finitely presented, torsion-free and Kazhdan.  Feeding that to the endpoint
gives `Rad_MF(Q) = Q`, and `Q != 1` since it is Kazhdan and two-generated with
`q s != 1`, so `Q` is not MF.

## Why this is a different route and not a restatement

`torsion-free-non-mf-from-defect-saturation` reaches the root through the same
endpoint but takes its existence input from Hull Theorem 7.1 applied to
Fournier-Facio's compression configuration.  This route replaces that input with
an elementary relative small-cancellation argument over a free product, provable
by normal-form and Greendlinger reasoning with no theory of acylindrical
hyperbolicity anywhere.  The two differ in exactly the input that is open, which
is the only place a route can differ that matters: closing either one closes the
root, and neither closes the other.

The remaining gate is one lemma.  The router interface `RoutingLemmaData`, its
keystone reduction to `DefectRoutingData` and the word-level Greendlinger
consequences are formalized sorry-free in `Sofic/SmallCancellationRouter.lean`;
the single open input is [[greendlinger-free-product-lemma]].

Two design notes from the source claim carry over and constrain anyone
extending this route.  The source needs no intrinsic obstruction — the routed
quotient satisfies the normal-Kazhdan hypothesis with the normal (T) subgroup
equal to `Q` itself, so `E` need only offer a protectable nontrivial defect and
may itself be MF.  And by [[mf-vs-tracial-radical-strict-gap]] torsion-free
commuting-lamp sources *are* MF, which is consistent with this architecture
rather than an obstacle to it: all obstruction is created by the quotient, none
is required of the source.
