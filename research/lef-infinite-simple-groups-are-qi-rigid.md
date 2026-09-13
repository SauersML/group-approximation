---
rg: 2
id: lef-infinite-simple-groups-are-qi-rigid
kind: claim
title: A finitely generated infinite simple LEF group is not finitely presented and is quasi-isometric to no finitely presented group, so the measure side of the UN ladder is separated from the non-MF side by a coarse invariant
distinct_from:
  lef-simple-rings-are-not-finitely-presented: that is about the coefficient ring being finitely presented as a ring; this is about the group being finitely presented and about its quasi-isometry class.
  fp-upgrades-make-non-lef-and-non-lea-cheap: that records the Vershik-Gordon upgrade and uses it to refute LEF from finite presentation; this runs it the other way, from LEF to the failure of finite presentation, and draws the quasi-isometry consequence.
artifacts:
  - research/artifacts/un-open-7-coarse-geometry-2026-09-13.md
---

**ESTABLISHED (2026-09-13, unreviewed)** through `lef-infinite-simple-groups-are-qi-rigid-proof`.

Let `S` be a finitely generated, infinite, simple, LEF group. Then

1. `S` is not finitely presented;
2. `S` is not quasi-isometric to any finitely presented group;
3. `S` is not of type `F_2`: it has no classifying space with finite 2-skeleton, and it
   has no Dehn function.

**Consequence for the UN ladder.** Every measure-side rung is such a group: with `R`
exactly matricial, `EL_n(R)` is LEF, and `S = EL_n(R)/Z` is finitely generated, infinite
and simple by `steinberg-elementary-groups-are-simple-mod-centre`. The Pestov witness of
`infinite-simple-kazhdan-hyperlinear-group` is the case of a minimal subshift. The non-MF
side, by contrast, contains finitely presented examples: the non-MF paper produces a
finitely presented torsion-free Kazhdan group with no nontrivial homomorphism to an MF
group. So the two ends of the program are separated by a **quasi-isometry invariant**.

That is a different kind of separation from every other one recorded in the program. No
MF quotient versus LEF, corona traces, Sylvester rank functions and type semigroups are
all ring-theoretic or operator-algebraic, and none of them is known to be a coarse
invariant. Finite presentability is one, and the argument uses no operator algebra.

**Scope, stated plainly.** Item 2 compares the measure side with a finitely presented
group from the non-MF paper, not with a finitely presented rung of the form
`EL_n(A_k(𝒢))/Z`. Whether the paradox side of the ladder itself contains a finitely
presented rung is open: see `paradox-side-elementary-group-is-finitely-presented`.
Quasi-isometry invariance of type `F_2` is classical (Alonso) and is cited from standard
knowledge; it was not re-read from the source in this lane.

**Review (un-verify, 2026-09-13): PASS.** Vershik–Gordon (finitely presented LEF ⇒ residually finite), infinite simple ⇒ not residually finite, and quasi-isometry invariance of finite presentability give items 1–3. Scope note on the consequence paragraph: `S = EL_n(R)/Z` is LEF when the central scalars map to central scalars of the finite models, as in the Pestov construction (§3.3) and for Steinberg rings with centre `k^×`; finite generation needs `k` finite. See `research/artifacts/un-review-2026-09-13-part9.md` §2.
