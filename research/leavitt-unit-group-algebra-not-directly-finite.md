---
rg: 2
id: leavitt-unit-group-algebra-not-directly-finite
kind: claim
title: The modular group algebra of the Leavitt unit group is not directly finite
root: true
distinct_from:
  binary-leavitt-algebra-not-directly-finite: that is the established defect in the Leavitt algebra, which is not a group algebra; this is the same failure demanded of F_2[R^x], which is one, and the gap between them is exactly direct-finiteness-not-inherited-by-quotients.
  kl-violating-equation-over-leavitt-unit-group: that is an equation-solving question over the same group, aimed at hyperlinearity through Kervaire--Laudenbach; this is a ring-theoretic question about its modular group algebra, aimed at Kaplansky, and neither is known to imply the other.
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that is a soficity statement about d-ary Leavitt unit and elementary groups, proved here through property (T); this is a ring identity demanded of one modular group algebra, and soficity of the group would refute it rather than supply it.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

*Marked `root` because it heads a lane of its own. It is not on the way to
`q3-4-resolved` and no route should be built from it toward that goal — see
the scope note below.*

Exhibit `alpha, beta` in `A = F_2[R^x]`, `R = L_(F_2)(1,2)`, with

    alpha beta = 1        and        beta alpha != 1.

This would refute **Kaplansky's Direct Finiteness Conjecture** — for every
group `G` and every field `K`, `K[G]` is directly finite — since `R^x` is a
group and `F_2` is a field.  Characteristic zero is Kaplansky's own theorem,
in the stronger stably finite form, so positive characteristic is the whole
of what is open; and the sofic case is Elek--Szabo, which is why the *nonsofic*
`R^x` of `openai-leavitt-unit-nonsofic` is the natural place to test it.

**Status: open, and the honest reading is that it is wide open.**  Every route
into it terminates at an unproved lifting statement.  The material that
exists — the surjection
`leavitt-unit-group-algebra-surjects-onto-leavitt`, its unital corner
sharpening `leavitt-corner-idempotent-unital-surjection`, and the explicit
support-three generator lifts `leavitt-rank-three-unit-lift` — establishes
that the defect lives in a *quotient*, which by
`direct-finiteness-not-inherited-by-quotients` proves nothing about `A`.
Anyone reading this lane quickly should read that node first.

## Scope: what this would and would not settle

It would refute Kaplansky's conjecture and would be a major result.  It would
**not** decide hyperlinearity of `R^x`, and so would not answer `q3-4-resolved`
either way.  The implication that connects approximation properties to direct
finiteness runs from **soficity**, over division rings, and `R^x` is announced
nonsofic; no positive-characteristic analogue for hyperlinear groups is
available here to run in either direction.  Conversely a proof that `A` *is*
directly finite would not make `R^x` sofic.  The two questions share a group
and nothing else, and this node is kept out of the goal's route structure for
that reason.

## The lanes

Two go through the explicit corner `e A e`:

* Exhibit the pair inside the corner — `leavitt-corner-one-sided-lift-exists`,
  reached through `binary-leavitt-family-lifts-into-unit-corner`, and padded
  back up to `A` by the route
  `leavitt-unit-algebra-not-directly-finite-by-corner-padding`.
* Prove the structural hypothesis `leavitt-corner-kernel-is-jacobson-radical`
  and let the quotient argument become legal.

Two work in the whole algebra and belong to the surjunctivity lane, which
reaches this claim from the other side: a left-invertible lift of `s_0`
(`left-invertible-lift-of-s0-in-leavitt-group-algebra`) and a module
splitting of the evaluation (`leavitt-evaluation-splits-as-module-map`).
They are independent of the corner lanes — in particular
`leavitt-rank-three-lift-inverse-support-thirteen` constrains the
whole-algebra form and is not known to transfer into the corner.

On the corner lanes, one should be precise about why the corner.  The
`F_2`-augmentation excludes a full **Leavitt family** from `A` itself and from
every corner of augmentation one, so the *family* lifting problem has nowhere
else to live.  It does **not** exclude a bare pair `alpha beta = 1 != beta
alpha` from `A`: applying `eps` gives only `eps(alpha) = eps(beta) = 1`, no
contradiction.  A direct construction of such a pair in `A`, owing nothing to
the corner, remains admissible and would be a third lane; nobody has one.
