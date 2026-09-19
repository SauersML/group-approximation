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
  - research/artifacts/sl2-hnn-iwahori-dynamical-fork-2026-08-21.md
---

*Marked `root` because Kaplansky's conjecture is a top-level question in its
own right, not a step toward another one. It is also reachable from the
surjunctivity root, through `stably-finite-failure-from-direct-finiteness-failure`
into `leavitt-group-algebra-not-stably-finite`; the mark is kept anyway, so
that the lane does not read as a sub-question of Gottschalk. It is not on the
way to `q3-4-resolved` and no route should be built from it toward that goal
— see the scope note below.*

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

There were four.  **Two of them died on 2026-08-17**, and both died for
structural reasons rather than for want of effort — see
`research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md`.  What is
left is the two that ask for an explicit element:

* Exhibit the pair inside the corner — `leavitt-corner-one-sided-lift-exists`,
  reached through `binary-leavitt-family-lifts-into-unit-corner`, and padded
  back up to `A` by the route
  `leavitt-unit-algebra-not-directly-finite-by-corner-padding`.
* A left-invertible lift of `s_0`
  (`left-invertible-lift-of-s0-in-leavitt-group-algebra`), which works in the
  whole algebra and belongs to the surjunctivity lane.  It is independent of
  the corner lane — in particular
  `leavitt-rank-three-lift-inverse-support-thirteen` constrains the
  whole-algebra form and is not known to transfer into the corner.

**Dead.**

* *The radical hypothesis.*  `leavitt-corner-kernel-is-jacobson-radical` is
  **false**: `ker(pi_e)` contains a nonzero idempotent of augmentation zero
  (`leavitt-corner-kernel-not-jacobson-radical`), and a Jacobson radical
  contains no nonzero idempotent.  Route
  `leavitt-unit-algebra-not-directly-finite-by-radical-kernel` invalidated.
* *The module splitting.*  `leavitt-evaluation-splits-as-module-map` is
  **false**: `A` is a prime ring
  (`leavitt-unit-group-algebra-is-prime`), and a section would make `ker(pi)`
  annihilate a nonzero ideal.  Route
  `leavitt-direct-finiteness-failure-from-module-splitting` invalidated.
  `R` is not projective over `A`.

**And one route was added, in the other direction.**  By
`leavitt-stable-finiteness-equals-direct-finiteness`, a failure of stable
finiteness at any matrix size compresses back to this scalar claim
(`leavitt-direct-finiteness-failure-from-matrix-failure`).  So this claim and
`leavitt-group-algebra-not-stably-finite` are interderivable, and Kaplansky
for `F_2[R^x]` and Gottschalk for `R^x` are now the same problem.

On the corner lanes, one should be precise about why the corner.  The
`F_2`-augmentation excludes a full **Leavitt family** from `A` itself and from
every corner of augmentation one, so the *family* lifting problem has nowhere
else to live.  It does **not** exclude a bare pair `alpha beta = 1 != beta
alpha` from `A`: applying `eps` gives only `eps(alpha) = eps(beta) = 1`, no
contradiction.  A direct construction of such a pair in `A`, owing nothing to
the corner, remains admissible and would be a third lane; nobody has one.

## Attempts

**Every lane runs out at the same place, and it is worth seeing that they run
out for different reasons.**

* *Compress the explicit lifts into the corner.*  The inequality comes free
  and the whole problem reduces to one equation `ab = e`, whose defect lies in
  `ker(pi_e)` — see the attempts under `leavitt-corner-one-sided-lift-exists`.
  Dies on having no handle on that kernel.
* *Lift the whole Leavitt family.*  Strictly harder: five relations instead of
  one, each contributing its own kernel element.  Notably it is not *refuted*
  in the corner, because `eps(e) = 0` switches off the only no-go available;
  it is simply unconstrained.
* *Use the radical.*  **Refuted 2026-08-17.**  `ker(pi_e) = J(eAe)` would have
  made the quotient argument legal without exhibiting anything.  It is false:
  the kernel contains a nonzero idempotent.  What is worth keeping from this
  lane is the diagnosis it produced — the question was gated on whether
  `ker(pi_e)` was zero, and that was the right gate.
* *Work in the whole algebra.*  The surjunctivity lane's
  `left-invertible-lift-of-s0-in-leavitt-group-algebra` faces the identical
  correction problem with `ker(pi)` in place of `ker(pi_e)`, and its first
  necessary condition already kills the obvious candidate: a left-invertible
  lift needs `eps(a) = 1`, while the natural four-unit lift has `eps = 0`.

**What has actually been ruled out, as opposed to merely not found.**
*(Rewritten 2026-08-18 — the support floor has been superseded by a complete
no-go.)*  The explicit support-three lifts of `t_0` and of `s_0` have **no
one-sided inverse in `A` at any support whatsoever**, and the corner
compression `e t~ e` has none in `eAe`
(`leavitt-rank-three-lift-has-no-one-sided-inverse`).  The mechanism is
location rather than size: the supports of `t~`, of `s~` and of `e` all lie
inside subgroups isomorphic to `(C_2 x C_2) * C_3`
(`leavitt-rank-three-support-group-is-virtually-free` — the corner's
order-three unit `g` is exactly `u_3`), whose group algebras are directly
finite, and by `subgroup-supported-one-sided-inverse-rigidity` a partner drawn
from anywhere in `A` collapses back into that subgroup.  So every explicit
candidate this lane had built is dead, and the earlier floor
(`leavitt-rank-three-lift-inverse-support-thirteen`, support at least
thirteen, and odd) is now vacuously true.

**The contrapositive is the usable output, and it is sharper than the floor.**
Any surviving witness must have support generating a subgroup with no known
direct finiteness — in particular a **nonsofic** one.  That is exactly why
`openai-leavitt-unit-nonsofic` made `R^x` the right group to test, and it says
the search had accidentally been running inside a virtually free part of it
where a counterexample provably cannot live.  Enumerating candidates by
support size is the wrong measurement; the subgroup generated by the support
is the right one.  Since 2026-08-17 there are two structural exclusions as well,
but note what they exclude: they kill two *ways of arguing*, not any candidate
pair.  Nothing yet excludes a pair.

**The cheapest new information has now been produced, and it did not help.**
This section used to name `ker(pi_e) = 0?` as the cheapest thing anyone could
find out.  The answer is no — `leavitt-corner-kernel-not-jacobson-radical`
exhibits a twelve-term idempotent in it, and
`leavitt-recursive-kernel-idempotents` an infinite orthogonal family.  The
lesson for the surviving lanes is negative and specific: the correction ideal
in `(a + alpha)(b + beta) = e` is large and idempotent-rich rather than
radical noise, so corrections should be sought with Peirce and corner
structure, not with nilpotent perturbation.  The one recursive correction that
the new structure makes natural has been tried and fails — the telescoping
tail `lambda^m(error)` is nonzero at every finite depth, and group-algebra
elements have finite support.

**Still not attempted.**  No machine search has been run at any support size
in this repository, and no presentation of `e A e` exists to search inside.
Two 2026-08-17 attempts both declined to search below the bound in Liu's
Zenodo preprint, which neither could retrieve; that bound is still unknown
here.  By `leavitt-stable-finiteness-equals-direct-finiteness` any such search
may fix `n = 1`.
