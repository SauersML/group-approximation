---
rg: 2
id: amalgam-torsion-permanence-needs-no-cyclic-reduction
kind: claim
title: Torsion-freeness of an amalgamated free product is unconditional in-repo, and the universal cyclic-reduction statement it was gated on is not reachable from that argument
distinct_from:
  omega-input-reduces-to-mikaelian-tower: that lane needed no amalgam at all once the notation was read correctly; this is the lane that did need one -- the image half of Higman's Lemma 3.3 -- and it is now closed.
artifacts:
  - GroupApproximation/Algebra/PushoutITorsionFree.lean
  - GroupApproximation/Higman/AmalgamTorsion.lean
  - GroupApproximation/Higman/TorsionFreeImageClosure.lean
---

An amalgamated free product of torsion-free groups is torsion-free, proved
outright: `PushoutITorsionFree.isPowerTorsionFree_pushoutI_of_nonempty`, by
running the induction on syllable length over `Monoid.PushoutI.NormalWord`.
The base group needs no hypothesis of its own, since it embeds in a factor.

This closes the last analytic debt of the benign theory's image half.  Higman's
Lemma 3.3 builds its witness as an amalgam `K *_G N`, which is why
`BenignTF.mapEmb` could not carry the torsion clause before; it now can, and
`Seq.torsionFreeImageClosure` is a theorem.  Downstream, Higman's operation
`rho` is no longer an input at all.

## The statement it was gated on, and why that gate was deleted rather than proved

The gate was: **every** element of an amalgam is conjugate either into a factor
or to the product of a cyclically reduced word.  Nothing ever inhabited it, and
it is not reachable from the induction that closed the theorem:

- the induction only ever needs to **rule out** a cyclically reduced word,
  which the finite-order hypothesis does, through
  `pow_ne_one_of_cyclicallyReduced`;
- the universal form has to **produce** one, and its hard case is a merged
  letter landing in the base, after which the base element must be pushed
  leftwards through the word --- and in an amalgam, unlike a free product, that
  rewrites every letter it passes.

So the universal form is strictly stronger than anything the theorem needs.
The two gated definitions were removed on 2026-08-22 and the theorem restated
unconditionally, its `CyclicReduction` argument becoming `[Nonempty ι]`.

## What survives of the amalgam-specific work

The normal form does: the head base element of a normal word absorbs into the
first letter, so every element is a factor element or the product of a nonempty
reduced word.  That is the piece the `NormalWord` induction does not expose,
and it is worth keeping independently of the torsion question.
