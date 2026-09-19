---
rg: 2
id: greendlinger-free-product-lemma
kind: claim
title: Greendlinger's lemma for C'(1/6) families, over free groups and free products
distinct_from:
  bespoke-routing-lemma: that claim asserts a routing lemma's conclusion list SUFFICES for DefectRoutingData (now machine-checked); this one is the combinatorial engine itself — the metric small-cancellation theorem the router's construction will run on.
  common-quotient-onto-normal-subgroup: that is the general acylindrically-hyperbolic common-quotient tool imported from the literature; this is the elementary normal-form statement the bespoke route uses INSTEAD of that theory, provable by Greendlinger's reduced-diagram count or Dehn-reduction induction with no geometry.
artifacts:
  - GroupApproximation/Sofic/SmallCancellationRouter.lean
---

Classical metric small cancellation, in the two forms the bespoke router
needs.  Free-group form: every C'(1/6) family of cyclically reduced
relators satisfies the Greendlinger conclusion — every nonempty reduced
word representing an element of the normal closure of the relators
contains, as a contiguous subword, more than half of some symmetrized
relator.  This is exactly the predicate `GreendlingerGate` frozen in
`SmallCancellationRouter.lean`, whose consequences
(`norm_bound_of_greendlinger`, `injOn_mk'_of_greendlinger`,
`protected_injOn_of_gate`) are already kernel-checked from the
conclusion alone.  Relative form: the same statement over the normal
forms of a free product (Mathlib's `Monoid.CoprodI.Word` syllables in
place of letters), which is the version applied to the HNN source and
the Kazhdan partner in the router's intended construction, together
with its standard companions — the torsion theorem (every finite-order
element of a C'(1/6) quotient of a free product is conjugate into a
factor) and preservation of finite presentation.  Everything here is
elementary combinatorics of words and reduced diagrams; no
acylindrical hyperbolicity, no geometry of the hyperbolic plane beyond
Greendlinger's count.

## Attempts

The textbook attack — Greendlinger's count over reduced van Kampen
diagrams — dies at the door in Lean: Mathlib has no diagram theory, no
planar combinatorics, and building one is a larger project than the
lemma deserves.  The attack to run instead is certificate-based: an
element of the normal closure comes with an expression as a product of
conjugated symmetrized relators; induct on the number of factors with
minimal total letter length, and show a shortest certificate for a
reduced word with no long relator subword forces a cancellation that
shortens the certificate — pure `List` bookkeeping over
`FreeGroup.reduce`, no planarity.  Where it will hurt: the
minimal-certificate cancellation analysis is the diagram argument in
disguise, and the piece bound enters through a case count that is easy
on paper and long in lists.  Deferred, not blocked: the interface
(`GreendlingerGate`) is frozen in `SmallCancellationRouter.lean` and
every consumer is already checked from the conclusion alone, so this
card can be attacked in isolation with zero downstream rework.
