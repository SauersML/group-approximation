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

The certificate attack is running.  The chain
`GreendlingerCombinatorics` -> `Conjugation` -> `NormalForm` ->
`OneRelator` -> `Expression` -> `Cancellation` -> `Descent` -> `Piece`
puts every factor of an expression in palindromic normal form, decomposes
the product of two reduced words into a single matched block, and reduces
the descent's second case to the identification of the eaten overlap as a
piece.  `GreendlingerOverlap` pays that identification: the overhang of one
conjugator past the other positions the overlap inside the next rotation,
and if the relator it lands in is the very one it was eaten out of, the two
palindromes spell mutually inverse elements
(`mk_palindrome_mul_eq_one_of_coincidence`).  `GreendlingerMinimal` supplies
the missing negation from minimality of the expression — a shortest
expression has no two factors whose product is trivial — so the overlap is a
piece unconditionally, and the two-factor case of the gate closes
(`greendlinger_of_isMinimalConjProduct_two`).  `GreendlingerMirror` records
the duality under the formal inverse and covers the opposite conjugator
ordering plus the free case at the far end.

The length regime is now discharged too.  `GreendlingerSlide` proves the
re-expression identities a conjugate admits --- a relator may be rotated at
the price of moving the conjugator --- and `GreendlingerWeight` makes an
expression *data*, with the total conjugator length as a second minimand,
so that minimality in (count, weight) is a well-founded object.  Each way
the destroyed block could swallow a rotation is then either a re-expression
that strictly shortens the total conjugator length (absorb, slide, meet), a
relator that would be a piece of itself, or a coincidence making the two
factors mutually inverse; `GreendlingerRegime` walks the six cases and
closes the two-factor case of the gate outright
(`greendlinger_of_le_two_factors`, no hypotheses).

What remains is one thing: the induction from `n >= 3` down to two factors.
`GreendlingerInduction` states it sharply --- the gate follows from the
three-or-more-factor case alone (`greendlingerConclusion_of_three_factor`)
--- proves the structural facts it runs on (the tail and the leading pair of
a minimal expression are minimal), and names the strengthening the induction
needs: the *two disjoint pieces* of Greendlinger's lemma proper, which the
one-piece conclusion cannot supply because the next factor can eat exactly
the relator the previous step produced.  That strengthening is what classical
treatments obtain from a reduced van Kampen diagram.
