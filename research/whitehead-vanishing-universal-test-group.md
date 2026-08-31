---
rg: 2
id: whitehead-vanishing-universal-test-group
kind: claim
title: The Whitehead group of the universal finitely generated torsion-free test group vanishes
distinct_from:
  whitehead-vanishing-torsion-free: that is the global conjecture over all torsion-free groups; this is one computation for one explicitly constructed group. They are equivalent, and the equivalence is the point -- but this form is a packaging device, not a weaker target.
  whitehead-vanishing-recursively-presented-torsion-free: that restricts the global statement to a countable class of groups and is a genuine reduction in difficulty of the *class*; this concentrates the whole statement into a single group without reducing anything.
  torsion-free-finitely-presented-non-mf: that asserts a finitely presented torsion-free group fails MF; this asserts the Whitehead group of one explicit uncountable restricted product vanishes. Different group, different invariant, no approximation content.
  torsion-free-countable-non-mf: that asks for a countable torsion-free group failing MF; the group here is deliberately *not* countable and the assertion is a K-theoretic vanishing rather than an approximation failure.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Let

    I    = { (n, N) : N normal in F_n and F_n/N is torsion-free }
    Ufg  = (+)_{(n,N) in I} F_n/N          (restricted direct product)

be the restricted direct product of one copy of every finitely generated
torsion-free group.  `Ufg` is torsion-free: an element has finite support and
a finite power of it is trivial only if the corresponding power is trivial in
each torsion-free coordinate.  The index set is a set, though not a countable
one, and nothing here claims countability.

**Claim:** `Wh(Ufg) = 0`.

## Read this before attacking it

This is *equivalent* to `whitehead-vanishing-torsion-free`, not easier.  Each
coordinate has an inclusion and a projection with `p . i = id`, so
`Wh(H) -> Wh(Ufg)` is split injective for every finitely generated
torsion-free `H`; the whole difficulty is preserved as a split summand rather
than removed.  The formula is a packaging device: it makes the conjecture
literally one computation for one explicit torsion-free group, which is worth
stating exactly once and is why this node exists, but it supplies no method.

The contrapositive is the useful half.  If the conjecture is false it already
fails for a finitely generated torsion-free group
(`whitehead-class-supported-on-finitely-generated-subgroup`), and that
group's nonzero class embeds split-injectively in `Wh(Ufg)`.  So a
counterexample search may always assume finite generation.

The repository's `UniversalFinitelyPresentedTorsionFreeGroup` is the
*finitely presented* coded analogue of this construction, and the same split
argument applies to it -- but it absorbs finitely presented torsion-free
groups only, and the reduction above delivers finitely generated ones.  That
mismatch is the subject of
`whitehead-vanishing-recursively-presented-torsion-free`.

## Finite tester upgrade

A stronger packaging theorem is now established in
[[whitehead-universal-finitely-presented-torsion-free-group]]: there is a
single finitely presented torsion-free U such that Wh(U)=0 is equivalent to
this claim and to the global conjecture. That does not establish vanishing;
it replaces this node's uncountable restricted product by a finite
presentation without losing any Whitehead class from the finitely presented
case.

## Attempts

**Compute it directly.**  `K_1` commutes with directed colimits of rings, and
`Ufg` is the directed colimit of its finite sub-products, so

    Wh(Ufg) = colim_F Wh( (+)_{i in F} G_i )

over finite `F`.  That much is free.  *Dies* one step later: `Wh` of a finite
direct product of torsion-free groups is not assembled from the factors'
Whitehead groups, and already for `F` of size one the term is `Wh(G_i)` for
an arbitrary finitely generated torsion-free group -- the general case.  The
colimit reorganizes the conjecture without touching it.

**Exploit the coordinates.**  Each coordinate is a split summand, which is
what makes the statement equivalent to the global one rather than a
consequence of it.  There is no direction in which that splitting can be
used: it delivers the difficulty *into* the test group and offers nothing
coming back out.

**Deferred**, and it should stay deferred: this node is here to mark a
boundary, not to be worked on.  Anyone tempted by "the conjecture is one
computation" should read the two paragraphs above first.  The one genuinely
usable consequence is the contrapositive recorded above -- a counterexample
may always be assumed finitely generated.
