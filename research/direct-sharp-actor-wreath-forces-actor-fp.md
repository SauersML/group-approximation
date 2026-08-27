---
rg: 2
id: direct-sharp-actor-wreath-forces-actor-fp
kind: claim
title: Finite presentation of the direct sharp-actor lamp group forces finite presentation of the actor
distinct_from:
  augmentation-actor-semidir-is-not-fp: that uses the classical regular-wreath theorem for an already finitely presented acting group; this applies to any transitive action and isolates the actor quotient obstruction.
  sharp-two-t-actor-gives-fp-host: that gives sufficient hypotheses for the lamp host; this gives a necessary actor finiteness hypothesis for the direct construction.
---

Let a group `A` act transitively on `X`, let `1!=K` be finitely generated,
and put

```text
W=K^(X) semidirect A.                                      (DAW1)
```

If `W` is finitely presented, then `A` is finitely presented.

Choose a finite generating set of the root lamp `K_x`.  Transitivity says
that its normal closure in `W` is the entire lamp base.  Hence `A` is the
quotient of `W` obtained by adjoining finitely many relations killing those
root-lamp generators.  A finitely presented group modulo the normal closure
of finitely many elements is finitely presented, proving the claim.

Consequently the André--Guirardel actor cannot be inserted directly into a
finitely presented binary lamp semidirect product merely from its published
finite generation.  The missing finite presentation is logically necessary,
not an artifact of the standard permutational-wreath criterion.

The same obstruction applies to any proposed finite-presentation
compression from which the direct lamp semidirect product is recovered by
killing finitely many extra generators.  An fp envelope can evade it only by
changing the acting group/action while retaining the property-`(T)` actor as
a subgroup whose permutation dynamics still control the seed-visible
characters.
