---
rg: 2
id: boolean-predicate-central-phase-word
kind: claim
title: Every fixed Boolean predicate has a finite 2-group word computing its nonlinear phase
distinct_from:
  boolean-predicate-is-one-rank-jump: that reads a predicate from irreducible representation rank; this reads its algebraic normal form from a central projective phase.
  affine-auxiliary-control-flow-barrier: affine words in commuting involutions cannot compute conjunction; this uses iterated commutators in a nilpotent noncommutative 2-group.
---

Let `f:F_2^m -> F_2` have algebraic degree at most `r`. There is an explicit
finite nilpotent `2`-group `H_f`, coordinate word families, and a fixed central
involution word `W_f` such that in every assignment-coordinate irreducible
model `pi_a`,

```text
pi_a(W_f)=(-1)^(f(a)) I.                                  (BPC1)
```

For a monomial `prod_(i in S) a_i`, the corresponding factor of `W_f` is an
`|S|`-fold commutator.  Multiplying those central factors according to the
algebraic normal form of `f` gives `(BPC1)`.  The group, word length, and
representation dimensions depend only on the fixed predicate, not on a
matrix microstate dimension.

Because `H_f` is finite, flexible normalized-HS stability transports the
phase through approximate packet tables.  This local gadget does not by
itself force the phase to be nontrivial in the global tracial model.
