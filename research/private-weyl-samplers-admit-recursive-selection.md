---
rg: 2
id: private-weyl-samplers-admit-recursive-selection
kind: claim
title: Good private Weyl samplers admit a recursive lexicographic selection
distinct_from:
  private-random-weyl-sampler-forces-growing-matrix-dimension: that proves a good finite sample exists probabilistically at every level; this removes randomness/nonconstructivity by deciding the finite sample property.
  uniform-halting-pauli-word-oracle: that asks for bounded-area words realizing the selected vector labels and additive decoder; this only computes the finite label/sign lists.
---

Fix rational constants strictly inside the gap supplied by
`private-random-weyl-sampler-forces-growing-matrix-dimension`.  There is an
algorithm which, on input `r`, outputs a finite private pair list satisfying
the matrix-valued sampled Weyl lower bound simultaneously for every
dimension `d<=r`.

For a candidate list and fixed `d`, an exact representation of `F_2^r` is a
finite list of `d` characters together with a conjugating unitary.  Enumerate
the two finite character lists.  Write the real and imaginary entries of the
relative unitary `W` as real variables.  Unitarity is a finite family of
polynomial equations, and the assertion

```text
sampled normalized-HS energy >= eta
```

is a polynomial inequality with rational coefficients after clearing the
normalizing denominator.  Its universal validity on `U(d)` is decidable by
quantifier elimination over real closed fields.  There are finitely many
character lists and finitely many `d<=r`, so goodness of one candidate is
decidable.

Enumerate all pair lists of the prescribed finite length lexicographically
and return the first good one.  The probabilistic existence theorem proves
termination.  Thus the sampler vectors, signs, and private matching are a
recursive family; no effective randomized construction or complexity bound
is needed.

This removes existential sample selection as a compiler gate.  It does not
give bounded-area group words for the selected vectors, nor round approximate
same-basis relations to exact additive actions.  The sole remaining interface
is `same-basis-rounding-interface-for-sparse-weyl-sampler` and its finite-
presentation realization.
