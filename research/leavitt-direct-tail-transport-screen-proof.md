---
rg: 2
id: leavitt-direct-tail-transport-screen-proof
kind: route
title: Enumerate unary pivots and trivalent gate pairs in the cyclic covers
target: leavitt-direct-tail-transport-screen-is-empty
requires:
  - leavitt-revised-degree4-candidate-is-injective
---

## Compiler criterion

In a degree-`m` cyclic cover, suppose two unary orbit relators have coefficient
corners `X,Y`.  Both become `z^(-1)` in the abstract Tietze quotient.  If two
trivalent orbit relators have singleton corners `a,c` and `b,d`, respectively,
and their third corners equal either `X` or `Y`, then their terminal `z` factors
cancel against the unary corners.  They force

```text
c=z a z^(-1),       d=z b z^(-1),
```

up to simultaneous reversal.  The source identity `[a,b]=1` would then kill
the exact target `[c,d]!=1`.  This is the cleanest possible redesign of the
fenced degree-four word.

## Exact fixed-packet screen

The first artifact enumerates all `C(8,2)=28` sign patterns of length eight
and exponent sum four, and all `8!=40,320` arrangements of

```text
(r,e,a,c,1,b,d,p).
```

It performs exact free-product/Bergman reduction of every orbit corner and
allows the two nonlinear tails to match either unary corner.  Its MSI output
is

```text
tested 1128960
structural_tail_collisions 0
transport_hits 0.
```

Thus no mere sign or coefficient rearrangement of the actual short packet
multiset realizes the compiler.

## Sparse repeated-tail screens

The second artifact replaces the coefficient multiset by source/target gates
`a,b,c,d`, repeated copies of one abstract involution `x`, and identities.
Equality is decided in the free product of the `m` abstract packet copies, so
the screen tests pure corner geometry without making an accidental finite
Leavitt quotient.  The disjoint MSI runs are

```text
degree 4, length 8, x-count 2,3,4:   517440 layouts;
degree 4, length 10, x-count 2:      9072000 layouts;
degree 5, length 9, x-count 2:       1088640 layouts;
degree 6, length 10, x-count 2:      3402000 layouts.
```

Every run reports `transport_hits 0`.  This is a bounded family theorem, not a
no-go for arbitrary words.  It excludes the direct compiler through the first
three nontrivial degrees and shows that the next design must introduce a
higher-valence dependency rather than another freely solvable tail.
