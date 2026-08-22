---
rg: 2
id: leavitt-d4-l14-eighteen-winner-profile-proof
kind: route
title: Rank, classify, and compile the eighteen-winner profile
target: leavitt-d4-l14-eighteen-winner-profile-has-two-classes
requires:
  - leavitt-d4-latin-triangle-reduction
---

MSI job `16684537` ran the generalized ranker with

```text
--length 14 --profile=---++-++++-+++ --balanced-only
--show-rank=9 --classify-rank=9
```

and returned

```text
rank 9: 18, rank 10: 927, rank 11: 6804,
rank 12: 19908, rank 13: 17109, rank 14: 3834.

CYCLIC_CLASSES ... 2
I(0;131): 9
N(0;131): 9
```

All counted systems are carrier-balanced.  The four literal corner orbits
have valences `(3,5,5,1)` before sorting, and the singleton orbit gives

```text
H=g9_0 g10_1 g11_0 g12_1 g13_2 g0_3 g1_2
  g2_1 g3_0 g4_1 g5_2 g6_1 g7_2 g8_3.
```

The compiler `compile-l14-profile18.py` independently reconstructs every
corner from the sign word by the ranker's integer-height algorithm and
asserts literal equality with its stored corners.  For each displayed class
representative it then checks that every arc is cyclically contiguous, that
the three arcs partition its face, and that each even target occurs once with
each sign.  If an arc word is `W=q^epsilon`, the even carrier is formed as
`W_+ W_-`; the boundary is
`W_1^epsilon1 W_3^epsilon3 W_5^epsilon5`.  Thus target elimination is literal,
not inferred from an abelian projection.

The resulting reduced free-product syllable counts are

```text
class       R0  R2  R4   K
N(0;131)    27  49  63  63
I(0;131)    27  35  59  81
```

Inversion in the compiler reverses the syllable order and reverses and
inverts each coefficient word.  No transpose surrogate is used.  These two
raw systems are therefore the complete next inputs to copy retraction,
all-maximal noncrossing forests, coordinate Tietze reduction, Q-first target
elimination, and primitive saturation.  This node only compiles the systems;
it makes no survival or nonhyperlinearity claim.
