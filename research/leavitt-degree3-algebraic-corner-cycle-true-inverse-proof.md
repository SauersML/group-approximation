---
rg: 2
id: leavitt-degree3-algebraic-corner-cycle-true-inverse-proof
kind: route
title: Replay every algebraic corner collision with true inverses
target: leavitt-degree3-algebraic-corner-cycle-is-absent
requires:
  - leavitt-d4-true-inverse-screen-audit
  - leavitt-degree3-formal-corner-cycle-is-absent
  - leavitt-degree3-direct-pivot-screen-is-empty
artifacts:
  - research/artifacts/search-leavitt-degree3-postpivot-true-inverse.py
---

There are exactly eleven length-eleven exponent-three sign paths whose three
Reidemeister--Schreier orbit valences are `(1,1,9)`.  For each path the
corrected verifier enumerates all

```text
11!/4! = 1,663,200
```

placements of the full packet `(r,e,a,c,1,b,d,p,1,1,1)`.  It forms the two
unary orbit corners `H,Y`, records both symbolic orientations of each, and
tests every corner of the actual reduced nine-valent orbit against

```text
H, H^(-1), Y, Y^(-1).
```

This last qualification is essential.  Identity coefficients can join, or
cancel, adjacent powers of `z=t^3`; hence the index and even the shape of the
formal three-letter corner need not survive in the actual word.  The verifier
therefore constructs the corners only after identity deletion and `z`-power
collection and checks all of them.  A layout is discarded by the formal
peeling theorem only when no actual target corner collides with any of the
four unary orientations.

All coefficient inverses are genuine multiplicative inverses.  The verifier
first asserts `x*x_inverse=1=x_inverse*x` for every named generator in the
faithful Bergman chart.  It then forms the inverse of a symbolic corner by
reversing the word and negating its exponents before chart evaluation; it
never uses transposition as inversion.  Exact free-product normal forms are
used throughout, with no hashing or finite-quotient filter.

All eleven shards completed normally.  Each owned one topology and reported

```text
layouts 1663200 pivots 3326400
collision_pivots 0
hits 0
```

Thus the exhaustive corrected census contains

```text
18,295,200 coefficient layouts,
36,590,400 oriented unary pivots,
```

and no actual target-corner collision at all.  In particular the post-pivot
two-relator family has no nonempty long-corner two-core.  By
`leavitt-two-relator-corner-peeling`, the marked coefficient group embeds, so
its central involution cannot be killed.  This proves exactly the finite
degree-three, length-eleven target claim and replaces the invalidated
transpose-as-inverse route without erasing that audit history.
