---
rg: 2
id: atlas-three-transverse-shears-counting-proof
kind: route
title: Count the degenerate affine characters of the full rank-five transverse star
target: atlas-three-transverse-shears-leave-fifteen-character-types
requires:
  - atlas-two-transverse-shears-have-determinant-balance-test
  - atlas-steinberg-rank-five-translation
  - atlas-steinberg-spare-index-independence
---

The three literal row families are `st3_12r_a1`, `r=3,4,5`.  Steinberg
(St2) says the actors commute, their target roots commute, and each actor
centralizes the entire target-root star.  The one-shear calculation therefore
extends verbatim with exponent vector `k in F_2^3`, proving
`(3TS4)--(3TS5)`.

The equations have a common solution precisely when the linear functional
`u` is nonzero on `ker(w)`.  Since

```text
ker(w)^perp=span{w},                                    (3TR1)
```

this is `(3TS6)`.  Its failure count is elementary: for `w=0`, only `u=0`
fails; for each of the seven nonzero `w`, exactly `u=0` and `u=w` fail.
Thus `1+7*2=15` of `2^6=64` pairs `(u,w)` are degenerate.

The roots at positions `(1,3),(1,4),(1,5)` commute.  At each position the
two coefficient roots for the linearly independent idempotents `p,q`
generate `C_2^2`; products across the three positions remain nontrivial
after mapping to the elementary matrices, so the combined subgroup is
`C_2^6`.  Restriction of the canonical group trace to a finite subgroup is
its regular character, proving `(3TS8)`.  Adding the two independent source
roots gives a commuting `C_2^8`; exactly half of its source characters have
product sign `x_12(p)x_12(q)=x_12(1)` negative.  This proves `(3TS9)`.

For the label calibration, the three coefficient-one target transvections
are independent commuting involutions in the finite `A8` chart.  Restricting
the left regular `A8` representation to their `C_2^3` subgroup gives a
multiple of its regular representation, so each joint sign, in particular
the common positive sign, has trace `1/8`.

Finally, on a degenerate target character, marked-preserving exponent vectors
lie in `ker(w)` and annihilate `u`.  Therefore the two marked branch
orientations lie in distinct affine orbits.  The permutation representation
of either orbit is the asserted exact local countermodel.  This proves a
no-go only for the full three-shear star, not for packet rows involving roots
outside that finite affine subgroup.
