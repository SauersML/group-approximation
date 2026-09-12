---
rg: 2
id: deligne-maslov-mf-quotient-equivalence-proof
kind: route
title: Apply the twisted universal property and polar-correct corona lifts
target: deligne-maslov-opnorm-sector-is-mf-quotient
requires: []
---

An `alpha`-projective point-norm sequence sends each canonical twisted
unitary `u_g` to its class in a norm-matrix corona.  The multiplier
relations hold exactly in the quotient, so the universal property of the
full twisted group C-star algebra gives the unital homomorphism in clause 2.

The closed image of any such homomorphism is a nonzero unital quotient of
`A_alpha` embedded in a norm-matrix corona, hence is MF.  This proves
`2 => 3`.  Conversely, an embedding of a nonzero MF quotient into a
norm-matrix corona, composed with the quotient map, gives clause 2.

For `2 => 1`, lift the image of each canonical twisted unitary to a bounded
matrix sequence.  The lifts are asymptotically unitary in operator norm;
polar correction changes them by `o(1)` and makes every coordinate exactly
unitary.  The twisted multiplication relations then give the required
pointwise projective defects.  A diagonal enumeration handles the
countable group.

Finally the lift of `-I` is a central involution in `A_alpha`.  Its two
central spectral projections sum to the unit.  Any unital corona image is
nonzero on at least one projection and restricts to a nonzero MF quotient
of that full-central-character fibre.  Conversely such a fibre quotient is
a quotient of `A_alpha`.  This proves the final equivalence.
