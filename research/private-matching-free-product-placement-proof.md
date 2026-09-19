---
rg: 2
id: private-matching-free-product-placement-proof
kind: route
title: Put each private pair on one shift translate of two sign prototypes
target: private-matching-free-product-separates-pauli-signs
requires: []
---

Reduced-word normal form in `F(s,p_0,p_1)` proves all assertions in `(PMF2)`:
different powers of `s` are distinct, and
`s^t p_b=s^u p_c` forces `t=u,b=c`.  It also separates the two singleton sign
double cosets.

Conjugating the prototype commutator in `(PMF5)` by `s^t` gives `(PMF4)`
exactly, so address length costs no relator cells.  Since every endpoint occurs
on only its matched edge, there is no alternating X/Z contour and hence no
relative piece to estimate.

For exact completeness, take the binary vector space on the left A-orbit and
its algebraic dual on the right A-orbit, with invariant pairing supported on
`(g,gp_1)`.  Its Heisenberg representation has common central sign `J=-I` and
realizes `(PMF5)`.  Finally, lexicographic search over finite sample lists is
recursive because, after enumerating the two finite character lists, goodness
is a universal polynomial inequality on one relative unitary group and is
decidable by real quantifier elimination.
