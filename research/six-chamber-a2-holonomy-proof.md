---
rg: 2
id: six-chamber-a2-holonomy-proof
kind: route
title: Complete the six Heisenberg chambers to SL3(F5) and evaluate the Coxeter holonomy
target: six-chamber-a2-holonomy-closes-fixed-clock-sector
requires: []
---

List the six ordered chambers around the `A_2` Coxeter hexagon.  Their local
Heisenberg relations, together with additivity and commuting walls, are the
non-opposite-root Steinberg relations over `F_5`.  The simple transition
words are the standard signed Weyl elements, and the circuit word is
`(n_12n_23)^3`.  It is the identity in `SL_3(F_5)` and has no central lift
because `K_2(F_5)=0`.

Thus all six exact packets form one finite Chevalley reservoir.  Dyadic
scaling is inner there, by `diag(2,1,3)`.  Any lifted scaling unitary differs
from that slot by a full-reservoir commutant unitary; Weyl conjugacy keeps the
corrector common and the rank-two diagonal relation forces it to one.  Fixed
finite-group Hilbert--Schmidt exactification, averaging, and word telescoping
make the argument dimension-uniform for the fixed packet.
