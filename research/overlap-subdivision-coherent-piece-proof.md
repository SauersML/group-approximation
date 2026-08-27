---
rg: 2
id: overlap-subdivision-coherent-piece-proof
kind: route
title: Separate macro overlap girth from the coherent coefficient link
target: overlap-subdivision-preserves-coherent-piece-obstruction
requires:
  - coherent-four-potential-pairings-cannot-be-long-c-sixth
  - term-pairing-does-not-bypass-signed-hecke-holonomy
---

For a chain `Z_0,...,Z_L`, telescoping in normalized Hilbert--Schmidt norm
and Cauchy--Schwarz give

```text
||Z_0-Z_L||_2^2
 <= (sum_k ||Z_(k-1)-Z_k||_2)^2
 <= L sum_k ||Z_(k-1)-Z_k||_2^2.
```

Adding the unchanged local constraint energy proves the stated
`gamma/L_max` lower bound.  Exact equivalence is transitivity in one
direction and the constant lift in the other.

In the coherent signed-Hecke parametrization, subdivision never changes the
endpoint formula `y_ij h_i h_j^(-1)E_ij`.  It only replaces its old partner
by a term at the first new path vertex.  Every vertex on a subdivided cycle
has two incident segment equations, so the four potential occurrences in
each endpoint/segment pairing remain recurrent on the cyclic core.  Apply
`coherent-four-potential-pairings-cannot-be-long-c-sixth` separately to that
local relator.  Its estimate contains no macro path length.

For the proposed one-relator alternative, the last fresh path letter occurs
once with exponent `+1` or `-1`; solve the relator for it and perform the
corresponding Tietze elimination.  Hence the long contour is semantically
empty until further relations reuse the path letters.  Exact segment
equalities are one such reuse and restore the preceding recurrent local
contours.

Finally, the four-piece count does not contradict `C(4)` by itself, so no
claim against every `C(4)-T(4)` redesign is made.  What subdivision controls
is the macro incidence girth.  `C(4)-T(4)` must instead be checked in the
piece link of the actual symmetrized coefficient relators; the former gives
no implication to the latter.
