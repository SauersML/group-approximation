---
rg: 2
id: signed-three-face-rstar-petal-proof
kind: route
title: Pull the unique R-star ghost back through three signed center coordinates
target: signed-three-face-rstar-petals-are-exact-cap-deletors
requires:
  - rstar-fano-ghost-affine-hull-criterion
---

For a fixed three-bit prefix `t`, odd parity determines the fourth petal bit
as `1+sum(t)`.  The resulting `R_*` tuple fails exactly at `t=100`.
The signs in `(TFP2)` make the prefix `100` equivalent to agreement with
`b` on the chosen three center coordinates.  The center parity equation
then forces agreement on the omitted coordinate, proving the singleton
deletion formula.

In a relational syntax permitting repeated variables, the
repeated-coordinate row `(TFP4)` cancels its first two entries in the parity
equation and cannot equal the ghost, proving the sign implementation there.
Independent petals intersect their singleton exclusions, giving `(TFP5)`.

Translate assignments by the ghost to identify them with the seven nonzero
vectors of `F_2^3`.  A deletion set hits every projective line exactly when
its complement is a cap, and the established Fano criterion gives `(TFP6)`.
If a three-point blocking set were not a line, its three translated vectors
would be independent; their three pairwise sums would form a line disjoint
from them.  Hence a three-point blocking set is a line, whose complement is
the other coset of its two-dimensional span.
