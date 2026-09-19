---
rg: 2
id: atlas-a4-classical-opaque-star-sharp-constant-proof
kind: route
title: Match regular root spectra and sum the blockwise optimal conjugators
target: atlas-a4-classical-opaque-star-sharp-constant
requires:
  - atlas-a4-packet-alone-fails-opaque-star
  - atlas-a4-classical-collision-gap-one-fifth
artifacts:
  - experiments/atlas_a4_opaque_star_regular_screen.py
---

The exact `F2` screen evaluates the four group elements

```text
alpha(t)t^-1,       t in T,
```

on all sixty packet alignments.  Their order profiles use only the orders
`2,3,4`.  Every leaf/hub pair either has equal order or is one of the pairs
`(2,3)` and `(2,4)` (up to reversal).  Equal orders give identical regular
spectra and hence conjugacy distance zero.

For orders two and four, the normalized regular spectral measures are

```text
mu_2=(delta_1+delta_-1)/2,
mu_4=(delta_1+delta_i+delta_-1+delta_-i)/4.
```

Optimal spectral matching keeps one quarter of the mass at each of `1,-1`
fixed and moves the two remaining quarters through squared chordal distance
two.  The minimum squared Hilbert--Schmidt orbit distance is therefore one.

For orders two and three, match one third of the mass at `1`.  Match one
quarter of the remaining mass at `-1` to each primitive cube root, at squared
distance one, and split the remaining one-sixth mass at `1` equally between
the primitive cube roots, at squared distance three.  Again the total cost is

```text
(1/2)*1+(1/6)*3=1.
```

Thus every nonzero leaf/hub orbit distance in the screen is exactly one.
`atlas-a4-classical-collision-gap-one-fifth` says collision `19243` is
nonidentity on all sixty packet alignments.  A nonidentity group element has
regular trace zero, so

```text
||lambda(q_alpha)-1||_2^2=2.
```

The screen also shows that every hub group element is nonidentity.  Hence its
distance from one is also `sqrt(2)`.  This proves `(A4-CL-STAR)` and
`(A4-CL-HUB)`, and the displayed order-mismatch sectors prove sharpness.

Finally take an arbitrary finite direct sum, allowing any multiplicity for
each sector.  On every leaf, use the direct sum of the blockwise optimal
conjugators.  Squared normalized-HS distance is the weighted sum of the block
distances, each at most one.  Meanwhile every collision block has squared
defect two, so the full direct sum still has collision squared defect two.
Therefore the global transport ratio is at most `1/sqrt(2)`.  Each hub block
and each collision block has squared defect two, proving the hub equality.
Tensoring by identity matrices changes none of these normalized quantities.
