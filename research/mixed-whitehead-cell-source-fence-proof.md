---
rg: 2
id: mixed-whitehead-cell-source-fence-proof
kind: route
title: Conjugate the g-star cells by the simultaneous partial swap and compute the signed intersection
target: mixed-whitehead-cell-moves-signed-source
requires:
  - positive-signed-actor-two-scale-profile-is-partial-and-gauged
  - endpoint-whitehead-signed-source-has-only-relative-hecke-overlap
---

Prefix cancellation gives

```text
c_2d_2=e_3,             d_2c_2=e_2.                   (1)
```

The standard three-elementary partial-Whitehead calculation therefore makes
both `P` and `J` involutions.  Their coordinate pairs are disjoint, so they
commute and `H^2=1`.  Conjugation by `P` carries
`A_(2,2)` to `A_(4,3)` and the endpoint root `x_23(b_2)` to
`x_43(b_3)`.  Conjugation by `J` carries `Y_2` to `Y_3`.  Simultaneously
moving the target pair `(2,4)` and source pair `(8,9)` fixes the matching
matrix

```text
g_*-1=E_(2,8)+E_(4,9),                                (2)
```

which proves `(SMP2)`.

Direct cross commutators give zero because the two `Y` roots have a common
source, the two `A` roots have a common target, and each opposite cross pair
has disjoint indices.  Thus the prescribed cross and common-tail menu adds
only commutation and the swap already recorded in `(SMP2)`.

For the source calculation, conjugate all `8192` constant actor matrices by
the faithful Leavitt matrix of `H`.  Exactly `16` images are again elements
of `L_0`; all are fixed pointwise by `H`, and the signed character has eight
positive and eight negative values on them.  This proves `(SMP3)`.  The
finite-character intersection formula gives `(SMP4)`.

The finite abelianization audit finds `32` characters trivial on `K`,
including the character supported only on the second displayed generator
`5->4`.  Diagonalize `L_0` by `lambda_0` and
`lambda_0` times this character, and let the chart involution swap the two
summands.  Since the two characters agree on `K`, every relation in
`(SMP3)` holds, while their signed projections are orthogonal.  This proves
`(SMP5)` and the claimed two-chart profile fence.  Reversing the two
multiplicity gauges on the second chart makes the same swap implement every
relation `(SMP2)` without identifying the two restrictions on the first
chart.
