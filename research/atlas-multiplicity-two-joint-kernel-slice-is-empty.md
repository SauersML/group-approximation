---
rg: 2
id: atlas-multiplicity-two-joint-kernel-slice-is-empty
kind: claim
title: The F4-seeded multiplicity-two packet slice has no 19243-plus-q14 point
artifacts:
  - experiments/atlas_a4_repeated_module_probe.py
  - experiments/atlas_a4_repeated_module_dataset.py
  - experiments/atlas_a4_repeated_module_screen.cpp
  - experiments/atlas-a4-repeated-module-screen.json
distinct_from:
  atlas-l44-subfield-packet-collision-exclusion: that restricts the whole frame to GL4(F4); this enlarges each F4-seeded H6 lift to its complete GL8(2) multiplicity-gauge fiber.
  atlas-q14-adds-stratified-thirteenth-double-coset: that is an all-dimensional unitary normal form; this is an exact finite-field screen on one explicitly delimited multiplicity-two slice.
---

On `V tensor F2^2`, the centralizer of the marked H6 is of order `120960`
and the centralizer of the full A8 chart is `GL2(2)` of order six.  Hence each
H6 lift has exactly `20160` effective multiplicity gauges.  Starting from all
`1262` H6 rectangle lifts in the F4 seed cell gives `25441920` exact gauge
positions for each marking parity.

For inner parity, the H18 packet leaves `136728`; collision `19243` leaves
`5184`; q14 leaves `10044`; their joint zero set is empty.  For graph parity,
the corresponding counts are `136728`, `5184`, `5184`, and zero.  In both
parities the collision orders on the packet locus are

```text
1:5184,     2:65448,     4:66096.                     (M2J1)
```

The defect-rank spectrum sharpens the zero count.  In both parities every
collision-zero point has

```text
(rank(q_19243-I),rank(q_14-I))=(0,1),                 (M2J3)
```

while every q14-zero point has pair `(2,0)`.  Thus the minimum unweighted
rank sum is only one.  This finite calibration does not itself provide a
rank deficit proportional to multiplicity.

This is not an exhaustive classification of all H6 image pairs in GL8(2):
the `1262` base lifts are the F4-linear seed cell.  It is therefore a sharp
finite slice theorem, not an all-multiplicity q14-plus-collision identity.

Algebraically, for a seed lift `U_p` and a gauge
`C in C_GL8(rho(H6))/C_GL8(rho(A8))`, put `U=C U_p`.  Every packet residual
and kernel word is a matrix-valued Laurent polynomial in `(C,C^-1)`:

```text
R_(x,y)(C)=(rho(x) U^-1 rho(y) U)^3-I,
Q_w(C)=product_j L_j(U)-I,                              (M2J2)
```

where `L_j(U)` is a fixed first-chart letter or a conjugated second-chart
letter.  The screen evaluates the simultaneous zero sets of these literal
polynomials, quotienting only the six gauges which commute with the whole
chart.  Since collision already acquires `5184` new zeros at multiplicity two
while q14 removes them, the joint emptiness cannot be promoted from the
scalar/F4 result; nor does a degree-two PI explain it without an additional
identity.  Direct sums of `(M2E1)` give collision escapes at every even
multiplicity, but continue to violate q14 blockwise.

The two pure fibers also cannot be glued by an upper-Toeplitz domain wall.
`atlas-m2-kernel-phases-cannot-upper-toeplitz-stitch` shows that Laurent-word
evaluation retains their diagonal rank defects on every flag quotient.  A
possible Følner escape must therefore use a cyclic/non-flag-preserving gauge
or a genuinely new bulk phase, not an upper-triangular mixture of the two
observed zero fibers.
