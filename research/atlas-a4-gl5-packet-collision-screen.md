---
rg: 2
id: atlas-a4-gl5-packet-collision-screen
kind: claim
title: The standard GL5(F2) extension has 202 exact A4-packet models, all killed by 19243
invalidates:
  - nonhyperlinear-from-centralizer-product-classicalization
artifacts:
  - experiments/atlas_a4_gl5_packet_screen.py
  - experiments/atlas-a4-gl5-two-holonomy-profile.json
distinct_from:
  atlas-a4-classical-mixture-trace-separator: that exhausts the 40,320 automorphism alignments inside A8 itself; this screen lets the second standard A8 copy move through every one of the 9,999,360 elements of GL5(F2), so it tests genuinely larger finite relative positions.
  atlas-a4-19243-parabolic-subgroup-ladder: that identifies subgroup geometry internal to the chart A8; this computes all exact packet solutions in one ambient rank-five finite linear group and shows collision 19243 kills every one.
---

Embed

```text
H = GL4(F2) = A8
```

as `diag(GL4(F2),1)` in `G=GL5(F2)`.  For `h in G`, represent the two atlas
charts by the standard copy `H` and its conjugate `h H h^-1`, with the chart
labels transported by `h`.

Then exactly **202** elements `h in GL5(F2)` satisfy all thirty shortest A4
pair-cubes from `atlas-shortest-a4-triangle-packet`.  They lie in exactly 25
of the 496 right cosets of `H`.  Their chart-intersection sizes are

```text
|H intersect hHh^-1| = 20160   for 30 solutions,
                       1344   for 54 solutions,
                        168   for 118 solutions.       (GL5-A4-1)
```

For every one of these 202 exact packet solutions, collision `q_19243` is
**nonidentity**.  More precisely its order in `GL5(F2)` is

```text
2  in 157 cases,
4  in  45 cases.                                      (GL5-A4-2)
```

The joint distribution is

```text
intersection 168:    q-order 2: 88,  q-order 4: 30,
intersection 1344:   q-order 2: 44,  q-order 4: 10,
intersection 20160:  q-order 2: 25,  q-order 4:  5.
```

Consequently there is no relative position of the two standard conjugate
`A8` copies inside `GL5(F2)` which realizes the thirty A4 packet relations and
collision 19243 simultaneously.

The same exhaustive list also admits a quantitative two-holonomy calibration
in the 31-point permutation representation.  See
`atlas-a4-gl5-two-holonomy-readout`: on all 202 packet positions,

```text
E_2HOL <= 5 ||q_19243-1||_2^2,
```

with equality at 96 positions.  This is fixed-rank evidence for the desired
collision readout, not an amplified-regular theorem.

### Packet-only classicalization is false

The same 202 solutions are exact countermodels to
`atlas-thirty-centralizer-products-classicalize` as it was originally stated.
Take the left-regular representation of `GL5(F2)`.  Its restriction to either
standard/conjugate `A8` is

```text
496 Reg(A8),
```

so every solution gives an exact regular-margin relative chart model satisfying
all thirty A4 constraints, hence all thirty corrected shifted centralizer-
product memberships.  For the 172 solutions with intersection size `1344` or
`168`, the second `A8` is not the same chart subgroup and the relative position
is not one of the finite inner/outer `A8` packet alignments (even modulo the
global regular-chart commutant).

Therefore the thirty packet constraints **alone cannot force one classical
alignment branch**.  Collision 19243, or an equivalent interior condition,
must be part of the joint classicalization hypothesis.  This invalidates the
route `nonhyperlinear-from-centralizer-product-classicalization`, whose open
premise omitted collision from the classicalization step.

The three intersection sizes are notable because they are exactly the orders
of the chart `A8`, the affine parabolic `AGL3(F2)`, and the rank-three core
`GL3(F2)` already appearing in `atlas-a4-19243-parabolic-subgroup-ladder`.
This is evidence that the finite packet is detecting the same parabolic
stratification in the first ambient rank enlargement rather than producing an
unstructured family of finite escapes.
