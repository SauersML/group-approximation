---
rg: 2
id: atlas-central-c3-directed-gl5-classification
kind: claim
title: The central-C3 A4 contexts split into two directed K2,2 blocks with an exact GL5 asymmetry
artifacts:
  - experiments/atlas_a4_gl5_packet_screen.py
  - experiments/atlas_a4_gl5_core_collision_countermodel.py
  - research/artifacts/atlas-a4-central-c3-directed-gl5-classification.json
distinct_from:
  atlas-14-core-q19243-gl5-countermodel: that refutes the fourteen-context collapse with a point satisfying none of the central-C3 contexts; this classifies all GL5 core-plus-collision points by the omitted constraints and gives a second point satisfying one whole directed half.
  atlas-a4-gl5-packet-collision-screen: that classifies the 202 full-packet GL5 positions and proves collision nontrivial there; this starts from the 216 collision-zero core positions and identifies exactly which transverse contexts exclude them.
---

Write the two nonidentity elements of the central `C3` in the large packet
component as `Z={z,z^-1}` and its two packet involutions as `B={b_0,b_1}`.
The sixteen contexts deleted in `atlas-a4-rank-three-core` are eight distinct
equations, each occurring at two tree indices.  For a relative chart frame
`U`, they are exactly

```text
D_12: [rho(zeta) U rho(beta) U*]^3=1,  zeta in Z, beta in B,
D_21: [rho(beta) U rho(zeta) U*]^3=1,  beta in B, zeta in Z. (A4-C3-DIR)
```

Thus the omitted incidence is two directed copies of `K_(2,2)`.  Independent
interchange of the two `Z` labels and the two `B` labels is transitive on each
copy, so one equation from `D_12` and one from `D_21` are the two minimal
directed label-orbit representatives.  Chart direction cannot be quotiented
out after collision `19243` is fixed: its finite behavior is asymmetric.
This is a combinatorial orbit statement, not a claim that one relation
implies the other three.  `a4-triangle-propagates-inverse-c3-edge` shows that
one edge automatically gives the edge with `zeta` inverted, so each directed
block needs at most two algebraic representatives, one for each `beta`.
Propagation between `b_0` and `b_1` remains additional content.

Indeed, exhaust all `9,999,360` relative matrices in `GL_5(F2)` between the
two standard `GL_4(F2)` charts.  Exactly 216 matrices satisfy the fourteen
core constraints and `q_19243=1`.  Number bits `0,...,3` by the four `D_12`
equations and bits `4,...,7` by the four `D_21` equations.  Their exact
satisfaction-mask histogram is

```text
0x00 : 54,      0x30 : 34,      0xc0 : 34,      0xf0 : 94. (A4-C3-GL5)
```

Consequently no collision-zero core point satisfies even one `D_12`
constraint.  Any single one of the first four distinct constraints excludes
the entire GL5 core fiber.  Conversely the reverse direction does not force
return to the full-packet sector: 94 points satisfy all four `D_21`
constraints.

One such reverse-half completion is

```text
    [1 0 0 0 0]
    [0 0 1 0 0]
R = [0 0 0 0 1].                                      (A4-C3-HALF)
    [0 0 0 1 0]
    [0 1 0 1 0]
```

It satisfies `q_19243=1`, all fourteen core occurrences, and all eight word
occurrences represented by `D_21`, hence exactly 22 of the thirty packet
words.  It satisfies none of `D_12` and moves every listed generator of the
rank-three `GL_3(2)`.  Therefore the forward directed central block, rather
than merely the presence of a central-`C3` letter, is the first finite
constraint not bypassed by an exact regular-chart countermodel.

For a general affine completion by two copies of `P=AGL_3(2)`, equations
`(A4-C3-DIR)` are precisely the extension conditions after adjoining either
central element `zeta`: `P` and `zeta` generate the full `A8` chart.  They are
not relations internal to `P*P`, which explains why the affine completion of
the fourteen-word core survives.  The full thirty-context problem must use at
least the forward directed block; this classification does not prove the
dimension-free full-packet gap.
