---
rg: 2
id: pure-dyadic-clifford-slots-have-a-uniform-one-third-gap
kind: claim
title: Pure dyadic Clifford packets have a uniform one-third common-rank gap
artifacts:
  - research/artifacts/dyadic-iwahori-character-branching-2026-08-23.md
distinct_from:
  adjacent-clifford-flow-has-one-third-rank-deficit: that bounds common mass supported only on adjacent conductor pairs; this includes same-depth cells and proves that their character slots compete with the adjacent arrival slots.
  regular-trace-allows-diffuse-dyadic-flow: that constructs a scalar nearest-neighbor profile without newest-layer character-slot incidence; this proves that the diagonal and adjacent cells compete inside the actual Clifford packets.
  pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss: that proves a stronger half-loss for Plancherel-weighted regular packets; this gives a one-third loss for arbitrary selected irreducibles and multiplicities.
---

Let `Pi_+` and `Pi_-` be equal-dimensional finite direct sums of
representations of the dyadic quotients

```text
G_a=SL_2(Z/2^a)
```

decomposed at their minimal exact conductor, with every occupied conductor
at least two.  Allow arbitrary irreducible labels and multiplicities at
unboundedly many finite depths.  If `d=dim(Pi_+)=dim(Pi_-)`, then the
maximal common subrepresentation of their upper/opposite Iwahori
restrictions has dimension at most

```text
2d/3.                                                    (DCS1)
```

More precisely, let `x_A,x_B` and `y_A,y_B` be the total physical
dimensions on the two vertex sides carried by the newest-layer orbits
`O_A,O_B`.  Then every common edge representation has dimension `C`
satisfying

```text
C <= (x_B+y_B)/3 + (2/3)min(x_A,y_A) <= 2d/3.           (DCS2)
```

The first term is a character-slot conservation law.  Every adjacent match
is charged to the unique root-character slot of its higher-conductor `O_B`
endpoint.  A same-depth `O_B` match consumes those same arrival slots, not
a third independent scalar cell.  Same-depth `O_A` matching has capacity
`2/3` on each side.  The fixed orbit has no same-depth cell, and exact
conductor excludes `O_0`.

The complete joint conductor table excludes all nonadjacent matches, so
`(DCS2)` covers the entire common subrepresentation.  Consequently Selberg
`(tau)` for the fixed Iwahori subgroup gives a depth- and label-uniform
normalized-Hilbert--Schmidt defect floor

```text
max_(s in S_B)||rho_+(s)V-V rho_-(s)||_2
   >= kappa_B/sqrt(3)                                  (DCS3)
```

for every unitary identification `V`.  Thus the selected-irrep pure-dyadic
tower cannot realize the scalar Folner window; projective multiplicities
cannot evade the missing character slot.

The conductor-one quotient is deliberately excluded: it is one fixed finite
diagram and can contain fully compatible packets.  It is already covered by
`bounded-dyadic-conductor-iwahori-pairs-have-uniform-repair`; the theorem
above supplies the depth-independent obstruction on its complement.
