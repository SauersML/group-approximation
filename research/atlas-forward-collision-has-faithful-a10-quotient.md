---
rg: 2
id: atlas-forward-collision-has-faithful-a10-quotient
kind: claim
title: The minimal forward-collision quotient has an explicit faithful-vertex A10 image
artifacts:
  - experiments/atlas_a4_forward_collision_a10_certificate.g
  - research/artifacts/atlas-a4-forward-collision-a10-certificate.json
distinct_from:
  atlas-forward-collision-has-faithful-s288-amalgam: that constructs a structural degree-288 regular amalgam; this gives an independent transitive degree-ten permutation certificate whose generated image is A10.
  atlas-forward-collision-bass-serre-reduction: that isolates vertex injection as a binary question; this answers it positively with five explicit permutations.
  atlas-one-forward-c3-has-no-standard-gl6-completion: that finite-field theorem only excludes a standard padded GL6 chart; this nonstandard permutation model explains why it cannot be promoted to an abstract operator-system obstruction.
---

Let `Gamma` be the one-relator quotient of
`atlas-forward-collision-bass-serre-reduction`.  The following one-based image
lists define permutations of ten points, in generator order `r,z,c,t,s`:

```text
r=[1,3,5,6,2,7,4,8,9,10]
z=[1,3,5,7,2,4,6,8,9,10]
c=[1,4,6,2,7,3,5,8,10,9]
t=[1,2,5,4,9,7,10,8,3,6]
s=[2,1,3,8,9,6,10,4,5,7].                           (A4-A10-1)
```

Exact permutation multiplication verifies every defining relation of
`Gamma`, including

```text
q=t c s c t^-1 c s t c=1.
```

The generated image has order `1814400=|A10|`, and all five generators are
even, so the image is exactly `A10`.  More importantly, the relevant subgroup
orders are

```text
|<r,z,c>|=18,       |<r,z,s t>|=144,       |<t,s>|=6,
|<r,z>|=9,          |<s t>|=2.                            (A4-A10-2)
```

Thus all three vertex groups `F,C,K` and both edge groups `A,B` inject.  This
decisively answers the binary seam `(A4-BS-4)` on the finite-quotient side;
in particular `b=s t` does not die after collision.

The left regular representation of `A10` is also an exact atlas-scale
carrier.  Since

```text
|A10|=1814400=90*20160,
```

its restrictions are

```text
100800 Reg(F) = 1120*90 Reg(F),
12600 Reg(C)  = 140*90 Reg(C),
302400 Reg(K) = 3360*90 Reg(K).
```

They are precisely the compatible multiplicities from the Bass--Serre
reduction at atlas multiplicity `k=90`.  Hence one forward edge plus its
minimal collision support has an exact finite-dimensional regular-margin
countercarrier.  This does not yet satisfy the other rank-three core edges;
their extension is the next global constraint.
