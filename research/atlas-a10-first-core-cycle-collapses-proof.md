---
rg: 2
id: atlas-a10-first-core-cycle-collapses-proof
kind: route
title: Exact Todd--Coxeter certificate for the collapsed first-core triangle
target: atlas-a10-first-core-cycle-collapses
requires:
  - atlas-forward-collision-has-faithful-a10-quotient
artifacts:
  - experiments/atlas_a4_first_cycle_triangle_completion.g
  - research/artifacts/atlas-a4-first-cycle-triangle-collapse.json
---

GAP 4.14 computes `J=<r,z,c,t>` from the certified degree-ten permutations.
`IsomorphismFpGroupByGenerators(J,[r,z,c,t])` returns the ten relators stored
verbatim in the certificate script.  They present a group of order `288`, so
using them introduces no quotient approximation at the `J` vertex.

Adjoin `u` and the five relations `(A4-TRI-2)`.  Exact Todd--Coxeter
enumeration gives an upper bound `|P|<=6`.  Conversely the assignment

```text
r,t,u -> 1,
z -> a,       c -> d
```

to `S3=<a,d | a^3=d^2=(d a)^2=1>` satisfies all fifteen relators and is
surjective.  Hence `|P|>=6`, proving `P~=S3` without relying on group-name
recognition.  A faithful permutation representation of `P` gives generator
orders

```text
(ord r,ord z,ord c,ord t,ord u)=(1,3,2,1,1),
```

which proves `(A4-TRI-3)`.  Since the canonical map from `J` kills its
order-three generator `t`, it is not injective; neither is the map from
`L=<u,t>`.

For geometric calibration, the pairwise Gersten--Stallings angles are
positive-curvature: at `J`, `|F intersect F^t|=2` supplies an alternating
length-four relation and angle `pi/2`; the `H` angle is `pi/2`; the `A4`
angle is `pi/3`.  Their sum is `4pi/3>pi`, so the nonpositive-curvature
triangle theorem cannot apply.  The Todd certificate decides this spherical
case exactly.
