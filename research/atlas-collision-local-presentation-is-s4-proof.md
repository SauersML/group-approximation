---
rg: 2
id: atlas-collision-local-presentation-is-s4-proof
kind: route
title: Todd-Coxeter the collision vertex and compare with its marked S4 quotient
target: atlas-collision-local-presentation-is-s4
requires:
  - atlas-19243-s3-relative-normal-form
artifacts:
  - experiments/atlas_a4_collision_local_universal_s4.g
---

GAP's exact coset enumeration gives order 24 for the displayed finitely
presented group.  Independently, the marked permutations

```text
t=(1 2 3),     s=(1 2),     c=(1 3)(2 4)
```

satisfy every displayed relator and generate `S4`, also of order 24.  The
resulting surjection from the presented group is therefore an isomorphism.
Here the tuple is written in the left-composition convention of the packet
replay; the GAP certificate uses the corresponding right-action label
`c=(1 4)(2 3)`.
GAP identifies it as `SmallGroup(24,12)` and verifies directly that

```text
|<t,s>|=6,       |<<c>>|=4,       |J/<<c>>|=6.
```

These are exact finite-presentation and permutation calculations.  In
particular, no assumption that a chosen matrix image is faithful enters the
universal identification.
