---
rg: 2
id: atlas-q1920-linear-collision-proof
kind: route
title: Compute C_GL5(2)(A) and combine it with the noncentral radial lift mismatch
target: atlas-any-q1920-completion-must-move-the-module
requires:
  - atlas-q1920-is-radial-holonomy-extension
artifacts:
  - experiments/atlas_a4_q1920_module_structure.g
  - research/artifacts/atlas-a4-q1920-module-structure.json
---

Using a pc basis of `V`, the verifier records the four exact conjugation
matrices for `r,y,u,b`.  It solves the simultaneous linear equations

```text
X R = R X,             X U = U X
```

over `F2`, retains the invertible solutions, and obtains a group of order
six with order profile `1^1 2^3 3^2`.  Substitution of each of its three
involutions into the two literal collision words gives zero solutions, for
both marked Q1920 classes.

The remainder of the claim is symbolic.  If `V normal L`, conjugation gives
a homomorphism `L -> GL(V)`, so the exact finite calculation forces `c` into
its kernel.  The already-certified lift mismatch `(3,3)` then contradicts
the marked collision-S4 centralizer flag: among the three `B` involutions
the flags are `[true,false,false]`, while the mismatch uses the third.
