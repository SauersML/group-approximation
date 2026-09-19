---
rg: 2
id: atlas-m2-six-ceiling-refutation-proof
kind: route
title: Evaluate every cycle and bridge opcode on the regularized GL8 escape
target: atlas-m2-escape-refutes-six-a4-cycle-bridge-ceilings
requires:
  - atlas-multiplicity-two-packet-collision-hub-escape
  - atlas-t30-is-one-parabolic-c3-bridge
artifacts:
  - experiments/atlas_a4_repeated_module_escape_verify.py
  - experiments/atlas_m2_six_ceiling_refutation_verify.js
  - experiments/atlas-m2-six-ceiling-refutation.json
---

The first prerequisite supplies the literal exact packet network, collision
`q_19243=1`, and its passage to the finite regular representation.  The
second fixes `h,k,z,b`, proves `c=hk`, `a=zb`, and identifies
`t30=c^-1ac`.

The standalone binary audit lifts those four `GL_4(F_2)` coordinates to the
repeated eight-dimensional module, constructs all four cycle roots, computes
`F^-1 g F g^-1`, and checks the matrices, orders, and positive ranks recorded
in the target.  Positive rank makes every opcode nonidentity.  Regular
character orthogonality then gives `(M2-6-1)` exactly.  Substitution gives
`73`, the optimized lower bound `25`, `x_30^2=1`, `E_PC3=12`, and
`E_2HOL=6`.  Finally rationalizing the joint spectral constant gives

```text
lambda=3pq/(p+q+sqrt(p^2-pq+q^2))<3q,
```

so even its unavoidable `qD_12=q` term exceeds `lambda/256`.  Direct-sum
amplification preserves every normalized value and supplies growing matrix
dimension if that convention is imposed.