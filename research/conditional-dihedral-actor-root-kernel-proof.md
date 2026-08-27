---
rg: 2
id: conditional-dihedral-actor-root-kernel-proof
kind: route
title: Quotient a conditional cyclic actor after setting its payload root equal to one
target: finite-cyclic-actor-root-kernel-dichotomy
requires:
  - split-steinberg-conditional-swap-has-root-kernel-countermodel
  - role-packed-bcs-gap-is-one-idempotent
  - protected-adaptive-btb-wordization-preserves-canonical-budget
---

Compute `(FCA2)` blockwise on `p` and `1-p`.  For the general actor, set all
root generators and `u=W` equal to one.  The actor factors through
`A/normalClosure(u)`.  If its quotient has no representation with the
protected central character used by the perfect seed, then perfect
completeness is impossible because `B_f=0` makes `W=1` in that very model.
Otherwise combine such a finite quotient representation with the finite
uniform-assignment/role representation in the same scalar central character.
The resulting exact finite model has positive `QB_f` but identity transport,
which refutes every positive overlap-loss constant.
