---
rg: 2
id: predicate-activated-cnot-routes-relative-pauli-halves-proof
kind: route
title: Check one symbolic symplectic transvection and read its flag action
target: predicate-activated-cnot-routes-relative-pauli-halves
requires:
  - relative-pauli-child-split-gives-one-exit-copy
artifacts:
  - experiments/predicate_activated_cnot_router.py
---

Write the commutator form of `(a,b,c,d)` as two identical hyperbolic blocks,
both labelled by the central word `K`.  The exponent matrix of `(PCR1)` has
columns

```text
(1,0,1,0), (0,1,0,0), (0,0,1,0), (0,1,0,1).
```

Direct multiplication over `F_2` shows `T^2=I` and
`T^T diag(H,H) T=diag(H,H)`.  Hence all defining commutators and involution
relations are preserved and `phi` is an involutive automorphism.  The HNN
embedding theorem for the stable letter implementing `phi` then retains the
base group and all of its central sectors.

Conjugation sends the target flag observable `d` to `bd` while fixing the
control observable `b`.  On the source spectral subspace `d=+1`, the target
`d` sign is therefore exactly the source `b` sign.  When `K=-1`, `a` swaps
the two `b` halves, proving their equal trace and `(PCR2)`.  When `K=+1`, the
same calculation is an invertible linear permutation of four commuting
involutions.  The verifier checks the order, symplectic identity, and four
sign cases exactly.
