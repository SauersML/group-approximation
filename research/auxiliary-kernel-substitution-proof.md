---
rg: 2
id: auxiliary-kernel-substitution-proof
kind: route
title: Kill every auxiliary letter and telescope back to the residual base relators
target: auxiliary-kernel-two-cells-reduce-to-base-word-detectors
requires:
  - one-round-v4-lamps-wordize-a-bcs-losing-projection
  - central-marked-two-cycle-zero-compression-cell
  - role-packed-bcs-gap-is-one-idempotent
---

The substitution `epsilon` sends every defining relator of `Gamma` to the
corresponding defining relator of `K_0`.  Hence the assignment which fixes
the base generators and kills the auxiliary generators descends from the
free group to the homomorphism `(AKT3)`.  Pulling any representation of
`K_0` back through this homomorphism proves the exact countermodel statement.
For the uniform-assignment/role packet, positivity in `(AKT4)` is the fixed
character-idempotent trace computation in
`role-packed-bcs-gap-is-one-idempotent`.

For `(AKT10)`, enumerate the auxiliary occurrences of a reduced representative
of `r` and replace them one at a time by the identity.  Left and right
multiplication by unitaries preserve normalized Hilbert--Schmidt norm, so
each replacement costs at most

```text
max_(a in A)||rho(a)-1||_2.
```

After all replacements the word is `epsilon(r)`.  The triangle inequality
first compares `rho(epsilon(r))` with `rho(r)` and then `rho(r)` with one,
giving `(AKT10)`.

Finally, every `V_4` lamp word becomes one when its lamp generators are
killed.  Taking also `z=1` turns `(AKT5)` into

```text
[1,W]=[1,1]=1,             W1W^(-1)=1.
```

Thus the arbitrary original payload word `W` is untouched and the positive
base model extends exactly.  This proves the advertised specialization.
