---
rg: 2
id: marked-clifford-table-exponential-dimension-proof
kind: route
title: Exactify the Pauli table and use its nonzero spin sector
target: marked-clifford-table-exponential-dimension
requires:
  - gowers-hatami-finite-group-hs-stability
---

Apply `(GHS2)` to obtain an exact representation
`rho:E_N->U(m)` and an isometry `V:C^d->C^m` with

```text
d<=m<=d/(1-4epsilon^2),
||f(g)-V^*rho(g)V||_2<=42epsilon.                              (MCT4)
```

If `rho(J)=I_m`, then `V^*rho(J)V=I_d`, so `(MCT4)` with `g=J`
contradicts `(MCT1)`.  Therefore the `-1` eigenspace of the central
involution `rho(J)` is nonzero and invariant.

On that eigenspace the pairs `(rho(X_i),rho(Z_i))` satisfy the exact Pauli
relations.  The generated algebra is `M_(2^N)(C)`, so every module is a direct
sum of its `2^N`-dimensional spin module.  In particular `m>=2^N`.  Combining
this with the upper bound in `(MCT4)` gives `(MCT2)`.
