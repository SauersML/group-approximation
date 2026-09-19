---
rg: 2
id: diagonal-regular-fell-center-proof
kind: route
title: Apply Fell absorption to the intrinsic diagonal image
target: diagonal-regular-isotypic-center-stays-plancherel
requires: []
---

For any finite-dimensional representation `pi`, the unitary

```text
delta_h tensor xi |-> delta_h tensor pi(h)^(-1)xi
```

conjugates `lambda_Q tensor pi` to `lambda_Q tensor 1`.  Iterating with
`pi=lambda_Q^(tensor(t-1))` yields

```text
Lambda_t ~= lambda_Q^(direct-sum |Q|^(t-1)).
```

Amplification preserves the central block labels and multiplies every block
rank and the total dimension by the same factor.  The normalized rank of the
`rho` block is therefore `dim(rho)^2/|Q|`.  Irreducibles and Plancherel weights
of `K^F` factor coordinatewise, giving the stated product law and intrinsic
faithful-fiber mass.
