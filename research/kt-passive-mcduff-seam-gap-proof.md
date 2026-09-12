---
rg: 2
id: kt-passive-mcduff-seam-gap-proof
kind: route
title: Tensor the seam representation with a trivial finite-tracial module
target: kt-passive-mcduff-amplification-does-not-close-the-seam
requires:
  - kt-internal-c-seam-has-a-kazhdan-gap
---

The Gamma representation controlling the seam on
`L^2(L(N) tensor Q)` is

```text
pi tensor 1_(L^2(Q)),
```

where `pi` is `(KIP1)`.  Since `pi` has no invariant vector, neither does
its tensor product with a trivial representation of arbitrary multiplicity:
decompose `L^2(Q)` by an orthonormal basis and apply the same assertion to
each coefficient.  The Kazhdan inequality retains the identical constant
`kappa`, proving `(KPM1)`.
