---
rg: 2
id: symmetric-sign-packet-density-loss-proof
kind: route
title: Compute the trivial-to-sign matrix coefficient and its ambient packet trace
target: symmetric-sign-packet-has-factorial-amitsur-density-loss
requires:
  - one-sided-amitsur-oracle-has-bounded-fock-model
---

The coefficient of `lambda(tau)` in `e_-^2` is

```text
(1/N^2)sum_sigma sgn(sigma)sgn(sigma^(-1)tau)
 =sgn(tau)/N,
```

so `e_-` is a projection.  Its identity coefficient, hence its normalized
regular trace, is `1/N`; the same calculation without signs gives `e_+`.
Their ranges are the unit vectors in `(SPD3)`.

Taking the matrix coefficient of the diagonal operator `(SPD2)` between
those vectors gives `(SPD4)` directly.  Comparison with `(SPD5)` gives the
internal `1/sqrt(N)` loss.  A rank-one packet block with coefficient
`T/sqrt(N)` has ambient squared normalized Hilbert--Schmidt norm

```text
(1/N)||T/sqrt(N)||_2^2=||T||_2^2/N^2,
```

which proves `(SPD6)`.  Finally the prefix-code orthogonality in
`one-sided-amitsur-oracle-has-bounded-fock-model` gives `T^*T=1` for its
Fock boundary, showing that both losses occur despite unit exact
completeness amplitude.
