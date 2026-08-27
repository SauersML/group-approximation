---
rg: 2
id: iwahori-cycle-packet-determinant-proof
kind: route
title: Divide the determinants of the two cubic words
target: iwahori-cycle-packet-determinant-fence
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
---

Taking determinants in `(X S^2)^3=1` and `(X R S)^3=1` gives two cube roots
of unity.  Their quotient is

```text
[det(XRS)/det(XS^2)]^3=[det R/det S]^3=1,
```

which proves `(PDF3)`.  In the scalar packet normal form, `R` is an
`m`-cycle permutation with one corner phase `v`, so
`det R=(-1)^(m-1)v`; multiplying the diagonal entries of `S` gives the
geometric sum in `(PDF4)`.  The prime specialization follows from
`p | 4^m-1` and invertibility of `3 mod p`.
