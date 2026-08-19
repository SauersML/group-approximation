---
rg: 2
id: a4-packet-collapse-from-component-commutants
kind: route
title: Glue the S3 and S3xC3 component commutants and recover all ten packet commutators
target: atlas-a4-relative-packet-commutator-collapse
requires:
  - atlas-a4-componentwise-commutant-collapse
  - atlas-a4-two-component-commutant-gluing
  - atlas-a4-packet-biclique-decomposition
---

Let `U_n` be the relative chart frame in the target.  By the componentwise
collapse and `(A4-COMP-GLUE)`,

```text
d_n := dist_2(U_n,lambda_(k_n)(A8)') -> 0.
```

Choose `Y_n` in the global right-regular commutant with

```text
||U_n-Y_n||_2 <= d_n+1/n.
```

Every packet letter `s` belongs to `A8`, so `Y_n` commutes with
`lambda_(k_n)(s)`.  Hence

```text
||U_n lambda(s)-lambda(s) U_n||_2
 <= ||(U_n-Y_n)lambda(s)||_2
    +||lambda(s)(U_n-Y_n)||_2
 <= 2(d_n+1/n).
```

The packet has ten distinct labels.  Therefore

```text
sum_(s in S)
 ||U_n lambda(s)-lambda(s)U_n||_2^2
 <= 40(d_n+1/n)^2 -> 0.
```

This is exactly `(A4-PACKET-COLLAPSE)`.
