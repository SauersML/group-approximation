---
rg: 2
id: nested-packet-reynolds-orthogonality-proof
kind: route
title: Order the fixed spaces and conjugate the subgroup Reynolds projections
target: nested-packet-reynolds-defect-is-orthogonal-to-old-commutant
requires: []
---

For a subgroup `K`, the range of its conjugation Reynolds projection is

```text
Fix(K)=End_K(H).
```

The inclusions `A<B<Lambda` reverse the fixed spaces:

```text
End_Lambda(H) < End_B(H) < End_A(H).
```

Orthogonal projections onto nested subspaces multiply to the smaller
projection.  Hence

```text
E_Lambda R_B=R_B E_Lambda=E_Lambda,
E_Lambda R_A=R_A E_Lambda=E_Lambda.
```

Subtracting proves `(NRO1)`.

Conjugation by `rho(t)` carries fixed spaces and their orthogonal
projections equivariantly:

```text
T R_K T^*=R_(tKt^(-1)).
```

Since `tBt^(-1)<Lambda`, one has

```text
E_Lambda <= R_(tBt^(-1)) <= R_(tAt^(-1)).
```

Subtracting exactly as before proves `(NRO2)`.

Finally the range in `(NRO2)` lies in
`End_Lambda(H)^perpendicular`.  The definition of the adjoint spectral gap
on that orthogonal complement gives `(NRO3)`.
