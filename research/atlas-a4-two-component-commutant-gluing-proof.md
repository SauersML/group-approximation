---
rg: 2
id: atlas-a4-two-component-commutant-gluing-proof
kind: route
title: Apply the amplification-stable finite-subspace angle to the two subgroup commutants
target: atlas-a4-two-component-commutant-gluing
requires:
  - atlas-a4-packet-biclique-decomposition
  - finite-subspace-gluing-is-amplification-stable
---

Work first on the base Hilbert--Schmidt space

```text
E = M_20160(C).
```

Let

```text
M_6  = Reg(A8)(H_6)',
M_18 = Reg(A8)(H_18)'.
```

Because the two packet subgroups generate `A8`, an operator commutes with both
of them exactly iff it commutes with all of `A8`.  Hence

```text
M_6 intersect M_18 = Reg(A8)(A8)'.
```

Apply `finite-subspace-gluing-is-amplification-stable` to the fixed pair
`M_6,M_18`.  It gives a finite base-space Friedrichs-angle constant `C_comp`
with

```text
dist(X,M_6 intersect M_18)^2
 <= C_comp (dist(X,M_6)^2+dist(X,M_18)^2).
```

For external multiplicity `k`, the relevant Hilbert--Schmidt operator space is
canonically the base space tensored with `M_k(C)`, and

```text
lambda_k(H_i)' = M_i tensor M_k(C),
lambda_k(A8)'  = (M_6 intersect M_18) tensor M_k(C).
```

The cited amplification theorem preserves the same gluing constant for every
`k`.  This is exactly `(A4-COMP-GLUE)`.
