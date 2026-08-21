---
rg: 2
id: global-marked-type-cycle-selector-proof
kind: route
title: Decompose the type permutation into cycles and pack compressed rows by orthogonality
target: global-marked-type-cycle-selector-decoder
requires:
  - cyclic-coarse-fine-selector-rows-spread-carrier-error
  - non-ce-bcs-has-robust-approximate-energy-gap
---

Decompose the finite permutation `sigma` into disjoint cycles.  On each cycle,
`cyclic-coarse-fine-selector-rows-spread-carrier-error` applies to `(GTC2)`
and `(GTC3)`.  Summing the cycle inequalities gives

```text
sum_omega d_omega^2 >=(1/4)sum_omega tr(P_omega).       (GTP1)
```

For each fixed ordinary word `r`, orthogonality of the isotypic domains inside
each context gives

```text
sum_omega ||(r(U)-1)Q_omega||_2^2
 =sum_c ||(r(U)-1)Q_c||_2^2
 <=L||r(U)-1||_2^2.                                   (GTP2)
```

Combine `(GTP1)` with `(GTC4)`, then use `(GTP2)` and `(GTC5)`:

```text
(alpha/4)E_forbid-zeta/4
 <=(1/4)sum_omega tr(P_omega)
 <=sum_omega d_omega^2
 <=KL sum_(r in T)||r(U)-1||_2^2+eta.                 (GTP3)
```

Rearranging is `(GTC6)`.  Finally apply the dichotomy following `(GTC7)`.
All sums are finite and fixed by the source BCS and packet menu, so
exactification losses remain dimension-independent.
