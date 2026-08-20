---
rg: 2
id: disjoint-tag-cross-gram-proof
kind: route
title: Apply the finite intertwiner Laplacian to leakage maps and branch cross products
target: disjoint-tag-covariance-controls-cross-gram
requires:
  - finite-group-intertwiner-laplacian-gap
  - partial-isometry-gram-is-range-overlap
---

First put `A_i=(1-P)T_i:V_i->(1-P)K`.  Since `P` commutes with `rho(H)`,

```text
rho(s)A_i-A_i pi_i(s)=(1-P)D_(i,s).                  (1)
```

The second clause of `(DTC1)` says that the exact intertwiner space for
`A_i` is zero.  The finite-group intertwiner gap therefore gives

```text
kappa ||(1-P)T_i||_2^2 <= E_i.                        (2)
```

Sum `(2)` over `i` to obtain the leakage estimate `(DTC3)`.

Now fix `i!=j` and put `A=T_i^*T_j:V_j->V_i`.  For `s in S`, covariance gives

```text
pi_i(s)A-A pi_j(s)
 =-D_(i,s^(-1))^*T_j+T_i^*D_(j,s).                    (3)
```

Both `T_i,T_j` are contractions, so

```text
||pi_i(s)A-A pi_j(s)||_2^2
 <=2||D_(i,s^(-1))||_2^2+2||D_(j,s)||_2^2.            (4)
```

By `(DTC1)`, the exact intertwiner space is zero.  Apply
`finite-group-intertwiner-laplacian-gap` and sum `(4)` over the inverse-closed
set `S`:

```text
kappa ||T_i^*T_j||_2^2 <=2(E_i+E_j).                  (5)
```

Summing `(5)` over ordered pairs `i!=j` counts each `E_i` exactly
`2(N-1)` times, proving `(DTC4)`.  Common normalization of every squared norm
does not change the calculation.  Finally
`partial-isometry-gram-is-range-overlap` substitutes
`||T_i^*T_j||_2^2=tau(R_iR_j)` and gives `(DTC5)`.  Adding the leakage and
overlap estimates gives `(DTC6)`.
