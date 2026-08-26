---
rg: 2
id: atlas-six-row-singular-counting-via-fixed-packet-hall-selection
kind: route
title: Prove six-row singular counting by one fixed packet-type Hall graph
target: atlas-six-row-singular-counting-dominates-nontrivial-s3
requires:
  - atlas-fixed-packet-hall-cannot-prove-six-row-singular-counting
---

**INVALIDATED.**  The proposed route was to refine the regular `A_8` Fourier
decomposition by finitely many packet restriction types, name the source
projection

```text
P_t=1_[t,infinity)(|U-E_K(U)|)
```

and the six residual projections

```text
Q_(r,t)=1_[kappa t,infinity)(|R_r(U)|),
```

and then prove `(SCI3)` from a fixed finite capacitated Hall graph whose
capacities are the ranks of the resulting type intersections.

`atlas-fixed-packet-hall-cannot-prove-six-row-singular-counting` shows that
this route cannot work when the graph and all compatibility constraints are
fixed rational packet data.  Clearing denominators makes its matrix profiles
dense in the finite tracial profile polytope, whereas the exact Leavitt
profile has positive source rank at some threshold and zero rank in every
residual target.  Hence no fixed family of those Hall cuts separates all
matrix profiles from that tracial profile.

The surviving Hall route must let the incidence itself move with `U` and
`t`, or use unbounded dimension-dependent data.  Merely inserting the moving
spectral ranks as capacities in a fixed type graph is insufficient.



