---
rg: 2
id: gao-popa-compactness-no-go-proof
kind: route
title: Separate coordinate hyperfiniteness from compactness of the ultraproduct deformation
target: gao-hyperfinite-carriers-do-not-give-popa-compactness
requires: []
artifacts:
  - research/artifacts/sl3-gao-popa-compactness-audit-2026-08-21.md
---

Popa's intertwining criterion says that `P precalB Q` is equivalent to the
existence of a nonzero finite-right-`Q` subbimodule of `L^2(calB)`, or to
the absence of a net `u_i in U(P)` satisfying

```text
||E_Q(x u_i y)||_2 -> 0       for every x,y in calB.          (GPC1)
```

The standard rigidity argument obtains such an intertwiner from normal
subunital subtracial completely positive maps `Phi_j` which converge
pointwise to the identity and whose `L^2` implementations are compact over
`Q`.  Property `(T)` upgrades pointwise convergence to uniform convergence
on `U(P)`; `(GPC1)` then contradicts compactness.

In a Gao scalar-coefficient model the carrier is

```text
calB=prod_omega B_k
```

with hyperfinite `B_k`.  Approximating a finite set in each `B_k` by a
finite-dimensional algebra produces maps of ranks `r_k`, but compactness of
the induced ultraproduct operator does not follow when `r_k -> infinity`.
Indeed, `P` itself embeds trace-preservingly into a matrix ultraproduct:
take left regular representations of an exhausting separating family of
finite quotients of the residually finite group `SL_3(Z)`.  If the resulting
ultraproduct inherited scalar-Haagerup compact maps merely from its matrix
coordinates, the preceding Popa argument would force its diffuse rigid
subfactor `P` to be finite dimensional, a contradiction.

Equivalently, fix representing sequences for a generating set of `P`.  If
finite-dimensional coordinate algebras approximate those representatives
with error tending to zero while their dimensions remain bounded on an
omega-large set, their ultraproduct is finite dimensional and contains the
generated copy of `P`, impossible.  Hence the required coordinate ranks
necessarily diverge.  Gao's definition imposes no rate or tightness that
turns this diverging family into a compact ultraproduct deformation.
