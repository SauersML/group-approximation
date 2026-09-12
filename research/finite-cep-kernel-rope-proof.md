---
rg: 2
id: finite-cep-kernel-rope-proof
kind: route
title: Put the graph on the diagonal and swap the two finite coordinates
target: finite-cep-kernel-witness-synchronizes-rope
requires: []
artifacts:
  - research/artifacts/three-bridge-finite-cep-rope-route-2026-08-25.md
---

The subgroup `L` is profinitely closed in `K`: if `(f,p)` is not on the
graph, choose a finite quotient `r` of `P` separating `p` from `j(q(f))`;
the map `(f',p')->(r(j(q(f'))),r(p'))` sends `L` to the diagonal and the
chosen point off it.  Finite-quotient Britton reduction then proves residual
finiteness of the central HNN `Gamma`.

Given `beta`, choose `r` from `(FCK1)` and map

```text
(f,p) in K |-> (r(j(q(f))),r(p)) in C times C,
v |-> the coordinate swap.
```

The graph `L` lands diagonally, so the centralizing relations hold.  On
`S=<F,F^v>`, first-coordinate projection is `r j tau`; hence the kernel of
this finite quotient on `S` is contained in `ker(beta tau)`.  Product these
maps with cofinal finite quotients of `Gamma` and `Q` to obtain `(RPS1)`.
