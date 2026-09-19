---
rg: 2
id: minimal-marked-graph-ce-from-finite-window-phase-space-section
kind: route
title: Cancel scalar Clifford curvature and pad by a regular finite quotient
target: minimal-marked-graph-crossed-product-ce
requires:
  - minimal-marked-graph-finite-window-phase-space-section
---

For one finite actor and lamp window, take the block supplied by
`minimal-marked-graph-finite-window-phase-space-section`.  Its multiplication
curvatures are scalars:

```text
U_g U_h = omega(g,h) U_(gh).
```

Replace `U_g` by `U_g tensor conjugate(U_g)` and the lamp `W_x` by
`W_x tensor 1`.  Every tested scalar multiplier cancels, while the first
factor retains the prescribed lamp covariance and exact twisted lamp trace.

Since the Kun--Thom actor group is residually finite, choose a finite quotient
separating all nonidentity actor words in the window and tensor the actors
with its regular representation.  This kills the trace of every mixed word
whose actor part is nonidentity.  Words with identity actor part retain the
exact Clifford trace.  The resulting matrices satisfy all four demands in
the finite-window formulation of `minimal-marked-graph-crossed-product-ce`.

