---
rg: 2
id: bergman-dicks-vertex-induction-projection-proof
kind: route
title: Apply the Bergman--Dicks projective-module theorem and polar decomposition
target: bass-serre-algebraic-projections-are-stably-vertex-induced
requires: []
---

For a finite graph of finite groups, form its graph of complex group rings.
Every edge ring is finite-dimensional semisimple by Maschke's theorem, and
the graph-of-rings fundamental ring is `R=C[Gamma]`.  Proposition 2.12 of
Sanchez-Peralta (2025), quoting Bergman, Corollary 2.6, for coproducts and
Dicks, Corollary 22, for HNN extensions, gives the induced decomposition
`(BSP2)` for the projective left module `R^n p` cut out by `p`.

Because `R^n p` is finitely generated and the graph is finite, each induced
summand is finitely generated over `R`.  Moreover `R` is free, hence
faithfully flat, as a right module over every vertex group algebra (choose
right coset representatives).  Finite generation descends along a faithfully
flat extension, so the vertex projectives may be taken finitely generated.
Each finite-dimensional semisimple
vertex algebra represents such a projective by a self-adjoint matrix
projection `e_v`.  The module isomorphism between the ranges of `p` and
`e=directSum_v e_v` is implemented algebraically by rectangular matrices
`X,Y` over `R` satisfying the usual idempotent-equivalence equations.  View
them in a rectangular matrix amplification of the finite von Neumann algebra
`L(Gamma)`.  The polar part of the range isomorphism has initial projection
`e` and final projection `p`, proving `(BSP3)`.

Finally, induction preserves von Neumann dimension.  In the regular Fourier
decomposition of a finite group algebra, a rank-one projection in the
`pi`-block has canonical trace `dim(pi)/|Gamma_v|`, giving `(BSP5)` and an
independent trace check.

Primary source:

```text
https://link.springer.com/article/10.1007/s00039-025-00710-4
```
