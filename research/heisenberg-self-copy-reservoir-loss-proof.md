---
rg: 2
id: heisenberg-self-copy-reservoir-loss-proof
kind: route
title: Compare the source and joint-child Stone--von Neumann commutant densities
target: heisenberg-self-copy-relators-do-not-pay-reservoir-loss
requires:
  - finite-tags-do-not-atomize-heisenberg-schrodinger-tower
  - orthogonal-heisenberg-self-copy-skeleton-has-marked-microstates
---

Use the stage-`M` Schrödinger model from the two prerequisites and restrict
the parent to `L` coordinates.  Its two coordinate-permutation children
jointly use `2L` coordinates.  Finite Stone--von Neumann gives the generated
algebras

```text
M_(p^L) tensor I_(p^(M-L)),
M_(p^(2L)) tensor I_(p^(M-2L)).
```

The normalized operator-space ranks of their commutant Reynolds projections
are therefore `p^(-2L)` and `p^(-4L)`.  The second algebra contains the first,
so the latter Reynolds range lies in the former and their difference has
trace `p^(-2L)-p^(-4L)>0`.  All self-copy and finite Heisenberg relations are
exact in the same model.  Tensoring a fixed tag changes only the common
spectator factor and leaves the normalized densities invariant.  This is
exactly the zero-defect reservoir loss asserted by the target claim.
