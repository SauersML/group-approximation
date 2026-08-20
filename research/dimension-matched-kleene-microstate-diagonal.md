---
rg: 2
id: dimension-matched-kleene-microstate-diagonal
kind: claim
title: Dimension-matched halting soundness is enough for a self-referential nonhyperlinear group
distinct_from:
  self-referential-perfect-zpc-irs-gap: that diagonalizes a computable game-value upper hierarchy to obtain one finite game separation; this diagonalizes directly against finite-dimensional marked group microstates and records the witness dimension as machine output.
  residual-commutant-supercritical-schur-trigger: that asks one fixed group to detect the residual dimension inside every candidate microstate; this shows a machine-indexed compiler need only defeat the single dimension reported by its own fixed-point search.
---

Suppose a total computable compiler sends every Turing machine `M` to a finite
presentation `G_M=<S_M|R_M>` and word `w_M`, with universal computable
rational constants

```text
delta>0,                     0<alpha<sqrt(2),
```

and the following properties:

```text
M does not halt
  => w_M!=1 in G_M,                                               (DMK1)

M halts and outputs the positive integer D
  => every D-dimensional unitary tuple U with Def_(R_M)(U)<delta
     satisfies ||w_M(U)-I||_2<=alpha.                             (DMK2)
```

Then one can effectively construct a finitely presented nonhyperlinear group.

The decisive weakening is that `(DMK2)` is required only in the dimension
printed by the halting computation, not in all finite dimensions.  Therefore
the compiled computation may use `D` as ordinary input to choose a finite
Clifford rank, Pauli-braiding test size, or Schur-replica count above the
capacity of `M_D(C)`.  It need not infer matrix dimension from operators
inside an arbitrary microstate.
