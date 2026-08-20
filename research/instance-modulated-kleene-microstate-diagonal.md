---
rg: 2
id: instance-modulated-kleene-microstate-diagonal
kind: claim
title: Computable instance-dependent microstate thresholds suffice for the Kleene diagonal
distinct_from:
  dimension-matched-kleene-microstate-diagonal: that assumes one universal defect and separation threshold for every source machine; this permits arbitrary positive computable thresholds attached to the source code.
  self-referential-perfect-zpc-irs-gap: that diagonalizes a computable game-value upper hierarchy; this diagonalizes directly against marked finite-dimensional group microstates.
---

Suppose a total computable compiler sends every Turing machine `M` to

```text
(G_M=<S_M|R_M>, w_M, delta_M, alpha_M),
```

where `delta_M>0` and `0<alpha_M<sqrt(2)` are computable rationals, and has
the following properties:

```text
M does not halt
  => w_M!=1 in G_M,                                               (IMK1)

M halts and outputs the positive integer D
  => every D-dimensional unitary tuple U with Def_(R_M)(U)<delta_M
     satisfies ||w_M(U)-I||_2<=alpha_M.                           (IMK2)
```

Then one can effectively construct a finitely presented nonhyperlinear
group.

The constants may depend arbitrarily, but computably, on the source code of
`M`.  They need not be uniform over machines.  They must be available before
running `M`: dependence on the unknown eventual runtime or on data revealed
only after halting is not covered.  This distinction admits computable
instance moduli such as a BCS soundness constant `C_M`, while preserving the
fixed-point contradiction.
