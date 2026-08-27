---
rg: 2
id: finite-selector-induction-proof
kind: route
title: Induce every compatible selector character to the finite gadget
target: finite-selector-gadget-induction-barrier
requires: []
---

Let `A<=H` be finite abelian, contain central `J`, and let
`chi:A->T` satisfy `chi(J)=zeta`.  The induced representation
`Ind_A^H chi` is finite-dimensional and its restriction to `A` contains
`chi`.  Since `J` is central, it acts on every inducing coset by the same
scalar `zeta`, so the entire induced representation has `J=zeta I`.

Thus every selector character compatible with the mark appears in some
marked representation of `H`.  No additional relations internal to the
finite overgroup can forbid one such character while allowing another.  In
particular, parity cannot prune three-hot characters while preserving the
one-hot characters of the same parity.
