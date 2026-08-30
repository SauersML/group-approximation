---
rg: 2
id: stw63-bidual-corner-equivalence-proof
kind: route
title: Put the von Neumann implementing sequence in the bidual corner
target: stw63-bidual-relative-corners-equivalent
requires:
  - stw63-all-von-neumann-codomains-have-uniqueness
  - stw63-aue-is-relative-corner-equivalence
---

The canonical maps `phi,psi:Z->B**` are unital and injective.  Universal
von Neumann uniqueness makes them approximately unitarily equivalent by a
sequence in `U(B**)`.  Apply the relative-corner characterization with
codomain `B**`, using the constant-coordinate copy of
`pi=diag(phi,psi)` inside `M_2((B**)_infinity)`.  The resulting lower-left
partial isometry belongs exactly to the commutant `E` in (1), and it has
initial projection `p` and final projection `q`.

The coordinate inclusion of sequence algebras is injective because
`B->B**` is isometric: a bounded `B`-sequence is norm-null in `B**` exactly
when it is norm-null in `B`.
