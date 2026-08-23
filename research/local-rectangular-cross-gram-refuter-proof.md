---
rg: 2
id: local-rectangular-cross-gram-refuter-proof
kind: route
title: Apply the positive-mass PI inequality to the exact rectangular model
target: local-rectangular-packet-refutes-cross-gram-four-word-intertwining
requires:
  - first-leavitt-weyl-cell-has-exact-rectangular-model
  - positive-mass-four-pauli-intertwiner-forces-pi-gap
---

Use `p=2` in `(FWC2)` and, if full canonical packet trace is desired, take
the left regular representation of the finite packet group as specified in
the rectangular-model theorem.  The nontrivial central-character summand is
an amplification of `(FWC2)` and has fixed positive Plancherel weight.  The
source tuple has repeated arguments and hence zero `s4`; the target tuple is
the exact two-qubit Pauli tuple, so its Pauli residual in `(PMI1)` is zero.

If the local packet relations forced a common contraction of any fixed
positive mass, all four intertwining residuals in `(PMI1)` would also be
zero.  The inequality would give `8||T||_2<=0`, a contradiction.  Therefore
no such local implication exists.
