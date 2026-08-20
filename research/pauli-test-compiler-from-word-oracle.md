---
rg: 2
id: pauli-test-compiler-from-word-oracle
kind: route
title: Turn the uniform word oracle into the dimension-matched Pauli strategy
target: dimension-reported-pauli-test-halting-compiler
requires:
  - uniform-halting-pauli-word-oracle
  - maximally-entangled-vectorization-is-hs-isometry
---

For a halting output `D`, use the word oracle's rounded question PVMs on the
first copy of `C^D` and their entrywise conjugates on the second copy, with
shared state `Phi_D`.  The identity `(MEH1)` converts every word consistency,
linearity and braiding error charged by the oracle into the corresponding
state-dependent test loss without a dimension factor.  The oracle's fixed
average bound therefore gives success at least `1-eta_0`.  Perfect nonhalting
marked completeness is inherited unchanged.  These are exactly the two
clauses of `dimension-reported-pauli-test-halting-compiler`.

