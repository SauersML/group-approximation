---
rg: 2
id: translated-three-site-central-mixture-proof
kind: route
title: Average bounded-incidence translates and compare global and blockwise resets
target: translated-three-site-blocks-defeat-global-peeling
requires:
  - three-site-pauli-refutes-unpeeled-fourth-moment
  - block-adaptive-sparse-reset-is-cheap
---

Choose a bounded-overlap cyclic family of translated row pairs and external
anchors.  Put one three-site Pauli tuple on each central summand with equal
trace.  Translation averaging makes every scalar coordinate tail `O(1/L)`.
A global set meets only `O(|U|)` summands, whereas the fourth-moment mass is
uniform over `Theta(L)` summands.  Conversely the central family of
three-element reset sets has integrated density `3/L`, so the block-adaptive
reset theorem applies.
