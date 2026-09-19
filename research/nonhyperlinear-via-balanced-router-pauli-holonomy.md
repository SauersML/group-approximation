---
rg: 2
id: nonhyperlinear-via-balanced-router-pauli-holonomy
kind: route
title: Expose the two native quarter reflections with balanced routers and charge their fixed holonomy
target: non-hyperlinear-group
requires:
  - atlas-steinberg-rank-five-translation
  - balanced-router-pauli-holonomy-interface
  - canonical-trace-tests-robustify-pauli-quarter-holonomy
  - fixed-holonomy-on-overlap-pays-relator-energy
---

The balanced-router interface supplies one finite extension of the atlas in
which the two native trace-quarter Hecke reflections are represented by fixed
derived-packet words and a named mixed return asks their holonomy to vanish.
The canonical trace tests force the squared commutator energy of those two
reflections to be `1/2-o(1)` in every regular microstate, independently of
external multiplicity.  The return relator forces the same energy to be
`o(1)`.  This fixed contradiction rules out a regular normalized-HS
microstate sequence for the explicit finite presentation.

The exact properly-infinite extension required by the router claim preserves
one nontrivial representation, so the presentation is not collapsed merely
to manufacture the gap.
