---
rg: 2
id: signed-hecke-balanced-holonomy-route
kind: route
title: Normalize every context rank and solve only the block-escaping chord holonomy
target: signed-hecke-compatible-projection-atlas-for-nonce-bcs
requires:
  - tracial-bcs-has-rational-balanced-hyperoctahedral-atlas
  - coherent-balanced-context-permutations-would-give-a-ce-trace
  - root-block-piecewise-transport-cannot-host-nonce-bcs
  - signed-hecke-block-escaping-cycle-holonomy
---

Equation `(BCH1)` gives orthogonal algebraic context partitions of `q`, and
`(BCH2)` is exactly the shared-marginal equation `(BPA3)`.  Therefore
`bcs-corner-model-is-a-compatible-projection-atlas` turns the construction
into the unital map `(SHA2)`.

The three established inputs remove all local rank and finite-type choices
and prove that a root-block-valued solution would be spurious.  The only open
input is consequently the finite-support realization of the residual cycle
holonomy by corner unitaries that commute with one binary marginal but do not
normalize the entire root matrix block.
