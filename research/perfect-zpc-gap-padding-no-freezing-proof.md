---
rg: 2
id: perfect-zpc-gap-padding-no-freezing-proof
kind: route
title: Mix the perfect gap verifier with the finite pinned magic-square selector
target: perfect-zpc-gap-padding-can-destroy-all-frozen-branches
requires:
  - perfect-zpc-irs-quantum-gap-game
  - finite-magic-square-selector-has-no-frozen-branch
---

Take the disjoint probabilistic mixture described in the target.  ZPC
strategies are closed under finite products and disjoint verifier mixtures,
so the two perfect strategies give value one.  Every strategy's conditional
behavior on the original checks is a strategy for the original game, giving
the strict upper bound `(ZPD2)`.

Freezing is monotone in the opposite direction: the padded frozen equation
set contains the gadget's frozen equation set.  Since that subset already
forces `J=1`, no choice of the original readable coordinates can restore a
negative-central representation.  This proves all assertions.
