---
rg: 2
id: rich-2to1-via-local-unique-orientation-gadgets
kind: route
title: Dead -- orient each 2-to-1 fiber with a gadget of unique constraints
target: rich-2to1-games-conjecture
requires: []
---

**Dead.**  The attack: since the difficulty is choosing which of the two
preimages `a_0, a_1` a fiber should decode to, attach a small gadget of
unique constraints that makes the choice, and inherit near-perfect
completeness from the source instance.

It is killed by `unique-constraints-orient-at-most-half-of-a-fiber`.
Unique constraints are bijections and compositions of bijections are
bijections, so no network of them sends both `a_0` and `a_1` to the
encoding of `pi(a_0) = pi(a_1)`.  The gadget preserves at most one preimage
per fiber, and adding more of the network does not help: within a connected
component, fixing one boundary label propagates a unique label everywhere,
leaving no freedom for the second element.  That is the structural content
of the `1/2` completeness wall these constructions keep hitting.

Allowing the gadget a commuting-operator strategy does not evade it either:
at perfect completeness such a strategy for a unique game is already a
classical labeling, by this repository's
`perfect-commuting-unique-game-is-classically-satisfiable`.
