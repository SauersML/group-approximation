---
rg: 2
id: nonsurjunctive-via-invariant-output-automaton
kind: route
title: An injective coset-invariant-output automaton misses every non-invariant configuration
target: leavitt-unit-group-nonsurjunctive
requires: [leavitt-units-carry-injective-invariant-output-automaton, invariant-output-injective-automata-need-invisible-symmetry]
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

The first prerequisite supplies an injective `tau` whose output is constant on
right cosets of a finite `H != 1`. The second records that such `tau` is not
surjective: a two-cell pattern on `{1,h}` with distinct symbols has no preimage.
So `tau` is injective and not surjective, which is the target.

The certificate in the shared checker format is `{tau, sigma, orphan}` with the
orphan on `{1, h}`. `certcheck.py` verifies `sigma o tau = id` exactly over the
Leavitt normal form and searches the orphan exhaustively.
