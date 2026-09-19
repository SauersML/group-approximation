---
rg: 2
id: pairwise-cross-grams-do-not-supply-one-game-state
kind: claim
title: Positive pairwise cross-Grams do not supply one state good for all contexts
distinct_from:
  one-gram-vector-decodes-a-finite-bcs-strategy: that assumes one common low-energy Gram operator; this gives a different exact Gram state on every edge.
  localized-non-ce-leakage-forces-cross-gram-overlap: that extracts one positive pair overlap; this proves it need not decode the full game.
  consistency-defect-is-state-dependent-distance: that works within one state; this prevents gluing different edge states.
---

For every `k>=3` there are exact commuting context carriers with positive
overlap for every pair and perfect pairwise consistency in an edge-dependent
state, but with zero common intersection.  Their average certified-context
mass is only `2/k`.  Therefore pairwise Gram moments cannot replace one
global game-Laplacian Rayleigh quotient evaluated on a single state.
