---
rg: 2
id: decidable-fp-groups-embed-in-perfect-decidable-fp-groups
kind: claim
title: Every finitely presented group with decidable word problem embeds effectively in an infinite perfect group with the same properties
artifacts:
  - research/artifacts/boone-higman-perfect-shell-route-2026-09-08.md
---

Given a finite presentation of P and an algorithm for its word problem,
one can construct a finite presentation of an infinite perfect group
W(P), words defining an embedding P->W(P), and a word-problem algorithm
for W(P).

The construction uses two HNN extensions of P times P, followed by
an amalgamation over a free group of rank two with A_5 * A_5. Both
edge-membership problems in the amalgamation are decidable, with
effective rewriting into the edge generators. This explicitly retains
decidability as well as the embedding and finite presentation.

In particular, after the existing Clapham embedding, restricting the
input to infinite perfect finitely presented groups with decidable word
problem loses no generality in a universal Boone--Higman construction.
