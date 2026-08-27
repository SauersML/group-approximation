---
rg: 2
id: chordal-partial-positive-operator-matrices-lift
kind: claim
title: Chordal partial positive operator matrices lift through arbitrary C-star quotients
artifacts:
  - research/artifacts/paulsen-rodman-chordal-positive-lifting-source-2026-08-21.md
distinct_from:
  chordal-abelian-graph-products-hs-stable: that repairs approximate unitary representations of chordal abelian graph products; this lifts partially positive operator matrices through a C-star quotient and is the complete-positivity input for finite operator systems.
  maslov-sector-tracial-generator-ucp-liftability: that asks for one global ucp lift across the nonchordal Deligne presentation; this theorem handles only chordal partial-matrix patterns.
---

Let `B -> B/J` be a unital C-star quotient and let `G` be a finite chordal
graph.  Every partially positive Hermitian matrix over `B/J` whose specified
entries have pattern `G` has a partially positive Hermitian lift over `B` with
the same pattern.

Equivalently, the clique-wise positive data on a chordal graph can be lifted
one simplicial vertex at a time through an arbitrary C-star quotient.  This is
Paulsen--Rodman, *Positive completions of matrices over C-star-algebras*, J.
Operator Theory 25 (1991), Lemma 3.4 together with the chordal perfect-
elimination argument.

The source import is `chordal-partial-positive-operator-matrices-lift-proof`.
