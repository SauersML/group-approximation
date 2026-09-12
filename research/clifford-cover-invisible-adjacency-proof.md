---
rg: 2
id: clifford-cover-invisible-adjacency-proof
kind: route
title: Re-choosing the graph on the read pairs moves a strict pair to a surjunctive Clifford cover
target: clifford-cover-strict-pairs-read-invisible-adjacency
requires:
  - strict-pairs-transfer-to-table-realizations
  - clifford-cover-center-separable-iff-graph-is-finite-pullback
  - separated-finite-normal-subgroups-preserve-surjunctivity
  - rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive
  - profinitely-saturated-clifford-covers-are-surjunctive
artifacts:
  - research/artifacts/clifford-cover-orbital-localization-2026-09-12.md
---

Artifact Section 3.

- **Orbital form.** Suppose every relevant edge is `K_E`-clean. Cleanliness passes to smaller `K`, so
  `K = intersection K_E` works for all of them. The graph `S'`, pulled back from the orbits of the relevant
  edges' images on `K\X`, agrees with `S` on `R` and is a finite pullback. So `E_(S')` is surjunctive
  (Theorem A and the separated theorem over the surjunctive wreath). The identity on coordinates satisfies
  the product identities of the table-realization theorem, so `E_(S')` carries a strict pair.
  Contradiction.
- **Coset form.** The orbital form, read through Lemma 2.1 and double cosets.
- **Holonomy form.** If no component has such a pair, send the site `w x_0` of component `i` to
  `w Hol_i-bar` in the `i`-th orbit of `X' = disjoint union of G/Hol_i-bar`. This map is well defined,
  injective, equivariant for the read moves, and order-embeddable. The complete graph on `X'` has closed
  stabilizers, so it is saturated and `E(X')` is surjunctive. Transfer as before.
