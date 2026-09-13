---
rg: 2
id: labelled-thompson-groups-are-acyclic-citation
kind: route
title: Import Palmer–Wu Theorem 2.6 (labelled Thompson groups are acyclic)
target: labelled-thompson-groups-are-acyclic
requires: []
---

Literature import. M. Palmer and X. Wu, "Embedding groups into acyclic
groups", arXiv:2510.16879 (submitted October 19, 2025). Read from the arXiv
HTML on 2026-09-13.

- Theorem 2.6, verbatim: "The labelled Thompson group V(G) is acyclic for any
  discrete group G."
- Definition, §2.1: G-expansion duplicates the label,
  `(g_1, ..., g_{i-1}, g_i, g_i, g_{i+1}, ..., g_n)`.
- Proposition 2.2: "The topological full group of the topological groupoid
  𝒱₂×G is isomorphic to V(G)."
- Lemma 2.4: `H_i(𝒱₂ × G) = 0` for all `i ≥ 0`, from Matui (Theorem 4.14 of his
  2012 paper) and the Künneth formula.

The proof uses Xin Li's theorem on homology of topological full groups
(Theorem 1.16 in the paper). This route imports only the acyclicity statement.
The identification `V(G) ≅ C(C, G) ⋊ V` follows from the label-duplicating
expansion (Lemma B1 of
`research/artifacts/zp-braided-v-rational-acyclicity-2026-09-13-part2.md`).
