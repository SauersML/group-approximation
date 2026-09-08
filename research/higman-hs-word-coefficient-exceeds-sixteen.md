---
rg: 2
id: higman-hs-word-coefficient-exceeds-sixteen
kind: claim
title: A rational three-dimensional Higman tuple rules out coefficient sixteen
distinct_from:
  higman-hs-word-coefficient-exceeds-nine-fifths: that exhibits a two-dimensional obstruction above nine fifths; this uses a three-dimensional tuple to refute even sixteen, beyond the range of the two-dimensional search.
  failed-hs-word-bounds-have-rational-witnesses: that semidecides failure of a specified coefficient; this provides explicit matrices and exact separating bounds for the Higman four-cycle.
artifacts:
  - research/artifacts/higman-qutrit-coefficient-bound.md
  - research/artifacts/higman-qutrit-coefficient-witness.json
  - experiments/higman_qutrit_witness.py
  - experiments/hs_word_certificate.py
---

For the Higman four-cycle relators, the specified rational U(3) tuple has
marked energy greater than 16/7 and total relator energy strictly between
zero and 1/7. Therefore every coefficient C in a dimension-independent
bound `e_(g_0)<=C sum_j e_(r_j)` must exceed sixteen.

This refutes coefficients two and sixteen. It proves neither validity
of any larger coefficient nor a separating sequence of approximate
representations. Nonhyperlinear existence remains open.
