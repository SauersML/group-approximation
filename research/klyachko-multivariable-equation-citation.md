---
rg: 2
id: klyachko-multivariable-equation-citation
kind: route
title: Klyachko's multivariable corollary, quoted from the arXiv source of his generalized unimodular theorem
target: klyachko-multivariable-equation-with-nonpower-content-solvable
requires: []
artifacts:
  - research/artifacts/hl-howie-systems-2026-09-13.md
---

Source: A. A. Klyachko, arXiv:math/0406382v4, `main.tex`, fetched on MSI into
`/scratch.global/sauer354/hl-kl-torsion/src/0406382/`.

- l.252--254: "Theorem 1'. Any unimodular generalized equation over a
  torsion-free group is solvable over it."
- l.327--336: "Corollary. An equation
  g_1x_{j_1}^{\epsilon_1}g_2x_{j_2}^{\epsilon_2}\dots g_nx_{j_n}^{\epsilon_n}=1
  (**) over a torsion-free group G with variables x_1,x_2,\dots is solvable
  over G if \prod x_{j_i}^{\epsilon_i} is not a proper power in the free group
  F(x_1,x_2,\dots)."
- l.339--357, the proof: the variable group is the universal central extension
  `T` of the one-relator group `T_1 = <x_1, x_2, ... | prod x_(j_i)^(eps_i) = 1>`.
  `T_1` is locally indicable when the content is not a proper power (citing
  Brodskii), hence a UP-group, and the content has infinite order in `T`. So
  (**) is a unimodular generalized equation in the sense of Definition 1
  (l.263--267), and Theorem 1' applies.

The exponent `eps_i` in (**) is the exponent of a single variable letter. A
reduced word in the variables and coefficients, with letters `x^(±1)` separated
by coefficients (possibly `1`), is of this form after conjugating the trailing
coefficient to the front. Conjugation does not change solvability.

The corollary's own proof relies on Brodskii's local indicability theorem and a
fact about universal central extensions (Klyachko's reference [3]); neither was
re-read at source here.
