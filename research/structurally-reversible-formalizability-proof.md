---
rg: 2
id: structurally-reversible-formalizability-proof
kind: route
title: A shear rewrites one track from the others, so applying it twice adds the same polynomial twice
target: structurally-reversible-automata-are-formalizable
requires: []
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

Section 1 of the artifact.
- **Shears.** A track shear changes only coordinate `i`, at every site, and its polynomial `f` reads
  no coordinate `i`. So a second application reads the same inputs, and coordinate `i` becomes
  `X + f + f = X` in characteristic 2.
- **Other gates.** Linear maps and translations are formally invertible.
- **Words.** Substitution is associative, so the reversed word of inverse gates is a two-sided formal
  inverse, and formal pairs compose.
- **Regrouping.** Regrouping along a finite-index subgroup keeps the polynomial variables, and matrix
  rings over `F_2[H]` are unital subrings of those over `F_2[G]`.
- **Strict automata.** Words of bijections are bijective, so no strict automaton is a word.
