---
rg: 2
id: structurally-reversible-automata-are-formalizable
kind: claim
title: Words in track shears, sitewise linear maps and constant translations form formalizable pairs with their reversed words, on every group
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that asks formalizability of every binary left-inverse pair; this proves it for the structurally reversible class, which contains no strict automaton.
  multilinear-collapse-defect-does-not-obstruct-bijectivity: that calibrates one sitewise Toffoli pair whose canonical representatives are not formal; this proves every word of gates with arbitrary memories is formalizable, including after regrouping along a finite-index subgroup.
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

Let `G` be a group and `A = F_2^n`. The following gates on `A^G` are formally invertible:
- a *track shear* `x(g)_i -> x(g)_i + f((x(gm)_j)_(m in M, j != i))`, for any finite `M` and any
  polynomial `f` that reads no coordinate `i`. It is a formal involution;
- a sitewise map in `GL_n(F_2)`;
- a constant translation.

A finite word `W` in these gates is *structurally reversible*. Its reversed word is a two-sided
formal inverse. So `W` is bijective and forms a formalizable pair with its inverse.

The same holds for words of gates over a finite-index subgroup `H`, acting on the regrouped
alphabet `A^T`, where `T` is a transversal. Such pairs still give the Kaplansky payoff:
`M_N(F_2[H])` is a unital subring of `M_N(F_2[G])`.

Formal pairs compose. The sitewise permutations are the case `M = {1}`. A strict automaton is never
structurally reversible.

Proof: Section 1 of the artifact.
