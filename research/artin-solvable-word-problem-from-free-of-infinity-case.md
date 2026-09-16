---
rg: 2
id: artin-solvable-word-problem-from-free-of-infinity-case
kind: route
title: A solvable word problem for every Artin group follows from the case of graphs with only finite labels
target: every-artin-group-has-solvable-word-problem
requires:
  - artin-word-problem-reduces-to-free-of-infinity-graphs
  - every-free-of-infinity-artin-group-has-solvable-wp
---

Let `Γ` be a finite Coxeter graph on `S`.

1. For every maximal free-of-infinity `X ⊆ S`, the graph `Γ_X` has only finite labels.
   So `A_{Γ_X}` has solvable word problem by
   `every-free-of-infinity-artin-group-has-solvable-wp`.
2. Then `artin-word-problem-reduces-to-free-of-infinity-graphs` shows that `A_Γ` has
   solvable word problem.

The converse is a special case, so this route is an equivalence. It is still a genuine
narrowing, not a restatement. The prerequisite says nothing about graphs with infinite
labels. The passage to them is the splitting
`A_Γ = A_{S∖{s}} *_{A_{S∖{s,t}}} A_{S∖{t}}` along a label `m_st = ∞`, together with the
Godelle–Paris membership algorithm.
