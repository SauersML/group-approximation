---
rg: 2
id: type-a-action-boone-higman-subgroups-citation
kind: route
title: Import Zaremsky Corollary B
target: type-a-action-gives-boone-higman-for-subgroups
requires: []
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Citation import.  Zaremsky, *Finite presentability of twisted Brin--Thompson
groups*, arXiv:2405.18354, Corollary B, together with the definition of type
(A) preceding Theorem A.  Read from source 2026-08-24; quoted verbatim in the
target node.

Not reproved here and no Lean counterpart exists.

## What is load-bearing

The four clauses of type (A) and the word "subgroup".  Everything downstream
uses the corollary as a black box that turns a permutation action into an
embedding into a finitely presented simple group, and the only thing that
could break a route built on it is a change to one of the four clauses --
in particular to faithfulness, which is the clause that a construction is
most tempted to give up and which is exactly the clause that supplies
simplicity of `SV_G`.
