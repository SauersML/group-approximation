---
rg: 2
id: fp-strongly-shift-similar-type-a-citation
kind: route
title: Import Zaremsky Proposition 5.3
target: fp-strongly-shift-similar-admits-type-a-action
requires: []
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Citation import.  Zaremsky, arXiv:2405.18354, Proposition 5.3, read from
source 2026-08-24 and quoted verbatim in the target node.  Not reproved here
and no Lean counterpart exists.

## What is load-bearing

That the conclusion is an action **of type (A)** rather than merely a
finitely presented twisted Brin--Thompson group.  Type (A) is what
`type-a-action-gives-boone-higman-for-subgroups` consumes, and it is what
carries the conclusion down to subgroups; a statement only about `SV_G`
would leave the embedding of the group one actually started from to be
redone by hand.
