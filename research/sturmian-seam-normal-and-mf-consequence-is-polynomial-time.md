---
rg: 2
id: sturmian-seam-normal-and-mf-consequence-is-polynomial-time
kind: claim
title: Fixed quadratic Sturmian graph groups have polynomial-time word, normal-closure and MF-consequence algorithms
root: true
distinct_from:
  monotone-mf-implications-use-commuting-involution-relators: that constructs selected word implications from a formula; this decides arbitrary finite word implications inside each fixed computable graph group.
artifacts:
  - research/artifacts/pestov91-finite-normal-control-2026-09-13.md
---

For each fixed finite directed graph, take all endpoint systems to
have slope `sqrt(2)-1` and the mechanical seam points of intercept
`1/2`. In its three-generator group the word problem, normal-closure
membership for finitely many input words, and MF semantic consequence
for those inputs are decidable in polynomial time in total expanded
word length.

The original tagged language has exact complexity
`|V|(h+1)+|E|h`. Its binary coding has linear complexity and polynomial
enumeration. Evaluating normal forms window by window costs `O(L^3)`
field operations. Endpoint and edge identity tests give the normal
label; unions and cycle pruning decide ordinary and MF consequences.
No polynomial bound in compressed-DAG size is claimed.
