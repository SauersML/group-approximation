---
rg: 2
id: stw83-finite-graphs-are-complete-test
kind: claim
title: Finite graphs are a complete test for the graph nuclear-dimension problem
distinct_from:
  stw83-problem-lxxxiii-graph-nuclear-dimension: that asks for all directed graphs; this proves the all-graphs statement follows from the finite-graph case but does not settle that finite case.
  stw83-hereditary-finite-exhaustion-preserves-one: that assumes a hereditary vertex exhaustion and row-finiteness; this constructs finite graph-algebra subalgebras for arbitrary finite generator packets, including at infinite emitters.
---

**ESTABLISHED.**  If every finite directed graph `F` satisfies

```text
dim_nuc(C*(F))<=1,
```

then every directed graph `E` satisfies `dim_nuc(C*(E))<=1`.
The converse restriction is immediate, so finite graphs are an exact complete
test for STW Problem LXXXIII.

DERIVATION
[[stw83-finite-graph-test-proof]]
