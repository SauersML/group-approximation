---
rg: 2
id: stw83-finite-source-dichotomy-dimension-one
kind: claim
title: The finite Condition-(K) source dichotomy forces nuclear dimension at most one
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
---

Let `F` be a finite graph with Condition (K).  Suppose that every source `v` of
`F` satisfies one of the following mutually compatible alternatives:

1. `v` connects to every cycle in `F`;
2. `v` connects to no cycle in `F`.

Then

```text
dim_nuc(C*(F)) <= 1.
```

It is zero when `F` is acyclic and exactly one when `F` contains a cycle.
