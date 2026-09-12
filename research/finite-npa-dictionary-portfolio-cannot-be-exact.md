---
rg: 2
id: finite-npa-dictionary-portfolio-cannot-be-exact
kind: claim
title: No finite portfolio of finite moment dictionaries characterizes the quantum set
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

In the `(2,2,2)` scenario, let `S_1, ..., S_m` be any finite collection of finite
NPA word dictionaries, chosen by any rule whatsoever, and let `Q_(S_i)` denote
the relaxation built from `S_i`.  Then

```text
intersection over i of Q_(S_i)   strictly contains   Q.
```

The same holds for any finite adaptive decision tree of moment-selection tests:
every dictionary the tree can ever request is finite and there are finitely many
of them, so the conclusion applies to the family of all of them.

Consequently no selection rule -- greedy, Bayesian, reinforcement-learned, or
budget-aware -- can make a fixed finite master dictionary complete.  Completeness
requires unbounded dictionary growth, and this is independent of whether the
moment objective is submodular, synergistic, or learned.  It is the exact
obstruction facing moment-selection work such as arXiv:2607.14755, which
optimizes which moments to add under a computational budget.

The statement is a corollary, not a new mechanism: monotonicity of the
relaxation does all the work once one finite level is known to be inexact.
