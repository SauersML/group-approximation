---
rg: 2
id: stw83-condition-k-finite-completion-reduction
kind: claim
title: Countable row-finite Condition-(K) graphs admit an injective finite-completion reduction
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
---

Let `E` be a countable row-finite directed graph with Condition (K).  There is an
increasing sequence of finite subgraphs `E_n` with Condition (K) such that the
canonical generator maps are injective and

```text
C*(E) = direct_limit_n C*(E_n).
```

Consequently, for every fixed nonnegative integer `d`, if
`dim_nuc(C*(E_n)) <= d` for all `n`, then

```text
dim_nuc(C*(E)) <= d.
```

The finite graphs are entrance completions.  The statement is not valid with an
arbitrary increasing sequence of finite induced subgraphs: omitting an edge at a
regular vertex can violate the Cuntz--Krieger relation and prevent the canonical
generator assignment from defining an injective *-homomorphism.
