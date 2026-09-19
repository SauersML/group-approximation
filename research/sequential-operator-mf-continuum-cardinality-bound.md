---
rg: 2
id: sequential-operator-mf-continuum-cardinality-bound
kind: claim
title: The unrestricted sequential operator-MF predicate has a continuum cardinality ceiling
distinct_from:
  finite-matrix-quotient-cardinality-width-bound: that treats arbitrary index cardinality and arbitrary finite-unitary quotients; this is the sequential norm-corona specialization and records its consequence for the universe-polymorphic formal predicate.
artifacts:
  - GroupApproximation/Sofic/OperatorMF.lean
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

For every sequence of positive matrix sizes `d_n`,

```text
|U((product_n M_(d_n)(C))/(directSum_n M_(d_n)(C)))|
 <= continuum.                                            (SCB1)
```

Therefore every group satisfying the universe-polymorphic predicate
`IsOperatorMF` has cardinality at most the continuum.

This is a theorem about the predicate as formally defined for arbitrary
groups.  It is not an obstruction for the standard countable group-MF
problem: every countable group lies below the cardinal ceiling.
