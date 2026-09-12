---
rg: 2
id: stw12-faithful-invariant-trace-af-criterion
kind: claim
title: Faithful invariant traces exactly characterize simple-AF embeddability of AH integer crossed products
distinct_from:
  stw99-problem-xii-ah-rr0-crossed-qd-afe: that asks whether quasidiagonality alone forces embedding into some AF algebra; this characterizes the stronger conclusion of embedding into a unital simple AF algebra and proves the simple crossed-product case.
  stw12-periodic-actions-over-af-embeddable-algebras: that uses outer periodicity and a Floquet embedding without traces; this applies to arbitrary automorphisms and is exact in terms of invariant traces.
artifacts:
  - research/artifacts/stw12-faithful-invariant-trace-criterion-audit-2026-08-30.md
---

Let `A` be a separable unital AH algebra and let `alpha in Aut(A)`.  Then

```text
A rtimes_alpha Z embeds into a unital simple AF algebra
    iff
A has a faithful alpha-invariant tracial state.                (SFIT)
```

No real-rank-zero, quasidiagonality, simplicity, or periodicity assumption
is needed for this equivalence.  In particular, a faithful invariant trace
is sufficient for ordinary AF-embeddability.

Consequently, Problem XII has a positive answer whenever the quasidiagonal
crossed product is simple.  The converse direction for ordinary
AF-embeddability is deliberately not asserted: embedding into a nonsimple AF
algebra need not produce a faithful trace.
