---
rg: 2
id: fixed-mark-query-not-limit-computable
kind: claim
title: The fixed non-MF marked query is not limit computable on enumerated presentations
artifacts:
  - GroupApproximation/Computability/EnumeratedFixedMarkedQueryConsequences.lean
distinct_from:
  fixed-mark-query-enumerated-second-level-complete: that is the many-one classification of the query at the second level; this is the operational consequence that no convergent computable classifier (a mind-change learner) recognizes it, proved directly by a recursion-theorem diagonal rather than by quoting the limit lemma.
---

ESTABLISHED (route `fixed-mark-query-not-limit-computable-proof`).  Let
`SURV(c)` be the fixed non-MF marked query of
[[fixed-mark-query-enumerated-second-level-complete]] on standard
enumerated presentation codes.  There is no total computable
`guess : Code x Nat -> Bool` that is eventually constant in the second
argument for every `c` with eventual value `SURV(c)`.  The same holds for
`KILL` and for `InfiniteDomain` and `FiniteDomain`, from which the query
statement follows through the computable many-one reductions of the
completeness theorem.
