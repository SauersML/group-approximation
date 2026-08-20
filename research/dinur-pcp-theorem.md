---
rg: 2
id: dinur-pcp-theorem
kind: claim
title: NP has logarithmic-randomness constant-query probabilistically checkable proofs
distinct_from:
  dinur-constraint-gap-amplification: that is the one-step constraint-graph transformation; this is the complexity-theoretic consequence obtained by iterating it and translating gap CSPs to verifiers.
---

Every language in `NP` has a probabilistic verifier with perfect completeness,
soundness at most `1/2`, `O(log n)` random bits, and `O(1)` nonadaptive proof
queries.  Equivalently,

```text
NP subset PCP[O(log n), O(1)].
```

In gap-CSP form, there are constants `q > 1` and `|Sigma| > 1` for which it is
NP-hard to distinguish a finite `q`-ary constraint system with `UNSAT = 0`
from one with `UNSAT >= 1/2`.

The equivalence uses one constraint per verifier random string in one
direction, and a verifier which samples and checks one uniformly random
constraint in the other.
