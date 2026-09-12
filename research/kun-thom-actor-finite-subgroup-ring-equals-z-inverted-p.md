---
rg: 2
id: kun-thom-actor-finite-subgroup-ring-equals-z-inverted-p
kind: claim
title: The finite-subgroup ring of a Kun--Thom Theorem E actor is exactly Z[1/P(q,r,d)]
distinct_from:
  kun-thom-actor-finite-subgroup-ring-has-finitely-many-primes: that bounds the primes dividing finite-subgroup orders by P(q,r,d); this realizes every prime of P(q,r,d) as an element order, so the trace-test target ring equals Z[1/P].
artifacts:
  - research/artifacts/bc-kun-thom-trace-test-2026-09-12.md
---

**ESTABLISHED.** Let `q = p^f`, `r, d >= 3`, `R = F_q[x_1^(+-1), ..., x_d^(+-1)]` and
`G = EL_r(R) semidirect SL_d(Z)`, the actor of a Kun--Thom Theorem E pair. Then

```text
Lambda^G = Z[ 1/|H| : H <= G finite ] = Z[ 1/l : l in P(q,r,d) ],
P(q,r,d) = {p} union {l : l | q^k - 1, 1 <= k <= r} union {l : l <= d + 1}.
```

**Why it matters.** It pins down the target of Lück's trace test for these groups. A projection in
`M_n(C*_r G)` refutes surjectivity of the reduced assembly map exactly when its trace lies outside
`Z[1/P(q,r,d)]`. See `baum-connes-counterexample-group-exists`.
