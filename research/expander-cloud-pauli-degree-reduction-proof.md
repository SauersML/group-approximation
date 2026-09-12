---
rg: 2
id: expander-cloud-pauli-degree-reduction-proof
kind: route
title: Apply Poincare to occurrence reflections and choose one representative per cloud
target: expander-cloud-reduction-preserves-pauli-dimension-gap
requires: []
---

For reflections `A,B` in a tracial strategy, the rejection probability of
their equality test is

```text
(1-Re tau(AB))/2 = ||A-B||_2^2/4.                               (1)
```

Let `bar A_q` be the average of the occurrence reflections in the expander
cloud for `q`.  The expander Poincare inequality gives, with the natural
incidence weights,

```text
Avg_t ||A_(q,t)-bar A_q||_2^2
 <= lambda^-1 Avg_(tt' edge) ||A_(q,t)-A_(q,t')||_2^2.          (2)
```

If the degree-reduced rejection is `delta`, averaging `(2)` over `q` shows
that a random occurrence `r(q)` satisfies

```text
Avg_(q,t) ||A_(q,t)-A_(q,r(q))||_2^2 <= C delta/lambda.         (3)
```

Choose the representatives deterministically with no larger weighted sum.
They are already reflections on the original Hilbert space.  Replacing at
most `k` occurrence operators in an old test by these representatives and
telescoping its correlation changes the average rejection by at most

```text
C_k sqrt(delta/lambda).                                        (4)
```

The old tests themselves contribute at most a fixed multiple of `delta`.
Hence the decoded `P_N` strategy has rejection at most

```text
C'(delta+sqrt(delta/lambda)).                                  (5)
```

Choose `eta_1` so that `(5)<eta_0`.  The dimension hypothesis for `P_N`
then gives `(ECD1)`.  A perfect strategy is copied identically across each
cloud, proving perfect completeness.

