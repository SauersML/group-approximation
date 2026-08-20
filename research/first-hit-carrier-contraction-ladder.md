---
rg: 2
id: first-hit-carrier-contraction-ladder
kind: claim
title: Persistent carriers and orthogonal first-hit exits force a linear reservoir collapse
distinct_from:
  contractive-computation-ladder: that sums an exponentially contracting scalar recurrence; this is the complementary accounting lemma for a carrier which persists while emitting orthogonal rank-jump exits.
  one-sided-paired-frame-reverse-reservoir-collapse: that must construct the carriers and exits from fixed group words; this is the exact scalar ledger needed once those word-level estimates exist.
---

Let `q_0,...,q_(N-1)` and `r_0,...,r_(N-1)` be nonnegative.  Think of `q_n`
as the trace of the transported active carrier and `r_n` as the trace of its
new reverse first-hit exit.  Suppose

```text
q_0 <= q_n + Delta_n,             Delta_n>=0,          (FHC1)
r_n >= eta q_n - epsilon_n,       epsilon_n>=0,        (FHC2)
sum_(n<N) r_n <= 1,               eta>0.               (FHC3)
```

Then

```text
N eta q_0
 <= 1 + eta sum_(n<N) Delta_n + sum_(n<N) epsilon_n.  (FHC4)
```

In particular, if fixed-word transport gives

```text
Delta_n <= C p(n) sqrt(E),
epsilon_n <= C p(n) sqrt(E)
```

for a polynomial `p`, then a polynomial `P` and dimension-independent `C'`
give

```text
N q_0 <= eta^(-1) + C' P(N) sqrt(E).                  (FHC5)
```

This identifies the orientation required from a one-sided packet compiler.
It is not enough that a surviving carrier shrink after each forbidden event:
that permits a geometric first-hit distribution.  One baseline packet copy
must persist as in `(FHC1)`, while the predicate rank jump emits an additional
exit as in `(FHC2)`.  Literal orthogonality, or any uniform summable-overlap
replacement, supplies `(FHC3)`.
