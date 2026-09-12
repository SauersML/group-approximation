---
rg: 2
id: zalesskii-idempotent-trace-is-rational
kind: claim
title: The trace of an idempotent in a group algebra over a field of characteristic zero is rational
distinct_from:
  weak-bass-fixed-two-generator-all-group-tester: that reduces the integral weak Bass identity to one universal host; this is Zalesskii's theorem that the Kaplansky trace of any idempotent over any characteristic-zero field is rational, for every group
---

**ESTABLISHED (literature import).** Let `K` be a field of characteristic
zero, `G` any group, and `e in K[G]` an idempotent. Then the coefficient of
the identity, `tr(e) = e(1)`, lies in `Q`.

This is the rationality half of Kaplansky's trace problem, proved by
Zalesskii (1972) for every group, with no approximation hypothesis. Kaplansky
had shown `0 <= tr(e) <= 1` over `C`.

The matrix form, `sum_i e_ii(1) in Q` for idempotent `e in M_n(K[G])`, is
derived from this statement in Step 3 of
`finite-spectrum-integral-determinant-proof`, through a Wedderburn component of
`Q[S_(n+1)]`.
