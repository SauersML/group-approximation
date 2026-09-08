---
rg: 2
id: binary-jacobson-matrix-rings-have-no-infinite-corner
kind: claim
title: No finite matrix ring over the binary Jacobson algebra has a nonzero properly infinite idempotent
invalidates:
  - jacobson-head-collapse-via-properly-infinite-corner
distinct_from:
  properly-infinite-corner-forces-non-mf-from-rank-two: that is the positive theorem drawing non-MF from a properly infinite corner; this proves the certificate is unavailable in the first open case, so the theorem cannot be applied there.
  binary-leavitt-algebra-not-directly-finite: that records a nonzero defect in the Leavitt algebra, a strictly weaker condition than proper infiniteness of an idempotent; this rules out proper infiniteness of every idempotent in every finite amplification of a different algebra.
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that is a group-level finite-quotient obstruction; this is a ring-level nonexistence statement about idempotents and mentions no homomorphism.
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

**ESTABLISHED.**  Let `J = F_2<S,T | TS = 1>`.  For every finite `d >= 1`,
the ring `M_d(J)` contains **no** nonzero properly infinite idempotent:
there are no

```text
0 != p = p^2 in M_d(J),   x_0,x_1,y_0,y_1 in p M_d(J) p,
y_i x_j = delta_(ij) p.                                           (NIC1)
```

Consequently the hypothesis of
`properly-infinite-corner-forces-non-mf-from-rank-two` is **unavailable**
for the binary Jacobson algebra, and stays unavailable after arbitrary
finite matrix amplification.

This locates the exact failure.  Any proposed properly infinite corner
has zero symbol, hence lies in the finitary ideal; and its whole corner
then sits inside a finite-dimensional matrix algebra over `F_2`, where
the same obstruction reappears.  The obstruction is a dimension count in
ordinary finite-dimensional linear algebra; it introduces no rank metric,
displacement metric, or substitute for an operator norm.

So the corner certificate genuinely extends the full-defect theorem, and
genuinely cannot decide the binary Jacobson endpoint.  Which side of
`binary-jacobson-mark-dichotomy-holds-from-rank-two` holds must be
decided by other means; at rank five it is decided by
`binary-jacobson-steinberg-head-root-is-mf-invisible`.

DERIVATION
binary-jacobson-no-infinite-corner-proof
