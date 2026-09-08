---
rg: 2
id: word-taylor-remainder-has-a-fourth-moment-bound
kind: claim
title: The unitary word Taylor remainder is bounded by the fourth normalized moment of the correction
distinct_from:
  normalized-hs-taylor-remainder-is-not-dimension-free: that proves no bound by the squared normalized HS norm exists, using a rank-one spike; this supplies the sharp substitute that does exist, in the fourth normalized moment, and recovers that node's operator-norm interpolation as a corollary.
  iwahori-uniform-infinitesimal-rigidity: that is the first-order lower bound for the Iwahori mismatch map; this is an upper bound for the second-order remainder of an arbitrary word map, with no arithmetic input.
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

**ESTABLISHED.**  Write `||X||_(p,d) = (tr_d |X|^p)^(1/p)` for the normalized
Schatten norms, `tr_d = (1/d) Tr`.  Let `U_1, ..., U_k in U(d)`, let
`X_1, ..., X_k` be self-adjoint, put `U_s(t) = U_s exp(i t X_s)`, and let `w` be
a word of length `ell >= 1` in the letters and their inverses.  Then

```text
|| w(U(1)) - w(U) - D_w(U)[X] ||_(2,d)
      <= (ell^2 / 2) (max_s ||X_s||_(4,d))^2.                          (WT1)
```

The bound is dimension-free and needs no operator-norm smallness hypothesis.

**It refines the archive's interpolated form.**  Since
`tr_d |X|^4 <= ||X||_op^2 tr_d |X|^2`,

```text
||X||_(4,d)^2 <= ||X||_op ||X||_(2,d),                                 (WT2)
```

so `(WT1)` implies the estimate `(NHT1)` of
`normalized-hs-taylor-remainder-is-not-dimension-free`. Equality in `(WT2)`
holds exactly when all nonzero singular values of `X` are equal; in
particular it holds for a scalar multiple of a projection of any rank.

**Effective rank is the quantity that decides.**  For `X != 0` put

```text
theta_eff(X) = ||X||_(2,d)^4 / ||X||_(4,d)^4  in  (0, 1],
```

so that `||X||_(4,d)^2 = ||X||_(2,d)^2 / sqrt(theta_eff(X))`. For one
correction matrix, `(WT1)` reads

```text
remainder <= (ell^2 / 2) ||X||_(2,d)^2 / sqrt(theta_eff(X)).           (WT3)
```

For `X = a P` with `P` a projection of normalized rank `mu = tr_d P` one gets
`theta_eff = mu` exactly. For several correction matrices, use the maximum
of `||X_s||_2^2 / sqrt(theta_eff(X_s))` over nonzero entries.
Hence `||X||_(2,d) = O(e)` and `theta_eff(X) >> e^2` are sufficient for
the bound to give nonlinear remainder `o(e)`. If `||X||_2` is comparable
to `e`, this is exactly the threshold for this upper bound to be `o(e)`.
It is not a necessary condition for the actual remainder: word cancellations
can make that remainder vanish. A normalized rank of order `e^2` therefore
marks a loss of this guarantee, rather than a proof that repair fails.
The rank-one
counterexample of the cited node is the case `mu = 1/d`, and `(WT3)` reproduces
its `sqrt(d)` growth.

This is a bound on one Taylor step.  It does not by itself restore any
Newton iteration; what it supplies is the exact budget such an iteration must
respect when it relies on this estimate, namely sufficient effective rank
relative to the size of the correction.
