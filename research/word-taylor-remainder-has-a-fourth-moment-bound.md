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
`normalized-hs-taylor-remainder-is-not-dimension-free`, and is strictly
stronger whenever the correction is not close to a scalar multiple of a
projection of full normalized rank.

**Effective rank is the quantity that decides.**  For `X != 0` put

```text
theta_eff(X) = ||X||_(2,d)^4 / ||X||_(4,d)^4  in  (0, 1],
```

so that `||X||_(4,d)^2 = ||X||_(2,d)^2 / sqrt(theta_eff(X))` and `(WT1)` reads

```text
remainder <= (ell^2 / 2) ||X||_(2,d)^2 / sqrt(theta_eff(X)).           (WT3)
```

For `X = a P` with `P` a projection of normalized rank `mu = tr_d P` one gets
`theta_eff = mu` exactly.  Hence a correction with `||X||_(2,d) = O(e)` has
nonlinear remainder `o(e)` if and only if `theta_eff(X) >> e^2`: a correction
that is small in normalized HS norm but concentrated on normalized rank `O(e^2)`
sits exactly at the threshold where the step stops gaining.  The rank-one
counterexample of the cited node is the case `mu = 1/d`, and `(WT3)` reproduces
its `sqrt(d)` growth.

This is a bound on one Taylor step.  It does not by itself restore any
Newton iteration; what it supplies is the exact budget such an iteration must
respect, namely a lower bound on the effective rank of every correction it
makes.
