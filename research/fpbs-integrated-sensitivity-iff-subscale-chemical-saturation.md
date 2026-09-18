---
rg: 2
id: fpbs-integrated-sensitivity-iff-subscale-chemical-saturation
kind: claim
title: Integrated sensitivity at criticality is equivalent to rate saturation by chemically short paths at slope o(1/epsilon)
artifacts:
  - research/artifacts/fpbs/docs/truncated-russo-lipschitz-2026-09-17.md
distinct_from:
  fpbs-integrated-sensitivity-universal: that is the open universal target (IS); this is an established equivalence, valid for each graph, between (IS) and the chemical-distance condition (SE). It does not prove either one.
  fpbs-integrated-pivotal-rate-identity: that equates (IS) with right-continuity of lambda at pc; this equates that right-continuity with a quantitative truncated-versus-untruncated rate comparison at an explicit sub-mean-field slope.
---

For every nonamenable Cayley graph, the following are equivalent:

* (IS) `lambda(p_c+epsilon) -> rho`;
* (SE) there are slopes `L(epsilon)` with `epsilon L(epsilon) -> 0` and
  `lambda_(L(epsilon))(p_c+epsilon)/lambda(p_c+epsilon) -> 1`.

Quantitative form: suppose (IS) fails with jump
`Delta = lim log(lambda(p_c+epsilon)/rho) > 0`. Then every chemical slope
`L < p_c Delta/epsilon` has truncated rate strictly below `lambda(p_c+epsilon)`.

Truncated pivotal budgets hold automatically (C=L) on every graph, including
a collapse graph. So Russo on truncated events cannot give (IS) or BS. The
content of the pivotal route is precisely the comparison (SE), at a slope
strictly below the mean-field intrinsic scale `p_c log(1/rho)/epsilon`,
which Corollary 3 of the artifact forces under collapse.

Theorem 2 and Section 5 of the artifact.
