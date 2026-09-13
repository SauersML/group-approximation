---
rg: 2
id: quotientless-hyperbolic-from-kazhdan-quotientless
kind: route
title: Forget property (T) - a finite-quotient-free hyperbolic Kazhdan group is a finite-quotient-free hyperbolic group
target: hyperbolic-group-without-finite-quotients
requires:
  - kazhdan-hyperbolic-group-without-finite-quotients
artifacts:
  - research/artifacts/nrfh-kazhdan-quotientless-2026-09-12.md
---

An infinite word-hyperbolic Kazhdan group with no nontrivial finite quotient is,
after forgetting property (T), an infinite word-hyperbolic group with no
nontrivial finite quotient.

**Why the edge is needed.**
- Before this route, the only consumer of the Kazhdan target was
  `non-mf-hyperbolic-from-kazhdan-quotientless`.
- That route also requires the open
  `mf-kazhdan-group-without-finite-quotients-is-trivial`.
- So a proof of the Kazhdan target did not reach
  `non-residually-finite-hyperbolic-group` in the graph, for instance one through
  `kazhdan-quotientless-hyperbolic-from-sp21-quotient`.
- Yet it reaches the root at once: through this route, then
  `non-rf-hyperbolic-from-quotientless-hyperbolic`.

`hyperbolic-rf-vtf-kazhdan-equivalence` records this implication in prose. This
route is the corresponding edge.

This route and `kazhdan-quotientless-hyperbolic-via-common-quotient`, which adds
(T) back, form an intended equivalence cycle. Do not delete either one to silence
the cycle warning. The audit is in the artifact, §1.
