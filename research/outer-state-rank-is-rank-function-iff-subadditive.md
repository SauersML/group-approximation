---
rg: 2
id: outer-state-rank-is-rank-function-iff-subadditive
kind: claim
title: The outer rank of a K_0 state is a Sylvester rank function exactly when it is subadditive on block sums
distinct_from:
  rank-functions-extending-a-state-are-pinned-on-regular-elements: that bounds every extension of a state between the outer and inner s-ranks and pins regular elements; this shows the outer s-rank satisfies every Sylvester axiom except subadditivity, so subadditivity alone makes it the smallest extension.
  k0-state-extends-to-rank-function-iff-triangular-monotone: that characterizes the states that extend to some rank function; this gives a sufficient, explicit extension, the outer s-rank.
artifacts:
  - research/artifacts/separated-triangular-certificates-flatten-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `outer-state-rank-subadditivity-criterion-proof`. Verification requested from
`w4-vf-linear-b`.

Let `s` be a state on `(K_0(A), [A])` and `rho^s(X) = sup s([f])` over idempotent matrices `f <~ X`. Then:
- **Normalization.** `rho^s(0) = 0`, `rho^s(1) = 1`, and `rho^s(e) = s([e])` on idempotents.
- **Monotonicity.** It is monotone for minors, and `rho^s(XY) <= min(rho^s X, rho^s Y)`.
- **Two axioms.** It is superadditive on block sums, and it satisfies the triangular axiom
  `rho^s([[X, C], [0, Y]]) >= rho^s(X) + rho^s(Y)`.

So `rho^s` is a Sylvester matrix rank function iff `rho^s(X (+) Y) <= rho^s(X) + rho^s(Y)` for all `X`,
`Y`. It is then the smallest rank function agreeing with `s` on idempotents.

**Use.** A weakly finite image of `S_-` (as in `anti-central-weakly-finite-images-carry-rank-functions`)
carries a rank function as soon as one of its states has a subadditive outer s-rank. Subadditivity can
fail only through an idempotent below `X (+) Y` whose minor mixes the two blocks.

Proof: Section 3 of the artifact.
