---
rg: 2
id: log-depth-rate-rounding-is-equivalent-to-unit-type
kind: claim
title: For each representation of the Theorem E actor, vertex rounding with a log-depth rate, unit-type rounding, and rounding with vanishing deep non-unit mass are equivalent
distinct_from:
  vertex-rounding-with-log-depth-rate: that is the open rate hypothesis; this proves it is exactly as strong as unit-type rounding, so it is not a weaker intermediate target.
  theorem-e-vertex-rounds-to-unit-type-representations: that is the open crux; this proves three existence statements equivalent to it for each representation, with no new input.
  vertex-rounding-deep-nonunit-root-mass-vanishes: that asks the deep non-unit mass of the supplied roundings to vanish; this shows that the existence of one rounding with vanishing deep mass is already equivalent to the crux.
  nonunit-root-mass-log-depth-scale-bound: that is the established one-way bound from the rate to unit type; this adds the converse directions and records the resulting goal-equivalence.
artifacts:
  - research/artifacts/nh-log-depth-rate-2026-09-12.md
---

**ESTABLISHED.** Let `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, `r, d >= 3`, and fix a
trace-preserving `σ : G -> U(prod_U M_n)`. The following are equivalent.

(a) **Rate.** (H1) holds with roundings `π_n` such that `δ_n^2 · log(1 + D(π_n)) -> 0` along `U`, as in
`vertex-rounding-with-log-depth-rate`.

(b) **Unit type.** (H1) holds with roundings that factor through `St_r(R_+/I_n)` with every `x_i` a unit,
as in `theorem-e-vertex-rounds-to-unit-type-representations`.

(c) **Deep mass.** (H1) holds with roundings `π_n` such that `μ_n(depth_nu > 1) -> 0` along `U`.

**Consequences.**
- The log-depth rate is not an easier target than the crux. Any proof of (a) already proves (b), and
  (b) gives (a) with `D = 0`.
- A counterexample to the crux for `σ` must defeat all three at once: every (H1) rounding of `σ` carries
  order-one non-unit mass above depth one. By `nonunit-root-mass-log-depth-scale-bound` such mass spreads
  over at least order `1/η_n` d-adic blocks.
- Quantitative rates in `n` or in `D_n` add nothing beyond (c). The whole content is vanishing of deep
  non-unit mass for one choice of rounding.

Derivation: `log-depth-rate-unit-type-equivalence-proof`. No root is affected.
