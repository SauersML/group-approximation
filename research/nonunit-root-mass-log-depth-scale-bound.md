---
rg: 2
id: nonunit-root-mass-log-depth-scale-bound
kind: claim
title: Under vertex rounding, non-unit root mass is at most the transport defect times log of the maximal non-unit depth, which is at most log log n
distinct_from:
  nonunit-component-root-mass-is-log-scale-folner: that counts 1 + log_d(r(r-1)n') d-adic scales from a crude depth bound; this counts 1 + log_d max(1, D_n), with D_n the maximal non-unit depth occurring, which is at most log_q n'.
  shallow-nonunit-root-mass-vanishes-under-vertex-rounding: that closes the shallow case and states the corollary with a log n scale count; this sharpens the corollary to a log of the intrinsic maximal depth, at most log log n.
  root-character-nonunit-depth-at-most-log-q-dimension: that is the unconditional depth bound for congruence representations; this feeds it into the transport-defect Følner bound under (H1).
  vertex-rounding-deep-nonunit-root-mass-vanishes: that asks the deep non-unit mass to vanish with no rate; this proves it is at most eta_n(1 + log_d max(1, D_n)) with D_n <= log_q n'.
  vertex-rounding-non-unit-mass-at-origin: that confines non-unit mass to the origin and bounds its profile scale by scale; this caps the number of scales by the log of the maximal depth, itself at most log log n.
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

**ESTABLISHED.** Take the setting and hypotheses of
`compressor-transport-exactifies-under-vertex-rounding`: `η_n = 4δ_n^2/κ^2`, `μ_n` the normalized
spectral measure of `f -> π_n(e_12(f))`, and `P_n` as in
`unit-type-vertex-rounding-forces-compressor-commutant-rigidity`. Put `D_n = D(π_n)`, the maximal
non-unit depth on the support of `μ_n`, as in `root-character-nonunit-depth-at-most-log-q-dimension`.
Let `η_n^t` be as in `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`.

1. **Log-depth Følner bound.**

   ```text
   μ_n(depth_nu > 1)  <=  η_n · (1 + log_d max(1, D_n)),     D_n <= log_q n'.
   ```

2. **Non-unit projection.**

   ```text
   τ(1 - P_n)  <=  r(r-1) · [ (q + 1 + log_d max(1, D_n))·η_n + η_n^t ].
   ```

3. **Rate.** Under (H1), the rounding is of unit type (`τ(1 - P_n) -> 0` along `U`) whenever
   `δ_n^2 · log(1 + D_n) -> 0`. In particular it suffices that `δ_n^2 · log log n -> 0`.

**Reading.**
- **Old rate.** The corollary of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` needed
  `δ_n^2 log n -> 0`. The scale count is now the log of the intrinsic maximal depth.
- **What a counterexample needs.** Order-one non-unit mass `c` above depth one must spread over at least
  `c/η_n` d-adic blocks. So `D_n > d^(c/η_n - 1)`, and by the depth bound some constituent of `π_n` has
  dimension at least `q^(D_n)`: doubly exponential in `1/δ_n^2`.
- **Intrinsic.** `D_n` and `δ_n` are both unchanged by amplification `σ -> σ ⊗ 1_m`, while `n` is not.
  So the rate target is `vertex-rounding-with-log-depth-rate`, stated against `D_n`.

No root is affected. Derivation: `nonunit-root-mass-log-depth-proof`.
