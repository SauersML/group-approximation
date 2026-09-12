---
rg: 2
id: vertex-rounding-with-log-depth-rate
kind: claim
title: Every trace-preserving representation of the Theorem E actor rounds on the vertex with transport defect beating the log of the maximal non-unit depth
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is (H1) with no rate; this asks for (H1) together with the quantitative condition delta_n^2 log(1 + D_n) -> 0 against the intrinsic maximal non-unit depth.
  theorem-e-vertex-rounds-to-unit-type-representations: that is unit-type rounding itself; this is a quantitative form of (H1) that implies it through nonunit-root-mass-log-depth-scale-bound.
  nonunit-root-mass-log-depth-scale-bound: that is the established conditional bound; this is the open rate hypothesis it consumes.
  vertex-rounding-deep-nonunit-root-mass-vanishes: that asks the deep non-unit mass of the supplied roundings to vanish with no rate; this asks for roundings whose defect beats the log of their maximal non-unit depth, which kills that mass for those roundings.
  laurent-vertex-rounds-for-every-model: that rounds the Laurent vertex, which needs no rate; this rounds the polynomial vertex with a rate.
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

**OPEN.** Let `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, with `r, d >= 3`, be the
explicit Theorem E pair, and fix a compressor `A ∈ SL_d(Z)` with every entry `>= 1`. For every
trace-preserving `σ : G -> U(prod_U M_n)`, (H1) should hold with rounding representations `π_n` and
unitary representatives of `σ_n(A)` such that

```text
δ_n^2 · log(1 + D(π_n))  ->  0     along U.
```

Here `δ_n` is the intertwining defect of `compressor-transport-exactifies-under-vertex-rounding`, and
`D(π_n)` the maximal non-unit root depth of `root-character-nonunit-depth-at-most-log-q-dimension`.
By `nonunit-root-mass-log-depth-scale-bound` this gives unit-type rounding (route
`unit-type-rounding-via-log-depth-rate`).

## Attempts

- **Shape of a counterexample.**
  - Assume (H1) with `τ(1 - P_n) >= c > 0` along `U`.
  - The shallow mass vanishes, so order-one mass sits above depth one.
  - It needs at least `c'/η_n` d-adic blocks, so `D(π_n) > d^(c'/η_n - 1)`.
  - Then some constituent has dimension at least `q^(D(π_n))`.
  - No model of this shape is known.
- **Intrinsic scale.** Amplifying `σ -> σ ⊗ 1_(m_n)` changes neither `δ_n` nor `D(π_n)`, but it multiplies the
  dimension arbitrarily. So a rate stated in `n`, such as `δ_n^2 log log n -> 0`, is sufficient but is not the
  right target.
- **Transport alone.** It cannot supply the rate. Compressor and torus transports drift depth through an
  amenable group, and log-uniform profiles pass every finite set of them (Attempts of
  `vertex-rounding-deep-nonunit-root-mass-vanishes`).
- **Restrict to the consumed wreath models.** It pays only through lamp covariance.
  - The endgame consumes `σ|G` for hyperlinearity witnesses `σ` of the Kun–Thom wreath.
  - Their regular trace and a trace-zero lamp symmetry in `σ(Γ)'` can be added to any model by tensoring with
    finite-quotient models of `G` and `1_2`. That keeps the same rounding defect, `δ_n`, non-unit mass and `D`
    (artifact §5).
  - The remaining structure is the covariant lamp family, which is what the endgame itself contradicts.
- **Strict stability.** Impossible (Becker–Lubotzky arXiv:1809.00632, abstract). This claim is flexible, and
  flexible HS stability of higher-rank Kazhdan groups is open.
