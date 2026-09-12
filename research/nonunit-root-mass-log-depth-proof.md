---
rg: 2
id: nonunit-root-mass-log-depth-proof
kind: route
title: Count the d-adic depth blocks up to the maximal occurring depth instead of up to r(r-1)n'
target: nonunit-root-mass-log-depth-scale-bound
requires:
  - root-character-nonunit-depth-at-most-log-q-dimension
  - nonunit-component-root-mass-is-log-scale-folner
  - shallow-nonunit-root-mass-vanishes-under-vertex-rounding
  - nonunit-projection-bounded-by-root-spectral-mass
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

Full derivation in §3 of the artifact.

- **Item 1.**
  - Item 3 of `nonunit-component-root-mass-is-log-scale-folner` gives
    `μ_n(d^j < depth_nu <= d^(j+1)) <= η_n` for every `j >= 0`.
  - By `root-character-nonunit-depth-at-most-log-q-dimension`, `μ_n` has no mass above `D_n <= log_q n'`.
  - If `D_n <= 1` there is nothing to sum. Otherwise the blocks meeting `(1, D_n]` are those with
    `d^j < D_n`, and there are `⌈log_d D_n⌉ <= 1 + log_d D_n` of them.
- **Item 2.**
  - `nonunit-projection-bounded-by-root-spectral-mass` gives `τ(1 - P_n) <= r(r-1)·μ_n(χ_nu ≠ 1)`.
  - `{χ_nu ≠ 1} = {depth_nu = 1} ⊔ {depth_nu > 1}`.
  - Item 5 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` bounds the first set by
    `q·η_n + η_n^t`, and item 1 bounds the second.
- **Item 3.**
  - `η_n^t -> 0` along `U` by item 2 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`.
  - `η_n · log_d max(1, D_n) -> 0` exactly when `δ_n^2 log(1 + D_n) -> 0`.
  - `D_n <= log_q n'` and `n'/n -> 1` give the `log log n` form.
