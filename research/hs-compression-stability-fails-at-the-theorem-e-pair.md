---
rg: 2
id: hs-compression-stability-fails-at-the-theorem-e-pair
kind: claim
title: Some approximate representations of the Kun--Thom actor carry almost commuting unitaries that a compressor conjugates away from commuting
distinct_from:
  hs-uniform-compression-stability-at-the-theorem-e-pair: that is the uniform inequality; this is its negation, carried separately because it has its own consequence, a hyperlinear nonsofic group.
  hyperlinear-group-carries-nontrivial-rigid-defect: that asks for any hyperlinear group with a nontrivial rigid defect; this is a sequence of finite matrix counterexamples at one explicit presentation, which produces such a group.
refuted_by:
  - hs-uniform-compression-stability-at-the-theorem-e-pair
artifacts:
  - research/artifacts/unified-compression-rigidity-2026-09-12.md
---

**OPEN.** With `Gamma < G = <Gamma, A, B>` and `F` as in
[[hs-uniform-compression-stability-at-the-theorem-e-pair]], there are `eta > 0`, `eps_k -> 0`,
`R_k -> infinity`, dimensions `n_k`, maps `u^(k)` from the `R_k`-ball of `G` to `U(n_k)`
with `u_1 = 1` and `||u_g u_h - u_(gh)||_2 <= eps_k`, and unitaries `z_k` with
`||[z_k, u^(k)_s]||_2 <= eps_k` for `s in F`, such that

```text
max_(s in F, t in {A,B}) ||[u^(k)_t z_k (u^(k)_t)^*, u^(k)_s]||_2 >= eta     for all k.
```

Consequence: `hyperlinear-group-carries-nontrivial-rigid-defect`, through
`hyperlinear-rigid-defect-from-hs-compression-instability`. That gives a hyperlinear nonsofic
group.

## Attempts

- **Genuine representations.** Excluded: the inequality holds on them
  (`ccr-holds-for-all-genuine-fd-coordinate-models`).
- **Atomic commutants.** Excluded: a compressor acts as an automorphism on the discrete type I
  summand of the relative commutant
  (`trace-preserving-endomorphism-fixes-discrete-type-i-summand`). The limit `z` must carry mass
  on the diffuse summand.
- **Haagerup targets.** Excluded: no relative wall exists when the image of `Gamma` generates a
  Haagerup algebra (`haagerup-targets-carry-no-relative-wall`).
- **Few aspect scales.** Excluded under vertex rounding with `delta_n log n -> 0`
  (`ccr-under-vertex-rounding-from-few-aspect-scales`).
- **Canonical Connes-embeddable models.** The model-shape survey is in the Attempts of
  `kt-canonical-hs-normalization-fails`. Its surviving shape is a one-sided Bernoulli shift on a
  diffuse summand, compatible with both compressors at once.
