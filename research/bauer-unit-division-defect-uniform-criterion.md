---
rg: 2
id: bauer-unit-division-defect-uniform-criterion
kind: claim
title: Under strict comparison on a Bauer simplex, only matrix sizes of local divisions need summing; defects need a uniform bound
distinct_from:
  bauer-unit-division-metric-order-criterion: that sums weights 1/N_i + δ_i of local divisions; this sums only 1/N_i and asks for a uniform bound on δ_i, so confinement caused by the defect alone never blocks division.
  bauer-unit-division-iff-summable-local-division: that sums square-root weights (1/N_i + δ_i)^{1/2}; this is the sharper defect-uniform form.
artifacts:
  - research/artifacts/ex2-tw-hilbert-cube-defect-uniform-division-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part4-2026-09-13.md
---

**Setting.** `A` is unital, simple, separable, exact and non-elementary, with strict
comparison and a nonempty Bauer simplex with extreme boundary `K`. A division set
`(O, φ, N, δ)` is an open `O ⊆ K` with c.p.c. order zero `φ: M_N → A` and
`λ(1 − φ(1)) < δ` on `O`.

**Theorem (defect-uniform criterion).** The unit of `A` is tracially `N`-divisible for
every `N` iff for every `κ > 0` some finite family of division sets `(O_i, φ_i, N_i, δ_i)`
covers `K` with
- `Σ_{i : λ ∈ O_i} 1/N_i ≤ κ` for every `λ ∈ K`, and
- `δ_i ≤ κ` for every `i`.

**Metric form.** Fix a compatible metric. Let `ℓ_A(N, δ)` be the Lebesgue number of the
cover by open sets carrying division sets with matrix size `≥ N` and defect `≤ δ`. The unit
divides iff for every `κ > 0` there are `δ ≤ κ` and `N` with `ord_K(ℓ_A(N, δ)) ≤ κN`.

**Hilbert cube.** Take `K = Q` with `ρ(x,y) = Σ_i 2^{−i}|x_i − y_i|`. If the unit does not
divide, some `κ_0 > 0` has `ℓ_A(N, κ_0) ≤ 16 · 2^{−κ_0 N}` for every `N`. Divisions of fixed
defect must be confined exponentially in the matrix size alone.

**Proof** (route `bauer-unit-division-defect-uniform-criterion-proof`).
- **Lemma H.1.** A central staircase has defect at most `1/(4N) + δ/N + t h(λ)δ`. Order zero
  functional calculus with `f(s) = s − s²` makes all pieces carry equal defect `δ/N`. Only
  about `Nth(λ) + 1` pieces are switched on.
- **Summation.** The profile-weighted parts sum to at most `t · max_i δ_i`, since
  `Σ h_i = 1`. The per-member parts are at most `2 Σ_{i∋λ} 1/N_i`.
- **Rest of the proof.** The spectral bounds (F2) and Lemma 8.1, the moves and the division
  step are those of Proposition 8.2.

**What it adds.** Corollary F (`bauer-unit-division-metric-order-criterion`) charges
`1/N + δ`. It cannot exclude confinement such as `ℓ_A(N, δ) ≈ 2^{−c/δ}` for every `N`. The
metric form above divides the unit there: take `δ = κ` and `N ≥ c/κ²`.

**Model tests.** `C(K)` fails the covering condition, since every point carries weight `1`.
A `Z`-stable algebra satisfies it with the single set `K`.

Unreviewed. It is a bookkeeping refinement of Proposition 8.2 of lane
`ex-tw-rotation-gluing`, which is itself unreviewed.
