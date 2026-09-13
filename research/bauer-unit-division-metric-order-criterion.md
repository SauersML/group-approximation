---
rg: 2
id: bauer-unit-division-metric-order-criterion
kind: claim
title: Under strict comparison on a Bauer simplex, the unit divides unless local divisions of weight 1/N + δ shrink to a mesh needing cover order of order N
distinct_from:
  bauer-unit-division-iff-summable-local-division: that characterizes division by summable covers with weights (1/N + δ)^{1/2}; this proves the same characterization with linear weights 1/N + δ and turns it into a metric criterion on the Lebesgue numbers of local divisions.
  bauer-c-space-strict-comparison-divides-unit: that needs property C of the boundary and no quantitative input; this needs no topological hypothesis on the boundary but a growth bound relating division radii to cover orders.
  ash-strict-comparison-rank-gap-algebra-exists: that seeks an ASH witness from a gluing obstruction linear in block size and cell dimension; this shows a strict-comparison witness on a Bauer simplex needs local divisions confined at a comparably linear rate.
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-part4-2026-09-13.md
---

**Setting.** `A` is unital, simple, separable, exact and non-elementary, with strict
comparison and a nonempty Bauer simplex with extreme boundary `K`.

**Theorem (linear weights).** The unit is tracially `N`-divisible for every `N` iff, for
every `κ > 0`, some finite family of division sets `(O_i, φ_i, N_i, δ_i)` covers `K` with
`Σ_{i : λ ∈ O_i} (1/N_i + δ_i) ≤ κ` at every `λ`. Here `φ_i: M_{N_i} → A` is order zero
with `λ(1 − φ_i(1)) < δ_i` on `O_i`.

**Metric criterion.** Fix a compatible metric on `K`.
- `ℓ_A(ω)`: the Lebesgue number of the open cover of `K` by sets carrying division sets
  with `1/N + δ ≤ ω`.
- `ord_K(r)`: the least order of a finite open cover of `K` of mesh `< r`.
- **Criterion.** If `liminf_{ω → 0} ω · ord_K(ℓ_A(ω)) = 0`, the unit divides.

**Examples.**
- `dim K < ∞`: the criterion always holds.
- Hilbert cube with `ρ(x,y) = Σ_i 2^{−i}|x_i − y_i|`: here `ord_Q(r) ≤ log_2(4/r) + 2`.
  So a strict-comparison algebra over this boundary with an indivisible unit has
  `ℓ_A(ω) ≤ 2^{−c/ω}` for some `c > 0` and all small `ω`. Its local divisions of matrix
  size `N` must be confined to sets exponentially small in `N`, heuristically thin in
  about `cN` coordinates.

**Proof** (route `bauer-unit-division-metric-order-criterion-proof`; Sections 8–9 of
the part 4 artifact).
- **Lemma 8.1.** `μ_{b,λ}((σ,1]) ≥ λ(b) − 2λ(b − b²)` for `σ ≤ 1/2`. So a fixed cutoff
  `s` charges each active member only its defect.
- **Linear weights.** The staircase-and-move construction of
  `bauer-c-space-strict-comparison-divides-unit` then needs only `Σ_{i∋λ} d_i ≤ ε_0²/64`,
  with `d_i = 1/(4N_i) + δ_i`.
- **Metric criterion.** A cover of mesh below the Lebesgue number has members inside
  division sets.

**Model test.**
- For `C(K)`, every order zero `M_N → C(K)` with `N ≥ 2` vanishes, so no division set
  has weight below `1`. For `ω < 1` there is no cover and no Lebesgue number, so the
  criterion cannot hold. That matches the failure of division; `C(K)` is not simple,
  which is where Lemma 1 fails.
- A `Z`-stable algebra has `ℓ_A(ω) ≥ diam K` for all `ω`, so the criterion holds.

Review PASS (ex-verify2-analysis, `research/artifacts/ex-review2-analysis-2026-09-13-part2.md`, §§2.2–2.7).
