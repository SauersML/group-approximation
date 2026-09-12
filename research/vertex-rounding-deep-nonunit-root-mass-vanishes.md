---
rg: 2
id: vertex-rounding-deep-nonunit-root-mass-vanishes
kind: claim
title: Under vertex rounding, non-unit root mass above depth one vanishes
distinct_from:
  theorem-e-vertex-rounds-to-unit-type-representations: that bundles (H1) with vanishing of all non-unit congruence mass; this assumes (H1) and asks only for the deep part, the one part not yet proved.
  nonunit-component-root-mass-is-log-scale-folner: that bounds the deep non-unit mass by the transport defect times the number of d-adic depth scales; this asks that it vanish with no rate.
  shallow-nonunit-root-mass-vanishes-under-vertex-rounding: that proves the non-unit mass at depth exactly one vanishes; this asks the same for the complementary mass at depth above one.
  vertex-rounding-non-unit-mass-at-origin: that confines non-unit mass to the origin and bounds its depth profile scale by scale; this asks that the deep origin mass vanish.
artifacts:
  - research/artifacts/nh-unit-type-valuations-2026-09-12.md
---

**OPEN.** Setting of `nonunit-component-root-mass-is-log-scale-folner`:
- `σ : G -> U(prod_U M_n)` is trace-preserving, with (H1) roundings `π_n` of the vertex `Γ = EL_r(F_q[x_1..x_d])`,
  `r, d >= 3`;
- `μ_n` is the normalized spectral measure of `f -> π_n(e_12(f))`;
- `depth_nu` is the `z`-depth of the non-unit component, where `z = x_1 ⋯ x_d`.

**Claim.** `μ_n(depth_nu > 1) -> 0` along `U`.

**Payoff.**
- `nonunit-projection-bounded-by-root-spectral-mass` gives `τ(1 − P_n) <= r(r−1)·[μ_n(depth_nu = 1) + μ_n(depth_nu > 1)]`.
- Item 5 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` kills the first term.
- So the claim gives `theorem-e-vertex-rounds-to-unit-type-representations` (route
  `theorem-e-vertex-unit-type-via-deep-root-mass`).

**What is left.**
- By `vertex-rounding-non-unit-mass-at-origin`, the deep mass is at the origin.
- Its profile must occupy at least order `1/η_n` d-adic depth scales, which needs `η_n log D_n` bounded below, where `D_n` is
  the largest origin depth.
- Every fixed finite quotient and every bounded depth carries vanishing mass.

## Attempts

- **Compressor and torus drift is amenable.** The exact transports available on root spectra move depth only by drift.
  - A nonnegative compressor divides `depth_nu` by `d`.
  - The Laurent torus `t = diag(x_1, x_1, x_1^(-2))`, exactified on `EL_2(R_+) ⋉ R_+^2` by relative (T), lowers the
    `x_1`-nilpotency of the origin component by `3`. This gives additive shells `μ_n(k <= ν <= k+2) <= η_n^t` (artifact §2).
  - The maps `k -> k/d` and `k -> k − 3` generate a solvable affine drift.
  - The log-uniform profile on `[1, D]` has defect `log d/log D` against the first test and `log 4/log D` against the second.
    So every finite set of such tests passes once `log D >> 1/ε`.
  - Neither `η_n` nor `η_n^t` has a rate along `U`, and iterating costs `j·η_n`.
- **Non-amenable directions only by containment.**
  - A rate-free bound would need transports acting on depth profiles through a non-amenable group, such as `SL_d(Z)` on
    exponent directions.
  - Only nonnegative `A` map `Γ` into `Γ`. A general `A` exactifies only on a cone subring `F_q[x^C]` with `AC ⊆ N^d`,
    through relative (T) of `EL_2(F_q[x^C]) ⋉ F_q[x^C]^2`.
  - Restriction to that subring relates annihilator monomial sets only by containment: `Mon_C(χ|) ⊇ Mon(χ) ∩ C`. The
    `SL_d(Z)`-action on shapes does not descend to the spectra.
  - The same containment defeats the projective-staircase compactness argument: two positive compressors with different
    Perron vectors have no common invariant shape measure, but constituents inherit only `J_κ ⊇ φ_A^(-1) J_ρ`.
- **Depth-one compressor rigidity (explains the need for the torus).** Take `R_+/J_ρ = A_u × F_q`.
  - The substitution `ψ∘φ_A` maps onto both factors, by the unit trick and `ev_0∘φ_A = ev_0`.
  - By Goursat its image is the whole product, since `x_1 -> (unit, 0)` excludes a graph.
  - So every depth-one type transports to a single depth-one type. This agrees with the constant-term invariance recorded in
    `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`.
