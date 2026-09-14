---
rg: 2
id: laurent-sl4-block-sl2-norm-four-off-full-spectrum-proof
kind: route
title: Factor through a finite congruence quotient and apply the chain-ring invariant vectors on one nonzero isotypic summand
target: laurent-sl4-block-sl2-norm-four-off-full-unipotent-spectrum
requires:
  - laurent-unipotent-spectra-are-finite-or-full
  - sl4-over-finite-chain-rings-has-sl2-invariant-vectors
  - ring-model-permutation-vectors-block-strong-convergence
artifacts:
  - research/artifacts/sk-mf-laurent-2026-09-14-part1.md
---

Artifact part 1, Section 4.

1. **A finite quotient.** The spectrum is not `Â^3`, so by `laurent-unipotent-spectra-are-finite-or-full` `σ` factors
   through `C*(G)`, `G = SL_4(A/J)`, `J ≠ 0`. This algebra is `⊕_ρ M_{d_ρ}`, with central projections `p_ρ`.
2. **One summand survives.** `σ` is unital, so `σ(p_ρ) ≠ 0` for some irreducible `ρ`, and a nonzero *-homomorphism on
   the simple summand `C*(G)p_ρ` is isometric.
3. **Norm four there.** `A/J ≅ F_q[t]/(f)` is a finite principal ideal ring. By
   `sl4-over-finite-chain-rings-has-sl2-invariant-vectors`, `ρ` has a nonzero `SL_2(A/J)`-fixed vector. So
   `‖ρ(z)‖ = 4`, with `S, T` free in `SL_2(F_q[t])` by item 3 of `ring-model-permutation-vectors-block-strong-convergence`
   (Nagao).
4. **Conclude.** `‖σ(z)‖ ≥ ‖σ(z)σ(p_ρ)‖ = ‖z p_ρ‖_{C*(G)} = ‖ρ(z)‖ = 4`, and `‖σ(z)‖ ≤ 4` always. On `H`,
   `σ(p_ρ)H ≠ 0` is `ρ`-isotypic, so it contains `ρ`'s fixed vectors.
