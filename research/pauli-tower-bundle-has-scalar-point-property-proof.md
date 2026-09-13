---
rg: 2
id: pauli-tower-bundle-has-scalar-point-property-proof
kind: route
title: Variance is Lipschitz in the uniform 2-norm and vanishes somewhere on every finite stage
target: pauli-tower-bundle-has-scalar-point-property
requires:
  - pauli-tower-sections-are-somewhere-scalar
  - closed-extreme-trace-sets-give-r-fibre-w-star-bundles
artifacts:
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md
---

Section 4 of the artifact (Theorem B). Unreviewed.

1. **Traces.**
   - On `A_m = C(Z_m, B_{0,m})`, a trace restricts to a measure `μ` on `Z_m`.
   - Local matrix units and traciality give `τ(f e_{ij}) = δ_{ij} τ(f e_{11})` for `f` supported in a
     trivializing set, so `τ(a) = ∫ tr(a(z)) dμ(z)`.
   - `T(A) = lim T(A_m) = Prob(X̂)`, with extreme points the point traces `τ_λ = tr ∘ π_λ`, and
     `π_λ(A) = M_{2^∞}`.
   - The second prerequisite with `K = X̂` makes `M` a strictly separable continuous W*-bundle with
     fibres `R` (nuclear, no finite-dimensional representation).
2. **Variance.**
   - `Var_λ(y) = E(y²)(λ) − E(y)(λ)² = ‖π_λ(y) − τ_λ(y)1‖²_{2,λ}`.
   - The fibre trace is faithful on `π_λ(M) = R`, so `Var_λ(y) = 0` iff `π_λ(y) ∈ C·1`.
3. **Lipschitz bound.** For self-adjoint `y, y'` of norm `≤ C`,
   `|τ(y²) − τ(y'²)| ≤ 2C‖y − y'‖_{2,u}` and `|τ(y)² − τ(y')²| ≤ 2C‖y − y'‖_{2,u}`. So
   `V(y) = min_λ Var_λ(y)` is `4C`-Lipschitz.
4. **Finite stages.** For self-adjoint `a ∈ A_m`, the first prerequisite (`n = 0`) gives `z ∈ Z_m`
   with `a(z) ∈ R1`. Every `λ` over `z` has `π_λ(a) = a(z) ⊗ 1` scalar, so `V(a) = 0`.
5. **Limit.**
   - Elements of `M` are norm-bounded `‖·‖_{2,u}`-Cauchy sequences from `A` modulo null sequences.
   - For self-adjoint `x`, take real parts (`‖w*‖_{2,u} = ‖w‖_{2,u}`), then norm-close self-adjoint
     elements of `∪_m A_m` with the same bound.
   - Step 3 gives `V(x) = 0`, attained by compactness.
6. **Nontriviality.** A W*-bundle isomorphism intertwines the conditional expectations, so it
   preserves `Var`. A constant trace-`1/2` projection of `C_σ(X̂, R)` has `Var ≡ 1/4`.
