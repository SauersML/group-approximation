---
rg: 2
id: amenable-bauer-factorial-tracially-complete-without-gamma-proof
kind: route
title: Lifts of a constant-trace projection in the reduced power contradict the scalar point property
target: amenable-bauer-factorial-tracially-complete-without-gamma
requires:
  - pauli-tower-bundle-has-scalar-point-property
  - nuclear-tracial-completions-are-amenable
  - uniform-gamma-iff-completion-has-gamma
---

Unreviewed.

1. **Tracially complete** (Definition 3.4).
   - `X` is faithful, since `E` is faithful.
   - The unit ball is `‖·‖_{2,X}`-complete: `‖·‖_{2,X}` is the uniform 2-norm, whose supremum over `X` is
     attained on the extreme points.
2. **Factorial** (Proposition 3.14). The extreme points of `X` are the point traces `τ_λ`, and
   `π_λ(M)'' = R` is a factor.
3. **Type II_1** (Definition 3.8).
   - For `τ ∈ X`, `π_τ(M)'' = π_τ(A)''` by density.
   - A type `I_n` summand with central projection `z` would give a unital *-homomorphism
     `A → π_τ(A)'' z ≅ L^∞(Ω) ⊗ M_n`. A character of `L^∞(Ω)` would then give a unital
     representation `A → M_n`.
   - Every irreducible representation of the `C(X̂)`-algebra `A` factors through a fibre `M_{2^∞}`, so
     `A` has no finite-dimensional representation.
4. **Amenable.** `A` is nuclear; apply the second prerequisite.
5. **No constant-trace projection.**
   - Let `p ∈ M^ω` be a projection with `τ(p) = 1/2` on `X^ω`. Represent `p` by contractions, and
     replace them by `f(Re x_n)` with `f(t) = min(max(t, 0), 1)`. These still represent `p`, since the
     quotient map commutes with functional calculus. So `x_n` are positive contractions with
     `lim_ω ‖x_n − x_n²‖_{2,X} = 0`.
   - **Uniformity.** `lim_ω sup_{τ∈X} |τ(x_n) − 1/2| = 0`. Otherwise some `δ > 0`, some `I ∈ ω` and some
     `τ_n ∈ X` have `|τ_n(x_n) − 1/2| > δ` for `n ∈ I`, and the limit trace `lim_ω τ_n` does not give
     `p` trace `1/2`.
   - **Contradiction.** Fix `η = 1/10`. For `ω`-many `n`, `sup_τ τ(x_n − x_n²) < η` and
     `|τ(x_n) − 1/2| < η` on `X`. The first prerequisite gives `λ` with `π_λ(x_n) = μ1`, where
     `μ = τ_λ(x_n)`. Then `τ_λ(x_n − x_n²) = μ − μ² ≥ 1/4 − η² > η`.
6. **Property Γ fails.** Definition 5.19 with `S = {1}`, `k = 2` would give such a `p = p_1`. Then the
   third prerequisite shows that `A` lacks uniform property Γ.
