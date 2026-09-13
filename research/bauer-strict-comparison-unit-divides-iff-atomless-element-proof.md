---
rg: 2
id: bauer-strict-comparison-unit-divides-iff-atomless-element-proof
kind: route
title: Turn an element with small atoms into a uniformly Lebesgue element by a central CDF transform, cut constant-trace projections, and compare
target: bauer-strict-comparison-unit-divides-iff-atomless-element
requires:
  - strict-comparison-compares-ultrapower-projections
artifacts:
  - research/artifacts/ex2-tw-atomless-element-division-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md
---

Section 1 of `research/artifacts/ex2-tw-atomless-element-division-2026-09-13.md`, over (F1),
(F4) and (F5) of part 1 of the C-space artifact.

1. **(i) ⟹ (ii).** For order zero `φ: M_N → A` with defect `< ε/2` and `N ≥ 2/ε`, put
   `h = Σ_j (j/N)φ(e_jj)`.
   - Its atom at `0` is `1 − d_λ(φ(1)) < ε/2`.
   - (F4) for `g(φ)` makes the pieces equidistributed on `(0,1]`, each of mass at most `1/N`.
     An atom at `x > 0` collects distinct points `Nx/j` of one such measure, so it is at most `1/N`.
2. **(ii) ⟹ small concentration.** If no `η` works, compactness of `K`, weak*-continuity of
   `λ ↦ μ_{h,λ}` and the Portmanteau inequality for closed sets produce an atom of mass `≥ ε`.
3. **(small concentration) ⟹ (iii).** Put `F(λ, s) = ∫ clamp((s − y)/η) dμ_{h,λ}(y)`.
   - `F` is jointly continuous, and `μ((−∞, s−η]) ≤ F(s) ≤ μ((−∞, s))`. So `F(λ,·)_*μ_{h,λ}` is within
     `ε` of Lebesgue in Kolmogorov distance.
   - Approximate `F` by `Σ a_m(λ)p_m(s)`, put `u = clamp(Σ θ(a_m)p_m(h))`, and use that `θ(a)` is the
     scalar `a(λ)` in the fibre at `λ`.
4. **(iii) ⟹ (i).**
   - **Ramps.** Take approximants `a_n ∈ A` with `‖a_n − u_n‖_{2,u} ≤ ε_n` and ramps `g_n` of width
     `η_n`, with `ε_n/η_n → 0`. Lipschitz functional calculus in the trace 2-norm bounds
     `|λ(g_n(a_n)) − t|` and `λ(g_n(a_n) − g_n(a_n)²)` by `O(η_n + ε_n/η_n)`, and integration extends the
     bounds to all traces.
   - **Projections.** `p_t = [(g_n(a_n))]` is a projection of `A^ω` with `σ(p_t) = t` for every limit
     trace.
   - **Matrix units.** For `t = 1/k`, comparison of ultrapower projections places `k` equivalent
     orthogonal copies. The remainder has zero limit traces, hence vanishes, so a unital
     `M_k ⊂ A^ω` exists.
   - **Lifting.** Order zero lifting gives `φ_n: M_k → A` with `sup_τ τ(1 − φ_n(1)) → 0` along `ω`.
