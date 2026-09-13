---
rg: 2
id: zero-dimensional-atomless-diagonal-divides-unit-proof
kind: route
title: An injective function on the zero-dimensional diagonal is a self-adjoint element with atomless spectral distributions at every extreme trace
target: zero-dimensional-atomless-diagonal-divides-unit
requires:
  - bauer-strict-comparison-unit-divides-iff-atomless-element
artifacts:
  - research/artifacts/ex2-tw-atomless-element-division-2026-09-13.md
---

Section 2 of `research/artifacts/ex2-tw-atomless-element-division-2026-09-13.md`.

1. **The element.** A compact metrizable zero-dimensional `Y` embeds topologically in the
   Cantor set, hence in `[0,1]`. Let `h ∈ C(Y) ⊆ A` be such an embedding. It is a self-adjoint
   contraction.
2. **Its distributions.** For `λ ∈ K` and polynomials `p`, `λ(p(h)) = ∫_Y p ∘ h d(λ|_{C(Y)})`.
   So `μ_{h,λ} = h_*(λ|_{C(Y)})`.
3. **No atoms.** `h` is injective and `λ|_{C(Y)}` is atomless, so `μ_{h,λ}({x}) = λ|_{C(Y)}(h^{−1}(x))`
   is the measure of at most one point, hence `0`.
4. **Conclusion.** Condition (ii) of `bauer-strict-comparison-unit-divides-iff-atomless-element`
   holds for every `ε > 0`, so the unit divides.
