---
rg: 2
id: kt-wreath-models-never-round-on-the-vertex-proof
kind: route
title: Run the unit-type chain at one wreath model and hit the rigid defect
target: kt-wreath-models-never-round-on-the-vertex
requires:
  - nonunit-projection-bounded-by-root-spectral-mass
  - shallow-nonunit-root-mass-vanishes-under-vertex-rounding
  - vertex-rounding-deep-nonunit-root-mass-vanishes
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - kun-thom-wreath-carries-rigid-defect
artifacts:
  - research/artifacts/q34-bc-witness-hyperlinear-2026-09-12.md
---

Let `σ : W -> U(M)`, with `M = ∏_U M_n`, be trace-preserving. Suppose `π_n` are (H1) roundings of `σ|G`
on `Γ`.

0. **One model.**
   - `σ|G` is a trace-preserving actor model.
   - Each premise below is a statement about one trace-preserving actor model and one (H1) rounding of it.
     None quantifies over other models.
   - The premises conjugate by the nonnegative compressors `A ∈ SL_d(Z)`, by
     `t = diag(x_1, x_1, x_1^(-2), 1, …, 1) ∈ EL_r(L)`, and by the powers `A^k` of `A = (min(i,j))` and the
     reversal conjugate `B`.
   - All of these lie in `G`, so the unitaries are `σ(A)`, `σ(t)`, `σ(A^k)` and `σ(B)`, from the same `σ`.
1. **Finite images.** By item 1 of `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`, each
   `π_n` factors through `St_r(B_n)`, with `B_n = A_u × A_nu` finite.
2. **Projection bound.** Since `χ|A_nu ≠ 1` iff `depth_nu(χ) >= 1`,
   `nonunit-projection-bounded-by-root-spectral-mass` gives

   ```text
   τ(1 − P_n)  <=  r(r−1) · [ μ_n(depth_nu = 1) + μ_n(depth_nu > 1) ].
   ```

3. **Both terms vanish.**
   - Item 5 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` gives
     `μ_n(depth_nu = 1) <= q·η_n + η_n^t`, which tends to 0 along `U`.
   - `vertex-rounding-deep-nonunit-root-mass-vanishes` gives `μ_n(depth_nu > 1) -> 0` along `U`.
   - So `τ(1 − P_n) -> 0` along `U`.
4. **Normalization.** By item 4 of `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`,
   `σ(G)` normalizes `N = σ(Γ)' ∩ M`.
5. **Rigid defect.** `kun-thom-wreath-carries-rigid-defect` gives a strict compressor `t_0 ∈ G` and an
   element `γ ∈ Γ \ t_0 Γ t_0^(-1)`.
   - The lamp `e_Γ` is fixed by `Γ`, so `σ(e_Γ) ∈ N`.
   - By step 4, `σ(e_(t_0 Γ)) = σ(t_0) σ(e_Γ) σ(t_0)^*` lies in `N`, so it commutes with `σ(γ)`. That is,
     `σ(e_(γ t_0 Γ)) = σ(e_(t_0 Γ))`.
   - But `γ t_0 Γ ≠ t_0 Γ`, so `e_(γ t_0 Γ) e_(t_0 Γ) ≠ 1`. Trace preservation gives

     ```text
     ||σ(e_(γ t_0 Γ)) − σ(e_(t_0 Γ))||_2^2  =  2 − 2 Re τ(σ(e_(γ t_0 Γ) e_(t_0 Γ)))  =  2.
     ```

This is a contradiction, so `σ|G` has no (H1) rounding on `Γ`.

**Relation to the open routes.** Steps 1–3 are steps 1–3 of `theorem-e-vertex-unit-type-via-deep-root-mass`.
Steps 4–5 are `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding`. Both routes are run here at a single
model. Their open premise, (H1) for every model, is replaced by the hypothesis being refuted. That is why
this route needs only established premises.

**Diagonal form.**
- Let `A_ε` be the set of `n` for which some padding of `σ_n` to `n' <= (1+ε)n` dimensions is within `ε` of a
  genuine representation of `Γ` on `F_Γ`.
- Suppose `A_ε ∈ U` for every `ε > 0`. Put `k(n) = max{k <= n : n ∈ A_(1/k)}` and choose `π_n` at `ε = 1/k(n)`.
- For each `k_0`, the set `{n : k(n) >= k_0}` contains `A_(1/k_0) ∩ [k_0, ∞)`, which lies in `U`. So this is an
  (H1) rounding, which the argument above excludes.
- Hence some `A_ε` is not in `U`.
