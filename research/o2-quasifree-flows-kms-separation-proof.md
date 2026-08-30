---
rg: 2
id: o2-quasifree-flows-kms-separation-proof
kind: route
title: Read the KMS temperature off the dual flow on the unique tracial ray
target: o2-quasifree-flows-cocycle-conjugacy-classified
requires: []
artifacts:
  - research/artifacts/stw99-lv-quasifree-flow-solution-2026-08-30.md
---

Four standard inputs, one elementary computation.

1. **KMS structure.**  For the quasifree flow with weights `(1, λ)`,
   `λ > 0`, the KMS_β states exist exactly for the unique `β = β(λ)`
   solving `e^{-β} + e^{-λβ} = 1` (quasifree KMS theory on Cuntz
   algebras; Kishimoto--Kumjian).  For irrational `λ > 0` the crossed
   product `O_2 ⋊_{α^{(λ)}} R` is simple, stably projectionless, with
   a UNIQUE tracial ray (Kishimoto--Kumjian, CJM).

2. **Duality between KMS weights and scaled traces.**  For a flow
   `α` on `A` with a KMS_β weight `φ`, the dual weight of `φ` on
   `A ⋊_α R` is a densely defined lower semicontinuous trace `τ`, and
   the dual flow scales it: `τ ∘ α̂_s = e^{-βs} τ`.  (This is the
   standard mechanism of the KMS-range constructions — the
   Elliott--Sato--Thomsen circle of results STW cite — specialized
   from Takesaki duality: rescale so that `α` is the modular flow of
   `φ`, where the dual trace on the core scales with exponent one,
   and undo the rescaling.)  Conversely every trace on the crossed
   product arises this way from a KMS weight of `α`.  So the
   trace-scaling exponent of `α̂` on the unique tracial ray equals
   `β(λ)`.

3. **Cocycle conjugacy preserves the marked pair.**  If
   `σ β_t σ^{-1} = Ad(u_t) α_t` with `(u_t)` a strictly continuous
   `α`-cocycle, then exterior equivalence (Packer--Raeburn) gives an
   isomorphism `A ⋊_{Ad(u)α} R ≅ A ⋊_α R` intertwining the dual
   flows at the SAME parameter, and `σ` transports the rest; so
   cocycle conjugate flows have isomorphic crossed products
   equivariantly for their dual flows.  Such an isomorphism maps the
   unique tracial ray to the unique tracial ray, preserving the
   scaling exponent.  Hence `β(λ) = β(μ)`.

4. **Injectivity.**  On `(0, ∞)`, `β(λ)` is strictly decreasing: at
   fixed `β`, `e^{-β} + e^{-λβ}` strictly decreases in `λ`, so the
   root of `= 1` moves strictly down as `λ` increases
   (`β(1) = ln 2`, `β → ∞` as `λ → 0⁺`, `β → 0` as `λ → ∞`).  So
   `β(λ) = β(μ) ⟹ λ = μ`.

Model check of step 2's sign and normalization on the classical
compact case: the gauge circle action on `O_n` has its unique KMS
point at `β = ln n`, and `O_n ⋊ T ≅ M_{n^∞} ⊗ K` carries the dual
`Z`-action scaling the trace by `1/n = e^{-β}` — the
Bratteli--Kishimoto trace-scaling picture — matching the exponent
claim exactly.
