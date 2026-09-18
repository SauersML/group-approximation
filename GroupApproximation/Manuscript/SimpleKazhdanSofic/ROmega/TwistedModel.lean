import GroupApproximation.Manuscript.SimpleKazhdanSofic.ROmega.GroupGraph
import GroupApproximation.Analysis.TwistedGroupVonNeumannFactor
import GroupApproximation.Analysis.PauliStageOperators
import GroupApproximation.Analysis.MatrixUltraproductToHyperfiniteUltrapower
import GroupApproximation.Meta.AxiomGuard

/-!
# Twisted group von Neumann algebras into `R^ω` from a projective model

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation":

> (tex 350–355) … $L(G)\mathbin{\bar\otimes}\mathcal R$ … embeds in $\mathcal R^\omega$.

The McDuff factor `L(G) ⊗̄ 𝓡` is spatially the twisted group von Neumann algebra `L_σ(P × G)` of the
product of the Pauli group with `G`, for the cocycle `σ = pauliCocycle ⊕ 0`
(`TwistedProduct.curryConj_image_twistedTensor`).  This module does the embedding step for a general
sign cocycle.

Route.  Let `u : Γ → 𝓡^ω` be a *projective model* of `(Γ, σ)`: `u 1 = 1`,
`u x u y = s(σ(x,y)) u(xy)`, `(u x)⋆ = s(σ(x,x⁻¹)) u(x⁻¹)` and `τ_ω(u x) = 0` for `x ≠ 1`.
The pairs `(λ_σ(x), u x)` span a trace-compatible graph: `λ_σ` obeys the same relations
(`twistedLeftOperator_mul`, `star_twistedLeftOperator_eq`, `twistedLeftOperator_one`), the vector
state of `δ₁` on `λ_σ(x)` is `[x = 1]` (`coefficient_twistedLeftOperator`), the first coordinates
are `‖·δ₁‖`-dense by the point-mass expansion, and `δ₁` separates `L_σ(Γ)`.
`exists_injective_of_generators` then gives an injective trace-preserving `⋆`-homomorphism
`L_σ(Γ) → 𝓡^ω` (`exists_twisted_embedding_of_model`).
-/

namespace GroupApproximation.SimpleKazhdanSofic.ROmega

open Filter TracialUltrapower ReducedGroupCStarTrace TwistedGroupVonNeumann
open scoped InnerProductSpace Topology ENNReal

noncomputable section

variable {Γ : Type} [Group Γ] (σ : Γ → Γ → ZMod 2)

local instance romegaDecEqTwisted : DecidableEq Γ := Classical.decEq Γ

/-- `δ₁` as a tracial vector of `L_σ(Γ)`. -/
def twistedTracialVector (hσ : IsSignCocycle σ) : TracialVector (twistedVonNeumannAlgebra σ) where
  vec := deltaOne Γ
  norm_vec := GroupVonNeumann.norm_deltaOne Γ
  tracial T hT S hS := by
    rw [GroupVonNeumann.inner_deltaOne_left Γ, GroupVonNeumann.inner_deltaOne_left Γ]
    exact coefficient_mul_comm σ hσ hT hS

/-- Finite combinations of twisted left operators are `‖·δ₁‖`-dense among all operators. -/
theorem exists_sum_twistedLeftOperator_close (hσ : IsSignCocycle σ)
    (T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ) {ε : ℝ} (hε : 0 < ε) : ∃ t : Finset Γ, ∃ c : Γ → ℂ,
      ‖(∑ x ∈ t, c x • twistedLeftOperator σ x - T) (deltaOne Γ)‖ < ε := by
  have htend : Tendsto
      (fun t : Finset Γ ↦ ∑ x ∈ t, (lp.single 2 x (T (deltaOne Γ) x) : GroupHilbert Γ))
      atTop (𝓝 (T (deltaOne Γ))) :=
    lp.hasSum_single ENNReal.ofNat_ne_top (T (deltaOne Γ))
  obtain ⟨t, ht⟩ := (htend.eventually_mem (Metric.ball_mem_nhds _ hε)).exists
  refine ⟨t, fun x ↦ T (deltaOne Γ) x, ?_⟩
  have hop : ∀ x ∈ t, (T (deltaOne Γ) x • twistedLeftOperator σ x) (deltaOne Γ)
      = (lp.single 2 x (T (deltaOne Γ) x) : GroupHilbert Γ) := fun x _ ↦ by
    rw [_root_.smul_apply, twistedLeftOperator_deltaOne σ hσ, ← lp.single_smul,
      smul_eq_mul, mul_one]
  rw [_root_.sub_apply, _root_.sum_apply, Finset.sum_congr rfl hop, ← dist_eq_norm]
  exact ht

section Model

variable (ω : Ultrafilter ℕ) (u : Γ → Hyperfinite.HyperfiniteUltrapower ω)

/-- The generator pairs `(λ_σ(x), u x)`. -/
def twistedPair (x : Γ) :
    (GroupHilbert Γ →L[ℂ] GroupHilbert Γ) × Hyperfinite.HyperfiniteUltrapower ω :=
  (twistedLeftOperator σ x, u x)

theorem twistedPair_mem_span (x : Γ) :
    twistedPair σ ω u x ∈ Submodule.span ℂ (Set.range (twistedPair σ ω u)) :=
  Submodule.subset_span ⟨x, rfl⟩

theorem twistedPair_one_mem (hσ : IsSignCocycle σ) (hone : u 1 = 1) :
    (1 : (GroupHilbert Γ →L[ℂ] GroupHilbert Γ) × Hyperfinite.HyperfiniteUltrapower ω)
      ∈ Submodule.span ℂ (Set.range (twistedPair σ ω u)) := by
  have h : twistedPair σ ω u 1 = 1 := Prod.ext (twistedLeftOperator_one σ hσ) hone
  rw [← h]
  exact twistedPair_mem_span σ ω u 1

theorem twistedPair_mul_mem (hσ : IsSignCocycle σ)
    (hmul : ∀ x y, u x * u y = zsign (σ x y) • u (x * y)) (x y : Γ) :
    twistedPair σ ω u x * twistedPair σ ω u y
      ∈ Submodule.span ℂ (Set.range (twistedPair σ ω u)) := by
  have e : twistedPair σ ω u x * twistedPair σ ω u y
      = zsign (σ x y) • twistedPair σ ω u (x * y) :=
    Prod.ext (twistedLeftOperator_mul σ hσ x y) (hmul x y)
  rw [e]
  exact Submodule.smul_mem _ _ (twistedPair_mem_span σ ω u (x * y))

theorem twistedPair_star_mem (hσ : IsSignCocycle σ)
    (hstar : ∀ x, star (u x) = zsign (σ x x⁻¹) • u x⁻¹) (x : Γ) :
    star (twistedPair σ ω u x) ∈ Submodule.span ℂ (Set.range (twistedPair σ ω u)) := by
  have e : star (twistedPair σ ω u x) = zsign (σ x x⁻¹) • twistedPair σ ω u x⁻¹ :=
    Prod.ext (star_twistedLeftOperator_eq σ hσ x) (hstar x)
  rw [e]
  exact Submodule.smul_mem _ _ (twistedPair_mem_span σ ω u x⁻¹)

theorem twistedPair_trace (hσ : IsSignCocycle σ) (hone : u 1 = 1)
    (htr : ∀ x, x ≠ 1 → Hyperfinite.hyperfiniteUltratrace ω (u x) = 0) (x : Γ) :
    ultratrace Hyperfinite.hyperfiniteTracialVector ω (twistedPair σ ω u x).2
      = ⟪(twistedTracialVector σ hσ).vec,
          (twistedPair σ ω u x).1 (twistedTracialVector σ hσ).vec⟫_ℂ := by
  show Hyperfinite.hyperfiniteUltratrace ω (u x)
    = ⟪deltaOne Γ, twistedLeftOperator σ x (deltaOne Γ)⟫_ℂ
  rw [GroupVonNeumann.inner_deltaOne_left Γ, coefficient_twistedLeftOperator σ hσ x]
  by_cases hx : x = 1
  · subst hx
    rw [if_pos rfl, hone]
    exact ultratrace_one Hyperfinite.hyperfiniteTracialVector ω
  · rw [if_neg hx]
    exact htr x hx

end Model

/-- **Projective models embed `L_σ(Γ)` in `R^ω`.**  A projective model `u : Γ → 𝓡^ω` of the sign
cocycle `σ` whose non-identity values have ultratrace `0` extends to an injective `⋆`-homomorphism
`L_σ(Γ) → 𝓡^ω` carrying the trace `T ↦ ⟪δ₁, T δ₁⟫` to the ultratrace. -/
theorem exists_twisted_embedding_of_model (hσ : IsSignCocycle σ) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (u : Γ → Hyperfinite.HyperfiniteUltrapower ω) (hone : u 1 = 1)
    (hmul : ∀ x y, u x * u y = zsign (σ x y) • u (x * y))
    (hstar : ∀ x, star (u x) = zsign (σ x x⁻¹) • u x⁻¹)
    (htr : ∀ x, x ≠ 1 → Hyperfinite.hyperfiniteUltratrace ω (u x) = 0) :
    ∃ Φ : ↥(twistedVonNeumannAlgebra σ).toStarSubalgebra →⋆ₐ[ℂ]
        Hyperfinite.HyperfiniteUltrapower ω, Function.Injective Φ ∧
      ∀ T : ↥(twistedVonNeumannAlgebra σ).toStarSubalgebra,
        Hyperfinite.hyperfiniteUltratrace ω (Φ T)
          = ⟪deltaOne Γ, (T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ) (deltaOne Γ)⟫_ℂ := by
  obtain ⟨Φ, hinj, htrΦ, -⟩ := exists_injective_of_generators (twistedTracialVector σ hσ)
    (twistedPair σ ω u) (twistedPair_one_mem σ ω u hσ hone) (twistedPair_mul_mem σ ω u hσ hmul)
    (twistedPair_star_mem σ ω u hσ hstar) hω (fun x ↦ twistedLeftOperator_mem σ x)
    (twistedPair_trace σ ω u hσ hone htr)
    (fun T _ ε hε ↦ exists_sum_twistedLeftOperator_close σ hσ T hε)
    (fun T hT h ↦ eq_zero_of_mem_of_apply_deltaOne_eq_zero σ hσ hT h)
  exact ⟨Φ, hinj, htrΦ⟩

end

end GroupApproximation.SimpleKazhdanSofic.ROmega

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.exists_twisted_embedding_of_model
