import GroupApproximation.Analysis.BlackadarKirchbergAbstractFiniteDimensionalLift
import GroupApproximation.Analysis.CStarExactness
import GroupApproximation.Meta.AxiomGuard

/-!
# Choi--Effros into matrix-sequence coronas: approximate CPC lifts

Lane `nm-tww-08`, step 1. Let `A` be nuclear and let `Φ : A → Q(X)` be a unital
`⋆`-homomorphism into the cofinite norm-matrix corona. For a finite set `S ⊆ A` and
`δ > 0`, there is a completely positive contraction `ψ : A → ∏ M_{X n}` whose corona
image is within `δ` of `Φ` on `S`.

Proof route.
* Nuclearity gives CPC maps `α : A → D` and `β : D → A`, with `D` finite-dimensional
  and `‖β α a - a‖ ≤ δ` on `S`.
* If `D` is trivial, `ψ = 0` works, because `‖Φ a‖ = ‖Φ (β α a - a)‖ ≤ δ`.
* Otherwise `Φ ∘ β : D → Q(X)` is CPC. The corpus lift
  `exists_completelyPositiveContractive_finiteDimensional_lift` gives a CPC lift `L`.
  Take `ψ = L ∘ α`. Then `q (ψ a) - Φ a = Φ (β α a - a)`, which has norm at most `δ`,
  because `⋆`-homomorphisms are contractive.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CoronaChoiEffros

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

variable {X : ℕ → Type v} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)] {A : Type u} [CStarAlgebra A]

/-- Bounded matrix sequences are C-star algebras (the same instance as in the corpus). -/
local instance boundedMatrixSequenceCStarAlgebraForCoronaChoiEffrosApprox :
    CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.boundedMatrixSequenceCStarAlgebraForCoronaChoiEffrosApprox

/-- The quotient `⋆`-homomorphism applies as `normMatrixCStarCoronaMk`. -/
theorem quotient_apply_eq_mk (x : BoundedMatrixSequence X) :
    normMatrixCStarCoronaQuotient X x = normMatrixCStarCoronaMk X x := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.quotient_apply_eq_mk

/-- The source of a unital `⋆`-homomorphism into the matrix corona is nontrivial,
because the corona is nontrivial. -/
theorem nontrivial_of_starAlgHom_normMatrixCorona
    (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona X) : Nontrivial A := by
  refine ⟨⟨1, 0, fun h ↦ ?_⟩⟩
  have h' : Φ 1 = Φ 0 := congrArg (⇑Φ) h
  rw [map_one, map_zero] at h'
  exact one_ne_zero h'

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.nontrivial_of_starAlgHom_normMatrixCorona

/-- The underlying linear map of `Φ`. -/
def starHomLinear (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona X) :
    A →ₗ[ℂ] NormMatrixCStarCorona X :=
  (Φ.toNonUnitalStarAlgHom : A →ₗ[ℂ] NormMatrixCStarCorona X)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.starHomLinear

theorem starHomLinear_apply (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona X) (a : A) :
    starHomLinear Φ a = Φ a := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.starHomLinear_apply

/-- A `⋆`-homomorphism is completely positive as a linear map. -/
theorem isCompletelyPositive_starHomLinear (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona X) :
    IsCompletelyPositive (starHomLinear Φ) :=
  isCompletelyPositive_of_starAlgHom Φ.toNonUnitalStarAlgHom

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.isCompletelyPositive_starHomLinear

/-- **Approximate CPC lifts.** Let `A` be nuclear. On a finite set, every unital
`⋆`-homomorphism into the matrix corona is approximated within `δ` by the corona
image of a completely positive contraction into the bounded matrix sequences. -/
theorem exists_cpc_approximateLift (hnuc : IsNuclearCStarAlgebra A)
    (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona X) (S : Finset A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : A →ₗ[ℂ] BoundedMatrixSequence X, IsCompletelyPositive ψ ∧
      (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧
        ∀ a ∈ S, ‖normMatrixCStarCoronaQuotient X (ψ a) - Φ a‖ ≤ δ := by
  obtain ⟨D, α, β, hαCP, hβCP, hαC, hβC, hrec⟩ := hnuc S δ hδ
  have hΦC : ∀ x : A, ‖Φ x‖ ≤ ‖x‖ := fun x ↦ NonUnitalStarAlgHom.norm_apply_le Φ x
  rcases subsingleton_or_nontrivial D with hD | hD
  · refine ⟨0, BlackadarKirchberg.isCompletelyPositive_zero, fun a ↦ ?_, fun a ha ↦ ?_⟩
    · rw [LinearMap.zero_apply, norm_zero]
      exact norm_nonneg a
    · have h : ‖β (α a) - a‖ ≤ δ := hrec a ha
      have hα0 : α a = 0 := @Subsingleton.elim _ hD (α a) 0
      rw [hα0, map_zero, zero_sub, norm_neg] at h
      rw [LinearMap.zero_apply, map_zero, zero_sub, norm_neg]
      exact (hΦC a).trans h
  · obtain ⟨L, hLCP, hLC, hq⟩ :=
      BlackadarKirchberg.exists_completelyPositiveContractive_finiteDimensional_lift
        (X := X) ((starHomLinear Φ).comp β) ((isCompletelyPositive_starHomLinear Φ).comp hβCP)
        (fun d ↦ (hΦC (β d)).trans (hβC d))
    refine ⟨L.comp α, hLCP.comp hαCP, fun a ↦ (hLC (α a)).trans (hαC a), fun a ha ↦ ?_⟩
    have h : ‖β (α a) - a‖ ≤ δ := hrec a ha
    have h1 : normMatrixCStarCoronaQuotient X (L (α a)) = Φ (β (α a)) := hq (α a)
    rw [LinearMap.comp_apply, h1, ← map_sub Φ]
    exact (hΦC _).trans h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.exists_cpc_approximateLift

end

end CoronaChoiEffros
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
