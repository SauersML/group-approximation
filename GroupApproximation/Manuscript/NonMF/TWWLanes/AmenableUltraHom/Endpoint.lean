import GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.QuotientHom
import GroupApproximation.Meta.AxiomGuard

/-!
# Amenable traces give trace-preserving maps into matrix ultraproducts
(lane nm-tww-06, endpoints)

Manuscript sentence (Schafhauser's proof of TWW, Brown--Ozawa Ch. 6): *an
amenable trace `τ` gives a unital ⋆-homomorphism
`θ : A → ∏_ω M_{k(n)}(ℂ)` with `tr_ω ∘ θ = τ`.  It is injective when `τ` is
faithful.*

## Truth check

**The printed lane target is FALSE as stated.**  `τ = 0` is amenable (empty
models with the zero map), but `tr_ω 1 = 1`.  The endpoint below adds
`hone : τ 1 = 1`, which is necessary.  With it the statement is true and
proved here.  The faithful endpoint takes a `FaithfulTracialState`, which has
`τ 1 = 1` for free.  The binders are the corpus ones, `X : ℕ → FiniteModel`
with `∀ n, Nonempty (X n)`, as in `IsTraciallyMatrixEmbeddable`.

## Proof

* Skip the finitely many empty models (`exists_tail_card_pos`).
* Take `ω := Ultrafilter.of atTop`, which is free.  Its cofinite bound comes
  from `Nat.cofinite_eq_atTop`.
* `θ := tailHom`.  The trace identity is `ultratrace_mk` together with
  `UltrafilterLimit.ulim_eq`, applied to the shifted `tendsto_trace`.
* Injectivity is
  `StarAlgHom.injective_of_faithfulTracialState_of_trace_preserving` against
  `ultratraceFaithfulTracialState`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace AmenableUltraHom

open Filter

universe u

noncomputable section

variable {A : Type u} [CStarAlgebra A] {τ : A → ℂ}

/-- The ultratrace of `tailHom` recovers `τ`, along any ultrafilter finer than
`atTop`. -/
theorem ultratraceCLM_tailHom (M : Quasidiagonal.AmenableTraceModel τ) (N : ℕ)
    [∀ n, Nonempty (tailSpace M N n)] (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) (a : A) :
    TracialUltraproduct.ultratraceCLM (tailSpace M N) ω
      (tailHom M N (ω : Filter ℕ) hω a) = τ a := by
  have h0 : Tendsto (fun n ↦ normTrace (M.space n) (M.map n a)) atTop
      (nhds (τ a)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      ((M.tendsto_trace a).congr fun n ↦ norm_sub_rev _ _)
  have hshift : Tendsto (fun n ↦ normTrace (M.space (n + N)) (M.map (n + N) a))
      (ω : Filter ℕ) (nhds (τ a)) :=
    ((tendsto_add_atTop_iff_nat
      (f := fun n ↦ normTrace (M.space n) (M.map n a)) N).mpr h0).mono_left hω
  show TracialUltraproduct.ultratrace (tailSpace M N) ω
      (TracialUltraproduct.tracialMatrixQuotientMk (tailSpace M N) (ω : Filter ℕ)
        (tailSeq M N a)) = τ a
  rw [TracialUltraproduct.ultratrace_mk]
  show UltrafilterLimit.ulim ω
      (fun n ↦ normTrace (M.space (n + N)) (M.map (n + N) a)) = τ a
  exact UltrafilterLimit.ulim_eq hshift

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.ultratraceCLM_tailHom

/-- **Manuscript sentence, corrected.**  A normalized amenable trace factors as
the ultratrace of a unital ⋆-homomorphism into a tracial matrix ultraproduct
over a free ultrafilter.  The added `hone : τ 1 = 1` is necessary: the lane's
printed target fails at `τ = 0`. -/
theorem manuscriptSentence_existsTracialQuotientHomOfIsAmenableTrace
    (h : Quasidiagonal.IsAmenableTrace τ) (hone : τ 1 = 1) :
    ∃ X : ℕ → FiniteModel, ∃ hXne : ∀ n, Nonempty (X n),
      letI : ∀ n, Nonempty (X n) := hXne
      ∃ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ cofinite ∧
        ∃ θ : A →⋆ₐ[ℂ]
            TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ),
          ∀ a, TracialUltraproduct.ultratraceCLM X ω (θ a) = τ a := by
  obtain ⟨M⟩ : Nonempty (Quasidiagonal.AmenableTraceModel τ) := h
  obtain ⟨K, hK⟩ := exists_tail_card_pos M hone
  have hne : ∀ n, Nonempty (tailSpace M K n) := fun n ↦
    Fintype.card_pos_iff.mp (hK (n + K) (Nat.le_add_left K n))
  let ω : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le (atTop : Filter ℕ)
  have hcof : (ω : Filter ℕ) ≤ cofinite := by
    simpa only [Nat.cofinite_eq_atTop] using hω
  exact ⟨tailSpace M K, hne, ω, hcof, tailHom M K (ω : Filter ℕ) hω,
    ultratraceCLM_tailHom M K ω hω⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.manuscriptSentence_existsTracialQuotientHomOfIsAmenableTrace

/-- The lane's name for the corrected endpoint. -/
theorem exists_tracialQuotientHom_of_isAmenableTrace
    (h : Quasidiagonal.IsAmenableTrace τ) (hone : τ 1 = 1) :
    ∃ X : ℕ → FiniteModel, ∃ hXne : ∀ n, Nonempty (X n),
      letI : ∀ n, Nonempty (X n) := hXne
      ∃ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ cofinite ∧
        ∃ θ : A →⋆ₐ[ℂ]
            TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ),
          ∀ a, TracialUltraproduct.ultratraceCLM X ω (θ a) = τ a :=
  manuscriptSentence_existsTracialQuotientHomOfIsAmenableTrace h hone

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.exists_tracialQuotientHom_of_isAmenableTrace

/-- **Manuscript sentence, faithful case.**  For a faithful tracial state the
trace-preserving ⋆-homomorphism is injective. -/
theorem manuscriptSentence_existsInjectiveTracialQuotientHomOfIsAmenableTrace
    (tau : FaithfulTracialState A)
    (h : Quasidiagonal.IsAmenableTrace (fun a : A ↦ tau a)) :
    ∃ X : ℕ → FiniteModel, ∃ hXne : ∀ n, Nonempty (X n),
      letI : ∀ n, Nonempty (X n) := hXne
      ∃ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ cofinite ∧
        ∃ θ : A →⋆ₐ[ℂ]
            TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ),
          (∀ a, TracialUltraproduct.ultratraceCLM X ω (θ a) = tau a) ∧
            Function.Injective θ := by
  obtain ⟨X, hXne, ω, hω, θ, hθ⟩ :=
    manuscriptSentence_existsTracialQuotientHomOfIsAmenableTrace h tau.apply_one
  letI : ∀ n, Nonempty (X n) := hXne
  refine ⟨X, hXne, ω, hω, θ, fun a ↦ hθ a, ?_⟩
  exact GroupApproximation.StarAlgHom.injective_of_faithfulTracialState_of_trace_preserving
    tau (TracialUltraproduct.ultratraceFaithfulTracialState X ω) θ
    (fun a ↦ hθ a)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.manuscriptSentence_existsInjectiveTracialQuotientHomOfIsAmenableTrace

end

end AmenableUltraHom
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
