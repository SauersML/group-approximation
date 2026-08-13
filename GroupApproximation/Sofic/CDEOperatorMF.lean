import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Sofic.OperatorMFIncreasingDimensions

/-!
# The literal Carrión--Dadarlat--Eckhardt MF predicate

Carrión--Dadarlat--Eckhardt define a countable group to be MF when it embeds
in the unitary group of a C-star algebra

`(∏ n, M_(d n) ℂ) / (⊕ n, M_(d n) ℂ)`.

This file states that predicate using the genuine norm-matrix C-star quotient
constructed in `Analysis.NormMatrixCorona` and proves it equivalent to the
unitary-sequence presentation used by the existing analytic development.  The
equivalence is the polar-correction equivalence, not a change of definition by
fiat.
-/

namespace GroupApproximation

universe u

/-- The literal CDE definition: a countable group embeds into the unitary
group of a genuine norm-matrix C-star corona whose positive matrix dimensions
are strictly increasing. -/
def IsCDEOperatorMF (G : Type u) [Group G] [Countable G] : Prop :=
  ∃ X : ℕ → FiniteModel, ∃ hne : ∀ n, Nonempty (X n),
    letI := hne
    (∀ n, 0 < Fintype.card (X n)) ∧
      StrictMono (fun n ↦ Fintype.card (X n)) ∧
        ∃ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
          Function.Injective rho

/-- The literal CDE C-star-corona definition and the unitary-sequence
definition are propositionally equivalent. -/
theorem isCDEOperatorMF_iff_isOperatorMF
    (G : Type u) [Group G] [Countable G] :
    IsCDEOperatorMF G ↔ IsOperatorMF G := by
  constructor
  · rintro ⟨X, hne, h⟩
    letI : ∀ n, Nonempty (X n) := hne
    rcases h with ⟨hX, _hmono, rho, hrho⟩
    exact ⟨X, hX, (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rho,
      (normMatrixCoronaUnitaryEquiv X).symm.injective.comp hrho⟩
  · intro hMF
    rcases isOperatorMFIncreasing_iff.mpr hMF with ⟨X, hX, hmono, rho, hrho⟩
    let hne : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    refine ⟨X, hne, ?_⟩
    letI : ∀ n, Nonempty (X n) := hne
    exact ⟨hX, hmono, (normMatrixCoronaUnitaryEquiv X).toMonoidHom.comp rho,
      (normMatrixCoronaUnitaryEquiv X).injective.comp hrho⟩

end GroupApproximation
