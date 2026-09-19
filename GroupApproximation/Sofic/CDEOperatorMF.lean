import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
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
  ∃ d : ℕ → ℕ, ∃ hd : ∀ n, 0 < d n,
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) := fun n ↦
      Fintype.card_pos_iff.mp (by simpa using hd n)
    StrictMono d ∧
      ∃ rho : G →* unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))), Function.Injective rho

/-- The literal CDE C-star-corona definition and the unitary-sequence
definition are propositionally equivalent. -/
theorem isCDEOperatorMF_iff_isOperatorMF
    (G : Type u) [Group G] [Countable G] :
    IsCDEOperatorMF G ↔ IsOperatorMF G := by
  constructor
  · rintro ⟨d, hd, _hmono, rho, hrho⟩
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) := fun n ↦
      Fintype.card_pos_iff.mp (by simpa [X] using hd n)
    exact ⟨X, (by simpa [X] using hd),
      (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rho,
      (normMatrixCoronaUnitaryEquiv X).symm.injective.comp hrho⟩
  · intro hMF
    rcases isOperatorMFIncreasing_iff.mpr hMF with ⟨X, hX, hmono, rho, hrho⟩
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    let d : ℕ → ℕ := fun n ↦ Fintype.card (X n)
    let rhoActual : G →*
        unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
      (normMatrixCoronaUnitaryEquiv X).toMonoidHom.comp rho
    let rhoNatural : G →* unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))) :=
      (actualCoronaNaturalizeEquiv X).toMonoidHom.comp rhoActual
    exact ⟨d, hX, hmono, rhoNatural,
      (actualCoronaNaturalizeEquiv X).injective.comp
        ((normMatrixCoronaUnitaryEquiv X).injective.comp hrho)⟩

end GroupApproximation
