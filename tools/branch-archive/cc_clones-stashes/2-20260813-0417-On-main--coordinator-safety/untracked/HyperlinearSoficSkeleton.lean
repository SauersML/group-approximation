import NonsoficGroupsExist.Sofic.Hyperlinear
import NonsoficGroupsExist.Criterion.FiniteQuotientBlindness

/-!
# Kernel-checkable logical skeleton for the hyperlinear-versus-sofic audit

Place this file at the root of the supplied `NonsoficGroupsExist` repository and run

    lake env lean HyperlinearSoficSkeleton.lean

with the repository's pinned Lean 4.32.2 toolchain.

The file deliberately formalizes only the final logical chain that is actually
established.  It does not postulate a resolution of the open question.
-/

namespace HyperlinearSoficAudit

open NonsoficGroupsExist

variable {G H Q : Type*} [Group G] [Group H] [Group Q]

/-- A single finite window with no model at a positive tolerance disproves
hyperlinearity.  This is the rigorous "uniform-gap" endpoint. -/
theorem not_hyperlinear_of_window_gap
    (F : Finset G) (ε : ℝ) (hε : 0 < ε)
    (hgap : ¬ Nonempty (HyperlinearModel G F ε)) :
    ¬ IsHyperlinear G := by
  intro hG
  exact hgap (hG F ε hε)

/-- Persistence on every finite window is exactly hyperlinearity, by the
repository's local definition. -/
theorem hyperlinear_of_window_persistence
    (hpersist : ∀ (F : Finset G) (ε : ℝ), 0 < ε →
      Nonempty (HyperlinearModel G F ε)) :
    IsHyperlinear G :=
  hpersist

/-- For a known nonsofic group, excluded middle leaves exactly the two genuine
endpoints: it is a hyperlinear nonsofic counterexample, or it is nonhyperlinear.
This is the corrected exhaustive dichotomy. -/
theorem nonsofic_candidate_dichotomy (hNS : ¬ IsSofic G) :
    (IsHyperlinear G ∧ ¬ IsSofic G) ∨ ¬ IsHyperlinear G := by
  by_cases hH : IsHyperlinear G
  · exact Or.inl ⟨hH, hNS⟩
  · exact Or.inr hH

/-- The direction already proved in the supplied development. -/
theorem sofic_implies_hyperlinear (hS : IsSofic G) : IsHyperlinear G :=
  isHyperlinear_of_isSofic hS

/-- Its contrapositive: a uniform hyperlinear gap also proves nonsoficity. -/
theorem nonhyperlinear_implies_nonsofic (hH : ¬ IsHyperlinear G) : ¬ IsSofic G :=
  not_isSofic_of_not_isHyperlinear hH

/-- A finite quotient identifies the image of a compressed subgroup with the
image of the original subgroup.  This is a convenient machine-checked form of
the finite-quotient blindness used in the separability-barrier proof. -/
theorem finite_image_of_compression
    [Finite Q] (φ : H →* Q) (Γ : Subgroup H) {t : H}
    (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    (Γ.map φ).map (MulAut.conj (φ t)).toMonoidHom = Γ.map φ :=
  compressedImage_eq φ Γ ht

/-- In particular, every element of the image of `Γ` already belongs to the
image of its compressed conjugate. -/
theorem finite_image_contains_compressed_preimage
    [Finite Q] (φ : H →* Q) (Γ : Subgroup H) {t : H}
    (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ)
    (γ : H) (hγ : γ ∈ Γ) :
    φ γ ∈ (Γ.map φ).map (MulAut.conj (φ t)).toMonoidHom := by
  rw [compressedImage_eq φ Γ ht]
  exact ⟨γ, hγ, rfl⟩

end HyperlinearSoficAudit
