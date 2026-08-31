import GroupApproximation.Analysis.CStarIdealApproximateUnit
import GroupApproximation.Analysis.ShulmanTraceClasses

/-!
# Descending tracial states through C-star quotients

An algebraically bundled tracial state which vanishes on a two-sided ideal
descends to the quotient.  The construction uses the linear quotient
universal property; positivity and traciality are checked on representatives.
-/

namespace GroupApproximation

noncomputable section

set_option linter.unusedSectionVars false

universe u

namespace TracialState

variable {A : Type u} [CStarAlgebra A]
  (I : Ideal A) [I.IsTwoSided]
  [CStarTensor.IsStarStable I]
  [IsClosed (I : Set A)]

/-- The complex-linear quotient of a functional which annihilates the ideal.
This is the noncommutative-ideal analogue of `Submodule.liftQ`; the quotient
type is formed from the ideal's additive subgroup, while complex linearity is
checked on representatives. -/
def descendLinearMap (tau : TracialState A) (hI : ∀ x ∈ I, tau x = 0) :
    (A ⧸ I) →ₗ[ℂ] ℂ :=
  { QuotientAddGroup.lift I.toAddSubgroup tau.toLinearMap.toAddMonoidHom hI with
    map_smul' := by
      rintro c ⟨x⟩
      exact tau.toLinearMap.map_smul c x }

@[simp]
theorem descendLinearMap_mk (tau : TracialState A)
    (hI : ∀ x ∈ I, tau x = 0) (a : A) :
    descendLinearMap I tau hI (Ideal.Quotient.mk I a) = tau a :=
  rfl

/-- A tracial state annihilating `I` descends to the C-star quotient `A/I`. -/
def descend (tau : TracialState A) (hI : ∀ x ∈ I, tau x = 0) :
    TracialState (A ⧸ I) where
  toLinearMap := descendLinearMap I tau hI
  map_one := by
    rw [← (Ideal.Quotient.mk I).map_one, descendLinearMap_mk]
    exact tau.map_one
  map_star_mul_self_nonneg := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [CStarTensor.quotient_star_mk, ← (Ideal.Quotient.mk I).map_mul,
      descendLinearMap_mk]
    exact tau.map_star_mul_self_nonneg a
  map_mul_comm := by
    intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← (Ideal.Quotient.mk I).map_mul, ← (Ideal.Quotient.mk I).map_mul,
      descendLinearMap_mk, descendLinearMap_mk]
    exact tau.map_mul_comm a b

@[simp]
theorem descend_mk (tau : TracialState A) (hI : ∀ x ∈ I, tau x = 0)
    (a : A) :
    tau.descend I hI (Ideal.Quotient.mk I a) = tau a :=
  descendLinearMap_mk I tau hI a

end TracialState

end

end GroupApproximation
