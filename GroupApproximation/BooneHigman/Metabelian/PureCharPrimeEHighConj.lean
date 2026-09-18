import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# The conjugation representation of a split extension (bh-met-56)

Let `κ : B →* GL_d(K)` and `ρ : Q →* GL_d(K)` satisfy `κ (φ q b) = ρ q * κ b * (ρ q)⁻¹`.  Then
`x ↦ κ x.left * ρ x.right` is a homomorphism `B ⋊[φ] Q →* GL_d(K)` (`SemidirectProduct.lift`).
It is injective when `κ` is injective and `ρ q ∈ κ(B)` forces `q = 1`.  This is the
multiplicative counterpart of the affine trick in `PureCharPrimeEAffine`.  It is needed when `B`
has exponent `p ^ e` with `e ≥ 2`, because then `B` cannot embed additively into `K^d`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open Matrix

section Conj

variable {B Q : Type*} [Group B] [Group Q] {φ : Q →* MulAut B} {K : Type*} [Field K] {d : ℕ}

theorem eHighConj_comp (κ : B →* GeneralLinearGroup (Fin d) K)
    (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (hκ : ∀ (q : Q) (b : B), κ (φ q b) = ρ q * κ b * (ρ q)⁻¹) (q : Q) :
    κ.comp (φ q).toMonoidHom = (MulAut.conj (ρ q)).toMonoidHom.comp κ :=
  MonoidHom.ext fun b => hκ q b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighConj_comp

/-- The representation `x ↦ κ x.left * ρ x.right`. -/
def eHighConjGL (κ : B →* GeneralLinearGroup (Fin d) K) (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (hκ : ∀ (q : Q) (b : B), κ (φ q b) = ρ q * κ b * (ρ q)⁻¹) :
    (B ⋊[φ] Q) →* GeneralLinearGroup (Fin d) K :=
  SemidirectProduct.lift κ ρ (eHighConj_comp κ ρ hκ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighConjGL

theorem eHighConjGL_apply (κ : B →* GeneralLinearGroup (Fin d) K)
    (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (hκ : ∀ (q : Q) (b : B), κ (φ q b) = ρ q * κ b * (ρ q)⁻¹) (x : B ⋊[φ] Q) :
    eHighConjGL κ ρ hκ x = κ x.left * ρ x.right :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighConjGL_apply

theorem eHighConjGL_injective (κ : B →* GeneralLinearGroup (Fin d) K)
    (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (hκ : ∀ (q : Q) (b : B), κ (φ q b) = ρ q * κ b * (ρ q)⁻¹)
    (hκi : Function.Injective κ) (hρ : ∀ (q : Q) (b : B), ρ q = κ b → q = 1) :
    Function.Injective (eHighConjGL κ ρ hκ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [eHighConjGL_apply] at hx
  have hr : x.right = 1 := by
    refine hρ x.right x.left⁻¹ ?_
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right hx
  have hl : x.left = 1 := by
    rw [hr, map_one, mul_one] at hx
    exact hκi (hx.trans (map_one κ).symm)
  exact SemidirectProduct.ext hl hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighConjGL_injective

end Conj

end GroupApproximation.BooneHigman.Metabelian.Coprimary
