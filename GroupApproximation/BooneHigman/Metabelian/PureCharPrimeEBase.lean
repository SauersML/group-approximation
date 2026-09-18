import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Base restriction for subgroups containing the complement (bh-met-26)

Let `H ≤ B ⋊[φ] Q` contain `inr Q`, and let `B₀ = eBase H = H.comap inl` be the base of `H`.
`φ` restricts to `eBaseAut H hQ : Q →* MulAut B₀` (because `inl (φ q b) = inr q * inl b * inr q⁻¹`),
and `x ↦ (x.left, x.right)` is a bijective homomorphism `eBaseHom : H →* B₀ ⋊ Q` (because
`inl x.left = x * (inr x.right)⁻¹ ∈ H`).  Consequently `B₀ ⋊ Q` is f.g. when `H` is, `B₀`
inherits commutativity and exponents, and a faithful linear representation of `B₀ ⋊ Q` gives one
of `H` (`exists_gl_of_eBase`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open Matrix

section Base

variable {B Q : Type} [Group B] [Group Q] {φ : Q →* MulAut B} (H : Subgroup (B ⋊[φ] Q))

/-- The base `H ∩ B` of a subgroup `H ≤ B ⋊ Q`. -/
abbrev eBase : Subgroup B := H.comap (SemidirectProduct.inl : B →* B ⋊[φ] Q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBase

theorem eBase_inr_mem (hQ : (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H) (q : Q) :
    (SemidirectProduct.inr q : B ⋊[φ] Q) ∈ H :=
  hQ (MonoidHom.mem_range.mpr ⟨q, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBase_inr_mem

theorem eBase_aut_mem (hQ : (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H) (q : Q)
    (b : eBase H) : φ q (b : B) ∈ eBase H := by
  refine Subgroup.mem_comap.mpr ?_
  rw [SemidirectProduct.inl_aut]
  exact H.mul_mem (H.mul_mem (eBase_inr_mem H hQ q) (Subgroup.mem_comap.mp b.2))
    (eBase_inr_mem H hQ q⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBase_aut_mem

/-- `φ q` restricted to the base `eBase H`. -/
def eBaseAutOf (hQ : (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H) (q : Q) :
    MulAut (eBase H) where
  toFun b := ⟨φ q (b : B), eBase_aut_mem H hQ q b⟩
  invFun b := ⟨φ q⁻¹ (b : B), eBase_aut_mem H hQ q⁻¹ b⟩
  left_inv b := Subtype.ext (by
    show φ q⁻¹ (φ q (b : B)) = (b : B)
    rw [← MulAut.mul_apply (φ q⁻¹) (φ q) (b : B), ← map_mul, inv_mul_cancel, map_one,
      MulAut.one_apply])
  right_inv b := Subtype.ext (by
    show φ q (φ q⁻¹ (b : B)) = (b : B)
    rw [← MulAut.mul_apply (φ q) (φ q⁻¹) (b : B), ← map_mul, mul_inv_cancel, map_one,
      MulAut.one_apply])
  map_mul' a b := Subtype.ext (map_mul (φ q) (a : B) (b : B))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBaseAutOf

/-- The restricted action `Q →* MulAut (eBase H)`. -/
def eBaseAut (hQ : (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H) :
    Q →* MulAut (eBase H) where
  toFun := eBaseAutOf H hQ
  map_one' := MulEquiv.ext fun b => Subtype.ext (by
    show φ 1 (b : B) = (b : B)
    rw [map_one, MulAut.one_apply])
  map_mul' q r := MulEquiv.ext fun b => Subtype.ext (by
    show φ (q * r) (b : B) = φ q (φ r (b : B))
    rw [map_mul, MulAut.mul_apply])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBaseAut

theorem eBase_left_mem (hQ : (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H) (x : H) :
    (x : B ⋊[φ] Q).left ∈ eBase H := by
  refine Subgroup.mem_comap.mpr ?_
  rw [eq_mul_inv_of_mul_eq (SemidirectProduct.inl_left_mul_inr_right (x : B ⋊[φ] Q))]
  exact H.mul_mem x.2 (H.inv_mem (eBase_inr_mem H hQ _))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBase_left_mem

/-- The isomorphism `H → eBase H ⋊ Q`, `x ↦ (x.left, x.right)`. -/
def eBaseHom (hQ : (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H) :
    H →* (eBase H ⋊[eBaseAut H hQ] Q) where
  toFun x := ⟨⟨(x : B ⋊[φ] Q).left, eBase_left_mem H hQ x⟩, (x : B ⋊[φ] Q).right⟩
  map_one' := SemidirectProduct.ext (Subtype.ext rfl) rfl
  map_mul' _ _ := SemidirectProduct.ext (Subtype.ext rfl) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBaseHom

theorem eBaseHom_injective (hQ : (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H) :
    Function.Injective (eBaseHom H hQ) := by
  intro x y hxy
  have hl : (x : B ⋊[φ] Q).left = (y : B ⋊[φ] Q).left :=
    congrArg (fun z : eBase H ⋊[eBaseAut H hQ] Q => (z.left : B)) hxy
  have hr : (x : B ⋊[φ] Q).right = (y : B ⋊[φ] Q).right :=
    congrArg (fun z : eBase H ⋊[eBaseAut H hQ] Q => z.right) hxy
  exact Subtype.ext (SemidirectProduct.ext hl hr)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBaseHom_injective

theorem eBaseHom_surjective (hQ : (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H) :
    Function.Surjective (eBaseHom H hQ) := by
  intro z
  have hz : (⟨(z.left : B), z.right⟩ : B ⋊[φ] Q) =
      SemidirectProduct.inl (z.left : B) * SemidirectProduct.inr z.right :=
    (SemidirectProduct.inl_left_mul_inr_right (⟨(z.left : B), z.right⟩ : B ⋊[φ] Q)).symm
  have hmem : (⟨(z.left : B), z.right⟩ : B ⋊[φ] Q) ∈ H := by
    rw [hz]
    exact H.mul_mem (Subgroup.mem_comap.mp z.left.2) (eBase_inr_mem H hQ z.right)
  exact ⟨⟨⟨(z.left : B), z.right⟩, hmem⟩, SemidirectProduct.ext (Subtype.ext rfl) rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBaseHom_surjective

theorem eBase_fg (hQ : (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H) (hH : H.FG) :
    Group.FG (eBase H ⋊[eBaseAut H hQ] Q) := by
  haveI : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  exact Group.fg_of_surjective (eBaseHom_surjective H hQ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBase_fg

theorem eBase_comm (hB : ∀ a b : B, a * b = b * a) (a b : eBase H) : a * b = b * a :=
  Subtype.ext (hB a b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBase_comm

theorem eBase_pow (n : ℕ) (hexp : ∀ b : B, b ^ n = 1) (b : eBase H) : b ^ n = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, hexp, Subgroup.coe_one])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eBase_pow

theorem exists_gl_of_eBase {p : ℕ} (hQ : (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H)
    (hlin : ∃ (K : Type) (_ : Field K) (d : ℕ)
      (f : (eBase H ⋊[eBaseAut H hQ] Q) →* GeneralLinearGroup (Fin d) K),
      ringChar K = p ∧ Function.Injective f) :
    ∃ (K : Type) (_ : Field K) (d : ℕ) (f : H →* GeneralLinearGroup (Fin d) K),
      ringChar K = p ∧ Function.Injective f := by
  obtain ⟨K, hK, d, f, hchar, hf⟩ := hlin
  exact ⟨K, hK, d, f.comp (eBaseHom H hQ), hchar, hf.comp (eBaseHom_injective H hQ)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_gl_of_eBase

end Base

end GroupApproximation.BooneHigman.Metabelian.Coprimary
