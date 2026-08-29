import GroupApproximation.Sofic.NormTraceGap
import GroupApproximation.Sofic.SoficUltraproduct

/-!
# Weak-MF approximations and their operator-norm ultraproduct

This file supplies the first analytic layer of the Kazhdan-corner argument.
The local operator-norm models of `IsNormApproximable` are assembled, for a
countable group, into one sequential approximation.  Its pointwise unitary
maps then induce an injective homomorphism into the quotient of the product of
matrix unitary groups by operator-norm-null sequences.

Unlike the Hilbert--Schmidt ultraproduct, no amplification theorem is needed:
the fixed separation constant in the definition of weak-MF directly prevents
distinct elements from becoming equal in the quotient.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-! ## The local weak-MF predicate -/

/-! ## Sequential weak-MF models -/

/-! ## Operator-norm length -/

/-- Operator-norm displacement of a unitary from the identity. -/
noncomputable def opLength (Y : FiniteModel)
    (u : Matrix.unitaryGroup Y ℂ) : ℝ :=
  ‖(u : Matrix Y Y ℂ) - 1‖

@[simp] theorem opLength_one (Y : FiniteModel) :
    opLength Y 1 = 0 := by
  simp [opLength]

/-- The length of a product is at most the sum of the lengths. -/
theorem opLength_mul_le (Y : FiniteModel)
    (u v : Matrix.unitaryGroup Y ℂ) :
    opLength Y (u * v) ≤ opLength Y u + opLength Y v := by
  have hsplit :
      ((u * v : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) - 1 =
        (u : Matrix Y Y ℂ) * ((v : Matrix Y Y ℂ) - 1) +
          ((u : Matrix Y Y ℂ) - 1) := by
    change (u : Matrix Y Y ℂ) * (v : Matrix Y Y ℂ) - 1 = _
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [opLength, hsplit, opLength, opLength]
  calc
    ‖(u : Matrix Y Y ℂ) * ((v : Matrix Y Y ℂ) - 1) +
        ((u : Matrix Y Y ℂ) - 1)‖ ≤
        ‖(u : Matrix Y Y ℂ) * ((v : Matrix Y Y ℂ) - 1)‖ +
          ‖(u : Matrix Y Y ℂ) - 1‖ := norm_add_le _ _
    _ = ‖(v : Matrix Y Y ℂ) - 1‖ + ‖(u : Matrix Y Y ℂ) - 1‖ := by
      rw [CStarRing.norm_mem_unitary_mul _ u.2]
    _ = ‖(u : Matrix Y Y ℂ) - 1‖ + ‖(v : Matrix Y Y ℂ) - 1‖ :=
      add_comm _ _

/-- Inversion does not change operator-norm length. -/
theorem opLength_inv (Y : FiniteModel) (u : Matrix.unitaryGroup Y ℂ) :
    opLength Y u⁻¹ = opLength Y u := by
  have hcoe : ((u⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) =
      (u : Matrix Y Y ℂ)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    rfl
  rw [opLength, opLength, hcoe]
  have hstar : (u : Matrix Y Y ℂ)ᴴ - 1 =
      ((u : Matrix Y Y ℂ) - 1)ᴴ := by simp
  rw [hstar, ← Matrix.star_eq_conjTranspose, norm_star]

/-- Conjugation does not change operator-norm length. -/
theorem opLength_conj (Y : FiniteModel)
    (t u : Matrix.unitaryGroup Y ℂ) :
    opLength Y (t * u * t⁻¹) = opLength Y u := by
  have htinv : (((t⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ))
      ∈ Matrix.unitaryGroup Y ℂ := (t⁻¹).2
  have hsplit :
      ((t * u * t⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) - 1 =
        (t : Matrix Y Y ℂ) * ((u : Matrix Y Y ℂ) - 1) *
          ((t⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) := by
    have hcancel : (t : Matrix Y Y ℂ) *
        ((t⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) = 1 :=
      congrArg Subtype.val (mul_inv_cancel t)
    change (t : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ) *
      ((t⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) - 1 = _
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hcancel]
  rw [opLength, opLength, hsplit, CStarRing.norm_mul_mem_unitary _ htinv,
    CStarRing.norm_mem_unitary_mul _ t.2]

/-- The identity converting quotient length to operator-norm distance. -/
theorem opLength_inv_mul (Y : FiniteModel)
    (a b : Matrix.unitaryGroup Y ℂ) :
    opLength Y (a⁻¹ * b) =
      ‖(b : Matrix Y Y ℂ) - (a : Matrix Y Y ℂ)‖ := by
  have hainv : (((a⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ))
      ∈ Matrix.unitaryGroup Y ℂ := (a⁻¹).2
  have hsplit :
      ((a⁻¹ * b : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) - 1 =
        ((a⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) *
          ((b : Matrix Y Y ℂ) - (a : Matrix Y Y ℂ)) := by
    have hcancel : (((a⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)) *
        (a : Matrix Y Y ℂ) = 1 :=
      congrArg Subtype.val (inv_mul_cancel a)
    change ((a⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) *
      (b : Matrix Y Y ℂ) - 1 = _
    rw [Matrix.mul_sub, hcancel]
  rw [opLength, hsplit, CStarRing.norm_mem_unitary_mul _ hainv]

/-! ## The norm ultraproduct -/

variable {ι : Type*} (𝒰 : Ultrafilter ι) (X : ι → FiniteModel)

/-- Sequences of unitaries converging to the identity in operator norm. -/
def IsNullOpSeq (u : ∀ i, Matrix.unitaryGroup (X i) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (𝒰 : Filter ι), opLength (X i) (u i) < ε

theorem isNullOpSeq_one : IsNullOpSeq 𝒰 X 1 := by
  intro ε hε
  filter_upwards with i
  simpa using hε

/-- Operator-norm-null sequences form a subgroup of the product. -/
def nullOpSubgroup : Subgroup (∀ i, Matrix.unitaryGroup (X i) ℂ) where
  carrier := {u | IsNullOpSeq 𝒰 X u}
  one_mem' := isNullOpSeq_one 𝒰 X
  mul_mem' := by
    intro u v hu hv ε hε
    filter_upwards [hu (ε / 2) (half_pos hε), hv (ε / 2) (half_pos hε)]
      with i hi hv
    exact (opLength_mul_le (X i) (u i) (v i)).trans_lt (by
      linarith only [hi, hv])
  inv_mem' := by
    intro u hu ε hε
    filter_upwards [hu ε hε] with i hi
    change opLength (X i) (u i)⁻¹ < ε
    rwa [opLength_inv]

instance nullOpSubgroup_normal : (nullOpSubgroup 𝒰 X).Normal where
  conj_mem := by
    intro u hu t ε hε
    filter_upwards [hu ε hε] with i hi
    change opLength (X i) (t i * u i * (t i)⁻¹) < ε
    rwa [opLength_conj]

/-- The operator-norm matrix ultraproduct unitary group. -/
abbrev UniversalWeakMF : Type _ :=
  (∀ i, Matrix.unitaryGroup (X i) ℂ) ⧸ nullOpSubgroup 𝒰 X

/-! ## A sequential weak-MF approximation is a faithful representation -/

end GroupApproximation
