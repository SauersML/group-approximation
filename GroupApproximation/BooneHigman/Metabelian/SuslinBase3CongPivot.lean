import GroupApproximation.BooneHigman.Metabelian.SuslinHorrocksReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2, congruence core: the unit-pivot lemma in rank two

Lane `bh-met-91k`.

* `suslinBase3Cong_mem_of_row`: a `2 × 2` matrix of determinant `1` whose row `0` is `e₀` is
  elementary.  Indeed its entries are `1, 0, c, d`, and `d = det = 1`, so it is `x₁₀(c)`.
* `suslinBase3Cong_mem_of_isUnit`: over any commutative ring `R`, a `2 × 2` matrix of determinant
  `1` whose `(0,0)` entry is a unit lies in `E₂(R)`.

  **Proof.**  Let `a = M₀₀ = u` be a unit and `b = M₀₁`.  A column move `x₀₁(u⁻¹(1 - b))` makes
  the `(0,1)` entry `b + u u⁻¹ (1 - b) = 1`.  The row with a `1` at column `1` is cleared to `e₁`
  (`suslinHorrocks_clear_of_eq_one`), then moved to `e₀` (`suslinHorrocks_move_single`).  All
  right factors are elementary, so the determinant stays `1`, and the previous item applies.
  No Whitehead lemma and no locality is used.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **Row `e₀` in rank two.**  Determinant `1` and row `0` equal to `e₀` force `x₁₀(c)`. -/
theorem suslinBase3Cong_mem_of_row {R : Type*} [CommRing R]
    (N : (Matrix (Fin 2) (Fin 2) R)ˣ) (hdet : Matrix.det (N : Matrix (Fin 2) (Fin 2) R) = 1)
    (hrow : ∀ c : Fin 2, (N : Matrix (Fin 2) (Fin 2) R) 0 c = if c = 0 then 1 else 0) :
    N ∈ elementaryGroup (Fin 2) R := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h00 : (N : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 := by rw [hrow 0, if_pos rfl]
  have h01' : (N : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := by rw [hrow 1, if_neg h10]
  have h11 : (N : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by
    rw [Matrix.det_fin_two, h00, h01', one_mul, zero_mul, sub_zero] at hdet
    exact hdet
  have hE : ∀ i j : Fin 2,
      ((elementaryUnit (1 : Fin 2) 0 h10 ((N : Matrix (Fin 2) (Fin 2) R) 1 0) :
        (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R) i j =
        (1 : Matrix (Fin 2) (Fin 2) R) i j +
          Matrix.single (1 : Fin 2) (0 : Fin 2) ((N : Matrix (Fin 2) (Fin 2) R) 1 0) i j :=
    fun _ _ ↦ rfl
  have hEq : N = elementaryUnit (1 : Fin 2) 0 h10 ((N : Matrix (Fin 2) (Fin 2) R) 1 0) := by
    apply Units.ext
    refine Matrix.ext ?_
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hE, h00, Matrix.one_apply_eq, Matrix.single_apply_of_row_ne h10, add_zero]
    · rw [hE, h01', Matrix.one_apply_ne h01, Matrix.single_apply_of_row_ne h10, add_zero]
    · rw [hE, Matrix.one_apply_ne h10, Matrix.single_apply_same, zero_add]
    · rw [hE, h11, Matrix.one_apply_eq, Matrix.single_apply_of_col_ne _ _ h01, add_zero]
  rw [hEq]
  exact elementaryUnit_mem _ _ _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_mem_of_row

/-- **Unit pivot in rank two.**  A `2 × 2` matrix of determinant `1` with a unit `(0,0)` entry
is elementary, over every commutative ring. -/
theorem suslinBase3Cong_mem_of_isUnit {R : Type*} [CommRing R]
    (M : (Matrix (Fin 2) (Fin 2) R)ˣ) (hdet : Matrix.det (M : Matrix (Fin 2) (Fin 2) R) = 1)
    (ha : IsUnit ((M : Matrix (Fin 2) (Fin 2) R) 0 0)) :
    M ∈ elementaryGroup (Fin 2) R := by
  obtain ⟨u, hu⟩ := ha
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : (Matrix (Fin 2) (Fin 2) R)ˣ, E₁ = elementaryUnit (0 : Fin 2) 1 h01
      (((u⁻¹ : Rˣ) : R) * (1 -(M : Matrix (Fin 2) (Fin 2) R) 0 1)) := ⟨_, rfl⟩
  have hE₁mem : E₁ ∈ elementaryGroup (Fin 2) R := by
    rw [hE₁]
    exact elementaryUnit_mem _ _ _ _
  have hrow : ((M * E₁ : (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R) 0 1 = 1 := by
    rw [hE₁, Units.val_mul, mul_elementaryUnit_apply, if_pos rfl, ← hu, ← mul_assoc,
      Units.mul_inv, one_mul]
    ring
  obtain ⟨F₂, hF₂, hrow₂⟩ := suslinHorrocks_clear_of_eq_one (M * E₁) 0 1 hrow
  obtain ⟨F₃, hF₃, hrow₃⟩ := suslinHorrocks_move_single (M * E₁ * F₂) 0 1 hrow₂
  have hdetN : Matrix.det ((M * E₁ * F₂ * F₃ : (Matrix (Fin 2) (Fin 2) R)ˣ) :
      Matrix (Fin 2) (Fin 2) R) = 1 := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_mul, hdet, suslin_det_eq_one_of_mem_elementaryGroup hE₁mem,
      suslin_det_eq_one_of_mem_elementaryGroup hF₂, suslin_det_eq_one_of_mem_elementaryGroup hF₃,
      mul_one, mul_one, mul_one]
  have hN := suslinBase3Cong_mem_of_row _ hdetN hrow₃
  have hprod := mul_mem (mul_mem (mul_mem hN (inv_mem hF₃)) (inv_mem hF₂)) (inv_mem hE₁mem)
  rwa [mul_inv_cancel_right, mul_inv_cancel_right, mul_inv_cancel_right] at hprod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_mem_of_isUnit

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
