import GroupApproximation.Leavitt.Leavitt

/-!
# Finite modules over a binary Leavitt ring are trivial

The binary Leavitt relations identify every unital module with its Cartesian
square.  A finite module must therefore have one element.  This is the exact
dimension obstruction used by the dual-orbit argument: a finite-rank
multiplication pairing would produce a nonzero finite quotient module.
-/

namespace GroupApproximation
namespace LeavittFamily

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- The binary Leavitt relations identify every left module with its square. -/
def moduleEquivProd (L : LeavittFamily A) : M ≃ M × M where
  toFun x := (L.t0 • x, L.t1 • x)
  invFun y := L.s0 • y.1 + L.s1 • y.2
  left_inv x := by
    change L.s0 • (L.t0 • x) + L.s1 • (L.t1 • x) = x
    rw [← mul_smul, ← mul_smul, ← add_smul, L.sum_range, one_smul]
  right_inv y := by
    rcases y with ⟨y0, y1⟩
    apply Prod.ext
    · change L.t0 • (L.s0 • y0 + L.s1 • y1) = y0
      simp [smul_add, ← mul_smul]
    · change L.t1 • (L.s0 • y0 + L.s1 • y1) = y1
      simp [smul_add, ← mul_smul]

/-- A finite unital module over a ring carrying a binary Leavitt family has
exactly one element. -/
theorem finite_module_subsingleton (L : LeavittFamily A) [Fintype M] :
    Subsingleton M := by
  have hcard : Fintype.card M = Fintype.card M * Fintype.card M := by
    calc
      Fintype.card M = Fintype.card (M × M) :=
        Fintype.card_congr L.moduleEquivProd
      _ = Fintype.card M * Fintype.card M := Fintype.card_prod M M
  have hpos : 0 < Fintype.card M := Fintype.card_pos_iff.mpr ⟨0⟩
  have hmul : Fintype.card M * 1 = Fintype.card M * Fintype.card M := by
    simpa using hcard
  have hone' : 1 = Fintype.card M :=
    Nat.eq_of_mul_eq_mul_left hpos hmul
  have hone : Fintype.card M = 1 := hone'.symm
  constructor
  exact Fintype.card_le_one_iff.mp hone.le

end LeavittFamily
end GroupApproximation
