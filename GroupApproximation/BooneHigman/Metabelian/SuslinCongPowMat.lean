import GroupApproximation.BooneHigman.Metabelian.SuslinCongLocGen
import GroupApproximation.Meta.AxiomGuard

/-!
# Explicit `3 × 3` bookkeeping over `Fin 2 ⊕ Unit`

Lane `bh-met-92r`.  Helper module for the rank-3 Mennicke-product identity
(`SuslinCongPowMennicke.lean`).  We write `1 = inl 0`, `2 = inl 1`, `3 = inr ()`.

* `suslinCongPow_m3`: the matrix with the nine listed entries (row by row);
  `suslinCongPow_ext3` (entrywise equality), `suslinCongPow_m3_mul` (the product formula),
  `suslinCongPow_m3_congr`.
* The values of the elementary units `E₃₂, E₁₂, E₂₁, E₂₃` as `suslinCongPow_m3`.
* The values of `diag(σ, 1)` and of its reindexings along `suslinCongPow_e₁`
  (`σ` in coordinates `(2, 3)`) and `suslinCongPow_e₂` (`σ` in coordinates `(1, 3)`).
-/

set_option linter.unreachableTactic false

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- The `3 × 3` matrix over `Fin 2 ⊕ Unit` with the given entries, listed row by row. -/
def suslinCongPow_m3 {S : Type*} (p11 p12 p13 p21 p22 p23 p31 p32 p33 : S) :
    Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S :=
  Matrix.of fun i j ↦
    Sum.elim
      (fun i' : Fin 2 ↦
        Sum.elim (fun j' : Fin 2 ↦ ![![p11, p12], ![p21, p22]] i' j')
          (fun _ : Unit ↦ ![p13, p23] i') j)
      (fun _ : Unit ↦ Sum.elim (fun j' : Fin 2 ↦ ![p31, p32] j') (fun _ : Unit ↦ p33) j) i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_m3

/-- Entrywise equality with a `suslinCongPow_m3`. -/
theorem suslinCongPow_ext3 {S : Type*} {M : Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S}
    {p11 p12 p13 p21 p22 p23 p31 p32 p33 : S}
    (h11 : M (Sum.inl 0) (Sum.inl 0) = p11) (h12 : M (Sum.inl 0) (Sum.inl 1) = p12)
    (h13 : M (Sum.inl 0) (Sum.inr ()) = p13) (h21 : M (Sum.inl 1) (Sum.inl 0) = p21)
    (h22 : M (Sum.inl 1) (Sum.inl 1) = p22) (h23 : M (Sum.inl 1) (Sum.inr ()) = p23)
    (h31 : M (Sum.inr ()) (Sum.inl 0) = p31) (h32 : M (Sum.inr ()) (Sum.inl 1) = p32)
    (h33 : M (Sum.inr ()) (Sum.inr ()) = p33) :
    M = suslinCongPow_m3 p11 p12 p13 p21 p22 p23 p31 p32 p33 := by
  refine Matrix.ext fun i j ↦ ?_
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
  · fin_cases i <;> fin_cases j
    · exact h11
    · exact h12
    · exact h21
    · exact h22
  · fin_cases i
    · exact h13
    · exact h23
  · fin_cases j
    · exact h31
    · exact h32
  · exact h33

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_ext3

/-- Congruence for `suslinCongPow_m3`. -/
theorem suslinCongPow_m3_congr {S : Type*}
    {a11 a12 a13 a21 a22 a23 a31 a32 a33 b11 b12 b13 b21 b22 b23 b31 b32 b33 : S}
    (h11 : a11 = b11) (h12 : a12 = b12) (h13 : a13 = b13) (h21 : a21 = b21) (h22 : a22 = b22)
    (h23 : a23 = b23) (h31 : a31 = b31) (h32 : a32 = b32) (h33 : a33 = b33) :
    suslinCongPow_m3 a11 a12 a13 a21 a22 a23 a31 a32 a33 =
      suslinCongPow_m3 b11 b12 b13 b21 b22 b23 b31 b32 b33 := by
  subst h11 h12 h13 h21 h22 h23 h31 h32 h33
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_m3_congr

/-- A matrix product over `Fin 2 ⊕ Unit`, entrywise. -/
theorem suslinCongPow_mul_apply {S : Type*} [CommRing S]
    (M N : Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S) (i j : Fin 2 ⊕ Unit) :
    (M * N) i j = M i (Sum.inl 0) * N (Sum.inl 0) j + M i (Sum.inl 1) * N (Sum.inl 1) j +
      M i (Sum.inr ()) * N (Sum.inr ()) j := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_unique] <;> rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_mul_apply

/-- **The product formula** for `suslinCongPow_m3`. -/
theorem suslinCongPow_m3_mul {S : Type*} [CommRing S]
    (a11 a12 a13 a21 a22 a23 a31 a32 a33 b11 b12 b13 b21 b22 b23 b31 b32 b33 : S) :
    suslinCongPow_m3 a11 a12 a13 a21 a22 a23 a31 a32 a33 *
        suslinCongPow_m3 b11 b12 b13 b21 b22 b23 b31 b32 b33 =
      suslinCongPow_m3
        (a11 * b11 + a12 * b21 + a13 * b31) (a11 * b12 + a12 * b22 + a13 * b32)
        (a11 * b13 + a12 * b23 + a13 * b33)
        (a21 * b11 + a22 * b21 + a23 * b31) (a21 * b12 + a22 * b22 + a23 * b32)
        (a21 * b13 + a22 * b23 + a23 * b33)
        (a31 * b11 + a32 * b21 + a33 * b31) (a31 * b12 + a32 * b22 + a33 * b32)
        (a31 * b13 + a32 * b23 + a33 * b33) := by
  refine suslinCongPow_ext3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    rw [suslinCongPow_mul_apply] <;> rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_m3_mul

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
