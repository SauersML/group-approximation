import GroupApproximation.CharClass.OddPTotalPackagingCartan

/-!
# Packaging the reduced powers, part 5: passing through a single-component class

If the total power of a homogeneous class `z` of even degree `q` is a multiple of `z`, say
`ptotOf q z = ν • z`, then for every even class `w`

`P^i(z · w) = (μ^{-q/2} ν) • (z · P^i w)`.

Multiply the total powers, project to the degree of `P^i(z·w)`, and pull the factor `z` out of the
projection.  The scalar is uniform in `i` and `w`.  This is how the class `z = t x` of the mapping
torus enters Step D: its total power has components only in degrees `0` and `2n + 2`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace OddPTotal

open CategoryTheory

noncomputable section

/-- The degree projection passes through left multiplication by a homogeneous class. -/
theorem projDeg_of_mul (K : Type) [CommRing K] (X : TopCat.{0}) (q e : ℕ)
    (z : TotalPieceOf K X q) (y : TotalHOf K X) :
    projDeg K X (q + e) (TotalHOf.of K X q z * y) = TotalHOf.of K X q z * projDeg K X e y := by
  induction y using DirectSum.induction_on with
  | zero => simp only [mul_zero, map_zero]
  | of a w =>
    show projDeg K X (q + e) (TotalHOf.of K X q z * TotalHOf.of K X a w)
      = TotalHOf.of K X q z * projDeg K X e (TotalHOf.of K X a w)
    rw [← TotalHOf.of_mul, projDeg_of, projDeg_of]
    by_cases h : a = e
    · rw [if_pos (by rw [h]), if_pos h, TotalHOf.of_mul]
    · rw [if_neg (by omega), if_neg h, mul_zero]
  | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]

theorem lt_goodDeg_of_lt {p b i : ℕ} (hp : 2 ≤ p) (h : b < 2 * i) :
    p * b < b + 2 * i * (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hq : 1 ≤ q := by omega
  nlinarith

namespace TotalReducedPowers

variable {p : ℕ} (R : TotalReducedPowers p)

theorem projDeg_ptotOf_of_lt (X : TopCat.{0}) (b e : ℕ) (c : TotalPieceOf (ZMod p) X b)
    (he : p * b < e) : projDeg (ZMod p) X e (ptotOf R.D X b c) = 0 := by
  rw [projDeg_apply, R.component_ptotOf_of_lt X b e c he, map_zero]

/-- **`P^i` passes through a single-component class**, homogeneous form. -/
theorem totalP_mul_single_piece (X : TopCat.{0}) (hp : 2 ≤ p) {q : ℕ} (hq : q % 2 = 0)
    (z : TotalPieceOf (ZMod p) X q) (ν : ZMod p)
    (hz : ptotOf R.D X q z = ν • TotalHOf.of (ZMod p) X q z) (i : ℕ) {b : ℕ} (hb : b % 2 = 0)
    (c' : TotalPieceOf (ZMod p) X b) :
    R.totalP X i (TotalHOf.of (ZMod p) X q z * TotalHOf.of (ZMod p) X b c')
      = (R.μinv ^ (q / 2) * ν) •
          (TotalHOf.of (ZMod p) X q z * R.totalP X i (TotalHOf.of (ZMod p) X b c')) := by
  have hqb : (q + b) % 2 = 0 := by omega
  have hprod : ptotOf R.D X (q + b) (cup z c')
      = ν • (TotalHOf.of (ZMod p) X q z * ptotOf R.D X b c') := by
    rw [R.ptot_mul X (Nat.even_iff.mpr hq) (Nat.even_iff.mpr hb), hz, smul_mul_left]
  rw [← TotalHOf.of_mul]
  by_cases hi : 2 * i ≤ b
  · rw [R.totalP_of_eq X hqb i (by omega), R.totalP_of_eq X hb i hi, hprod, projDeg_smul,
      Nat.add_assoc q b (2 * i * (p - 1)), projDeg_of_mul, mul_smul_right, smul_smul, smul_smul]
    congr 1
    have hK : (q + b) / 2 - i = q / 2 + (b / 2 - i) := by omega
    rw [hK, pow_add]
    ring
  · rw [R.totalP_of_eq_zero X i (fun h => hi h.2), mul_zero, smul_zero]
    by_cases hi' : 2 * i ≤ q + b
    · rw [R.totalP_of_eq X hqb i hi', hprod, projDeg_smul, Nat.add_assoc q b (2 * i * (p - 1)),
        projDeg_of_mul, R.projDeg_ptotOf_of_lt X b _ c' (lt_goodDeg_of_lt hp (by omega)),
        mul_zero, smul_zero, smul_zero]
    · rw [R.totalP_of_eq_zero X i (fun h => hi' h.2)]

/-- **`P^i` passes through a single-component class**, for every even class `w`. -/
theorem totalP_mul_single (X : TopCat.{0}) (hp : 2 ≤ p) {q : ℕ} (hq : q % 2 = 0)
    (z : TotalPieceOf (ZMod p) X q) (ν : ZMod p)
    (hz : ptotOf R.D X q z = ν • TotalHOf.of (ZMod p) X q z) (i : ℕ) {w : TotalHOf (ZMod p) X}
    (hw : TotalHOf.IsEven w) :
    R.totalP X i (TotalHOf.of (ZMod p) X q z * w)
      = (R.μinv ^ (q / 2) * ν) • (TotalHOf.of (ZMod p) X q z * R.totalP X i w) := by
  classical
  rw [← TotalHOf.sum_support_of' (ZMod p) X w, Finset.mul_sum, map_sum, map_sum, Finset.mul_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b % 2 = 0
  · exact R.totalP_mul_single_piece X hp hq z ν hz i hb (w b)
  · have hwb : w b = 0 := hw b (Nat.odd_iff.mpr (by omega))
    simp only [hwb, map_zero, mul_zero, smul_zero]

end TotalReducedPowers

end

end OddPTotal

#audit_axioms OddPTotal.projDeg_of_mul
#audit_axioms OddPTotal.lt_goodDeg_of_lt
#audit_axioms OddPTotal.TotalReducedPowers.totalP_mul_single_piece
#audit_axioms OddPTotal.TotalReducedPowers.totalP_mul_single

end CharClass
end GroupApproximation
