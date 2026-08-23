import GroupApproximation.Sofic.LiteralAffineFreeProductBassSerre

/-!
# Short displacement estimates for the explicit Bass--Serre defect

This small module is kept separate from the normal-form/loxodromy adapter so
the latter remains a fast compilation unit.  It supplies only the upper
estimates used in the independent-axis calculation.
-/

namespace GroupApproximation.LiteralAffineFreeProductBassSerre

open Monoid Monoid.CoprodI
open LiteralAffineCongruenceSource LiteralAffineFreeProductSource

noncomputable section

/-- One crossing commutator moves the left base vertex by at most four edges. -/
theorem crossingDefect_displacement_le_four :
    dist (BassSerreFreeProduct.baseLeft Envelope :
        BassSerreHullGeometry.PathVertex Envelope)
      (crossingDefect •
        (BassSerreFreeProduct.baseLeft Envelope :
          BassSerreHullGeometry.PathVertex Envelope)) ≤ 4 := by
  let o : BassSerreHullGeometry.PathVertex Envelope :=
    BassSerreFreeProduct.baseLeft Envelope
  have hdFix : markedDefect • o = o :=
    (BassSerreFreeProduct.smul_baseLeft_eq_iff Envelope markedDefect).mpr
      markedDefect_mem_leftFactor
  have hdiFix : markedDefect⁻¹ • o = o :=
    (BassSerreFreeProduct.smul_baseLeft_eq_iff Envelope markedDefect⁻¹).mpr
      ((BassSerreFreeProduct.leftFactor Envelope).inv_mem markedDefect_mem_leftFactor)
  let yr : BinaryCoprodNormalForm.factor Envelope true :=
    MulEquiv.ulift.symm (Multiplicative.ofAdd (1 : ℤ))
  have hr : rightShift =
      BinaryCoprodNormalForm.fromIndexed Envelope (CoprodI.of yr) := by
    simp [rightShift, yr]
  have hri : rightShift⁻¹ =
      BinaryCoprodNormalForm.fromIndexed Envelope (CoprodI.of yr⁻¹) := by
    simp [hr]
  have hrMove : dist o (rightShift • o) ≤ 2 := by
    rw [hr]
    exact BassSerreHullGeometry.dist_fromIndexed_of_true_smul_baseLeft_le_two
      Envelope yr
  have hriMove : dist o (rightShift⁻¹ • o) ≤ 2 := by
    rw [hri]
    exact BassSerreHullGeometry.dist_fromIndexed_of_true_smul_baseLeft_le_two
      Envelope yr⁻¹
  have hfirst : dist o ((rightShift * markedDefect) • o) ≤ 2 := by
    simpa only [mul_smul, hdFix] using hrMove
  have hsecond : dist o ((rightShift⁻¹ * markedDefect⁻¹) • o) ≤ 2 := by
    simpa only [mul_smul, hdiFix] using hriMove
  have hsub := BassSerreHullGeometry.dist_mul_smul_baseLeft_le Envelope
    (rightShift * markedDefect) (rightShift⁻¹ * markedDefect⁻¹)
  rw [show (rightShift * markedDefect) * (rightShift⁻¹ * markedDefect⁻¹) =
      crossingDefect by simp only [crossingDefect, mul_assoc]] at hsub
  calc
    dist o (crossingDefect • o) ≤
        dist o ((rightShift * markedDefect) • o) +
          dist o ((rightShift⁻¹ * markedDefect⁻¹) • o) := hsub
    _ ≤ 2 + 2 := add_le_add hfirst hsecond
    _ = 4 := by norm_num

/-- Hence the `n`-th positive power has displacement at most `4n`. -/
theorem crossingDefect_pow_displacement_le (n : ℕ) :
    dist (BassSerreFreeProduct.baseLeft Envelope :
        BassSerreHullGeometry.PathVertex Envelope)
      ((crossingDefect ^ n) •
        (BassSerreFreeProduct.baseLeft Envelope :
          BassSerreHullGeometry.PathVertex Envelope)) ≤ 4 * n := by
  have hpow := HullGeometry.dist_pow_le bassSerre_isometric crossingDefect
    (BassSerreFreeProduct.baseLeft Envelope :
      BassSerreHullGeometry.PathVertex Envelope) n
  calc
    _ ≤ (n : ℝ) * dist
        (BassSerreFreeProduct.baseLeft Envelope :
          BassSerreHullGeometry.PathVertex Envelope)
        (crossingDefect •
          (BassSerreFreeProduct.baseLeft Envelope :
            BassSerreHullGeometry.PathVertex Envelope)) := hpow
    _ ≤ (n : ℝ) * 4 :=
      mul_le_mul_of_nonneg_left crossingDefect_displacement_le_four
        (Nat.cast_nonneg n)
    _ = 4 * n := by ring

end

end GroupApproximation.LiteralAffineFreeProductBassSerre
