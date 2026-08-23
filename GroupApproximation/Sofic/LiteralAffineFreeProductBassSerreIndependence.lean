import GroupApproximation.Sofic.LiteralAffineFreeProductBassSerreDisplacement

/-!
# Independent axes for the amplified affine source

The conjugator is the square of the marked left-factor defect.  It fixes the
left base vertex, while the square prevents complete cancellation at every
seam of the mixed words `g⁻ᵃ c gᵇ c⁻¹`.
-/

namespace GroupApproximation.LiteralAffineFreeProductBassSerre

open Monoid Monoid.CoprodI
open LiteralAffineCongruenceSource LiteralAffineFreeProductSource

noncomputable section

/-- A basepoint-fixing conjugator chosen to separate the crossing axis. -/
def axisConjugator : Ambient := markedDefect ^ 2

theorem axisConjugator_mem_leftFactor :
    axisConjugator ∈ BassSerreFreeProduct.leftFactor Envelope :=
  (BassSerreFreeProduct.leftFactor Envelope).pow_mem
    markedDefect_mem_leftFactor 2

@[simp] theorem axisConjugator_smul_baseLeft :
    axisConjugator •
        (BassSerreFreeProduct.baseLeft Envelope :
          BassSerreHullGeometry.PathVertex Envelope) =
      BassSerreFreeProduct.baseLeft Envelope :=
  (BassSerreFreeProduct.smul_baseLeft_eq_iff Envelope axisConjugator).mpr
    axisConjugator_mem_leftFactor

/-- The conjugate crossing element which supplies the second axis. -/
def separatedCrossing : Ambient :=
  axisConjugator * crossingDefect * axisConjugator⁻¹

theorem separatedCrossing_mem :
    separatedCrossing ∈ amplifiedDefectData.core.defectNormal :=
  (inferInstance : amplifiedDefectData.core.defectNormal.Normal).conj_mem
    crossingDefect crossingDefect_mem axisConjugator

theorem separatedCrossing_isLoxodromic :
    HullGeometry.IsLoxodromic separatedCrossing
      (BassSerreFreeProduct.baseLeft Envelope :
        BassSerreHullGeometry.PathVertex Envelope) :=
  HullGeometry.isLoxodromic_conj bassSerre_isometric
    crossingDefect_isLoxodromic

/-! Reduced-word repetition without normalization. -/

private def repeatThen {M : Bool → Type*} [∀ i, Group (M i)]
    {i j k : Bool} (hji : j ≠ i) (u : CoprodI.NeWord M i j) :
    (n : ℕ) → CoprodI.NeWord M i k → CoprodI.NeWord M i k
  | 0, v => v
  | n + 1, v => u.append hji (repeatThen hji u n v)

private theorem repeatThen_prod {M : Bool → Type*} [∀ i, Group (M i)]
    {i j k : Bool} (hji : j ≠ i) (u : CoprodI.NeWord M i j)
    (n : ℕ) (v : CoprodI.NeWord M i k) :
    (repeatThen hji u n v).prod = u.prod ^ n * v.prod := by
  induction n with
  | zero => simp [repeatThen]
  | succ n ih =>
      rw [repeatThen, CoprodI.NeWord.append_prod, ih, pow_succ']
      simp only [mul_assoc]

private theorem repeatThen_length {M : Bool → Type*} [∀ i, Group (M i)]
    {i j k : Bool} (hji : j ≠ i) (u : CoprodI.NeWord M i j)
    (n : ℕ) (v : CoprodI.NeWord M i k) :
    (repeatThen hji u n v).toList.length =
      n * u.toList.length + v.toList.length := by
  induction n with
  | zero => simp [repeatThen]
  | succ n ih =>
      simp only [repeatThen, CoprodI.NeWord.toList, List.length_append, ih]
      omega

/-! The first of the four sign quadrants.  Keeping this lemma generic makes
the normal-form calculation independent of the affine source. -/

private theorem mixed_neg_pos_sylLength
    {M : Bool → Type*} [∀ i, Group (M i)] [∀ i, DecidableEq (M i)]
    {x : M false} {y : M true}
    (htf : IsPowerTorsionFree (M false))
    (hx : x ≠ 1) (hy : y ≠ 1) (hx2 : x ^ 2 ≠ 1)
    (_hxm2 : x⁻¹ ^ 2 ≠ 1) (hxi : x⁻¹ ≠ 1) (hyi : y⁻¹ ≠ 1)
    (n m : ℕ) :
    let u : CoprodI.NeWord M true false :=
      ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
        (CoprodI.NeWord.singleton x hx)).append Bool.false_ne_true
          ((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
            (CoprodI.NeWord.singleton x⁻¹ hxi))
    let v : CoprodI.NeWord M false true := u.inv
    4 * (n + 1) + 4 * (m + 1) ≤
      FreeProductCyclic.sylLength
        (v.prod ^ (n + 1) * CoprodI.of (x ^ 2) *
          u.prod ^ (m + 1) * CoprodI.of (x⁻¹ ^ 2)) := by
  intro u v
  have hx3 : x⁻¹ * x⁻¹ ^ 2 ≠ 1 := by
    intro h
    have : x ^ 3 = 1 := by
      have := congrArg (fun z : M false => z⁻¹) h
      simpa [pow_succ', mul_assoc] using this
    exact hx (htf x 3 (by omega) this)
  let va : CoprodI.NeWord M false false :=
    v.append Bool.false_ne_true.symm (CoprodI.NeWord.singleton (x ^ 2) hx2)
  let tail : CoprodI.NeWord M true false :=
    ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
      (CoprodI.NeWord.singleton x hx)).append Bool.false_ne_true
        ((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
          (CoprodI.NeWord.singleton (x⁻¹ * x⁻¹ ^ 2) hx3))
  let middle : CoprodI.NeWord M true false :=
    repeatThen Bool.false_ne_true u m tail
  let rest : CoprodI.NeWord M false false :=
    va.append Bool.false_ne_true middle
  let W : CoprodI.NeWord M false false :=
    repeatThen Bool.false_ne_true.symm v n rest
  have huLen : u.toList.length = 4 := by simp [u, CoprodI.NeWord.toList]
  have hvLen : v.toList.length = 4 := by
    simp [v, FreeProductCyclic.toList_length_inv, huLen]
  have htailLen : tail.toList.length = 4 := by
    simp [tail, CoprodI.NeWord.toList]
  have hvaLen : va.toList.length = 5 := by
    simp [va, CoprodI.NeWord.toList, hvLen]
  have hWLen : W.toList.length = 4 * n + 4 * m + 9 := by
    simp only [W, repeatThen_length, hvLen, rest, CoprodI.NeWord.toList,
      List.length_append, hvaLen, middle, huLen, htailLen]
    omega
  have htailProd : tail.prod = u.prod * CoprodI.of (x⁻¹ ^ 2) := by
    simp [tail, u, CoprodI.NeWord.append_prod, pow_two, mul_assoc]
  have hWProd : W.prod =
      v.prod ^ (n + 1) * CoprodI.of (x ^ 2) *
        u.prod ^ (m + 1) * CoprodI.of (x⁻¹ ^ 2) := by
    simp only [W, repeatThen_prod, rest, CoprodI.NeWord.append_prod, va,
      middle, htailProd]
    rw [pow_succ', pow_succ']
    group
  rw [← hWProd]
  have hlen : FreeProductCyclic.sylLength W.prod = W.toList.length :=
    FreeProductCyclic.sylLength_eq_of_neWord
      (FreeProductCyclic.equiv_prod W).symm
  rw [hlen, hWLen]
  omega

end

end GroupApproximation.LiteralAffineFreeProductBassSerre
