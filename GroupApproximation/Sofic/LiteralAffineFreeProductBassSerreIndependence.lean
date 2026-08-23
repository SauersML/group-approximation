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
      simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm]

/-- Cyclically reduced powers retain their full syllable length after a fixed
conjugation. -/
private theorem cyclic_npow_conj_sylLength_lower
    {M : Bool → Type*} [∀ i, Group (M i)] [∀ i, DecidableEq (M i)]
    {i j : Bool} (hij : i ≠ j) (u : CoprodI.NeWord M i j)
    (c : CoprodI M) (n : ℕ) :
    (n + 1) * u.toList.length ≤
      FreeProductCyclic.sylLength
        (c * u.prod ^ (n + 1) * c⁻¹) := by
  let w := FreeProductCyclic.npow hij u n
  have hwProd : w.prod = u.prod ^ (n + 1) :=
    FreeProductCyclic.npow_prod hij u n
  have hwLen : w.toList.length = (n + 1) * u.toList.length := by
    simpa [w] using FreeProductCyclic.npow_toList_length hij u n
  rw [← hwProd, ← hwLen]
  exact FreeProductCyclic.length_le_sylLength_conj hij w c

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
    simp only [CoprodI.NeWord.prod_singleton]
    rw [pow_succ', pow_succ']
    group
  rw [← hWProd]
  have hlen : FreeProductCyclic.sylLength W.prod = W.toList.length :=
    FreeProductCyclic.sylLength_eq_of_neWord
      (FreeProductCyclic.equiv_prod W.toWord).symm
  rw [hlen, hWLen]
  omega

private theorem mixed_neg_neg_sylLength
    {M : Bool → Type*} [∀ i, Group (M i)] [∀ i, DecidableEq (M i)]
    {x : M false} {y : M true}
    (htf : IsPowerTorsionFree (M false))
    (hx : x ≠ 1) (hy : y ≠ 1) (_hx2 : x ^ 2 ≠ 1)
    (hxm2 : x⁻¹ ^ 2 ≠ 1) (hxi : x⁻¹ ≠ 1) (hyi : y⁻¹ ≠ 1)
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
          v.prod ^ (m + 1) * CoprodI.of (x⁻¹ ^ 2)) := by
  intro u v
  have hx3 : x ^ 3 ≠ 1 := fun h => hx (htf x 3 (by omega) h)
  let core : CoprodI.NeWord M false true :=
    (((CoprodI.NeWord.singleton x hx).append Bool.false_ne_true
      (CoprodI.NeWord.singleton y hy)).append Bool.false_ne_true.symm
        (CoprodI.NeWord.singleton x⁻¹ hxi)).append Bool.false_ne_true
          (((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
            (CoprodI.NeWord.singleton (x ^ 3) hx3)).append Bool.false_ne_true
              ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
                ((CoprodI.NeWord.singleton x⁻¹ hxi).append Bool.false_ne_true
                  (CoprodI.NeWord.singleton y⁻¹ hyi))))
  let tail : CoprodI.NeWord M false false :=
    CoprodI.NeWord.singleton (x⁻¹ ^ 2) hxm2
  let middle : CoprodI.NeWord M false false :=
    repeatThen Bool.false_ne_true.symm v m tail
  let rest : CoprodI.NeWord M false false :=
    core.append Bool.false_ne_true.symm middle
  let W : CoprodI.NeWord M false false :=
    repeatThen Bool.false_ne_true.symm v n rest
  have huLen : u.toList.length = 4 := by simp [u, CoprodI.NeWord.toList]
  have hvLen : v.toList.length = 4 := by
    simp [v, FreeProductCyclic.toList_length_inv, huLen]
  have hcoreLen : core.toList.length = 8 := by
    simp [core, CoprodI.NeWord.toList]
  have htailLen : tail.toList.length = 1 := by simp [tail, CoprodI.NeWord.toList]
  have hWLen : W.toList.length = 4 * n + 4 * m + 9 := by
    simp only [W, repeatThen_length, hvLen, rest, CoprodI.NeWord.toList,
      List.length_append, hcoreLen, middle, htailLen]
    omega
  have hcoreProd : core.prod = v.prod * CoprodI.of (x ^ 2) * v.prod := by
    simp [core, v, u, CoprodI.NeWord.append_prod, pow_succ', mul_assoc]
  have hWProd : W.prod =
      v.prod ^ (n + 1) * CoprodI.of (x ^ 2) *
        v.prod ^ (m + 1) * CoprodI.of (x⁻¹ ^ 2) := by
    simp only [W, repeatThen_prod, rest, CoprodI.NeWord.append_prod,
      middle, tail, hcoreProd, CoprodI.NeWord.prod_singleton]
    rw [pow_succ', pow_succ']
    group
  rw [← hWProd]
  have hlen : FreeProductCyclic.sylLength W.prod = W.toList.length :=
    FreeProductCyclic.sylLength_eq_of_neWord
      (FreeProductCyclic.equiv_prod W.toWord).symm
  rw [hlen, hWLen]
  omega

private theorem mixed_pos_pos_sylLength
    {M : Bool → Type*} [∀ i, Group (M i)] [∀ i, DecidableEq (M i)]
    {x : M false} {y : M true}
    (htf : IsPowerTorsionFree (M false))
    (hx : x ≠ 1) (hy : y ≠ 1) (_hx2 : x ^ 2 ≠ 1)
    (_hxm2 : x⁻¹ ^ 2 ≠ 1) (hxi : x⁻¹ ≠ 1) (hyi : y⁻¹ ≠ 1)
    (n m : ℕ) :
    let u : CoprodI.NeWord M true false :=
      ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
        (CoprodI.NeWord.singleton x hx)).append Bool.false_ne_true
          ((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
            (CoprodI.NeWord.singleton x⁻¹ hxi))
    4 * (n + 1) + 4 * (m + 1) ≤
      FreeProductCyclic.sylLength
        (u.prod ^ (n + 1) * CoprodI.of (x ^ 2) *
          u.prod ^ (m + 1) * CoprodI.of (x⁻¹ ^ 2)) := by
  intro u
  have hxm3 : x⁻¹ * x⁻¹ ^ 2 ≠ 1 := by
    intro h
    have h3 : x ^ 3 = 1 := by
      have hi := congrArg (fun z : M false => z⁻¹) h
      simpa [pow_succ', mul_assoc] using hi
    exact hx (htf x 3 (by omega) h3)
  let head : CoprodI.NeWord M true false :=
    ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
      (CoprodI.NeWord.singleton x hx)).append Bool.false_ne_true
        ((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
          (CoprodI.NeWord.singleton (x⁻¹ * x ^ 2) (by
            simpa [pow_two] using hx)))
  let tail : CoprodI.NeWord M true false :=
    ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
      (CoprodI.NeWord.singleton x hx)).append Bool.false_ne_true
        ((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
          (CoprodI.NeWord.singleton (x⁻¹ * x⁻¹ ^ 2) hxm3))
  let middle : CoprodI.NeWord M true false :=
    repeatThen Bool.false_ne_true u m tail
  let rest : CoprodI.NeWord M true false :=
    head.append Bool.false_ne_true middle
  let W : CoprodI.NeWord M true false :=
    repeatThen Bool.false_ne_true u n rest
  have huLen : u.toList.length = 4 := by simp [u, CoprodI.NeWord.toList]
  have hheadLen : head.toList.length = 4 := by simp [head, CoprodI.NeWord.toList]
  have htailLen : tail.toList.length = 4 := by simp [tail, CoprodI.NeWord.toList]
  have hWLen : W.toList.length = 4 * n + 4 * m + 8 := by
    simp only [W, repeatThen_length, huLen, rest, CoprodI.NeWord.toList,
      List.length_append, hheadLen, middle, htailLen]
    omega
  have hheadProd : head.prod = u.prod * CoprodI.of (x ^ 2) := by
    simp [head, u, CoprodI.NeWord.append_prod, pow_two, mul_assoc]
  have htailProd : tail.prod = u.prod * CoprodI.of (x⁻¹ ^ 2) := by
    simp [tail, u, CoprodI.NeWord.append_prod, pow_two, mul_assoc]
  have hWProd : W.prod =
      u.prod ^ (n + 1) * CoprodI.of (x ^ 2) *
        u.prod ^ (m + 1) * CoprodI.of (x⁻¹ ^ 2) := by
    simp only [W, repeatThen_prod, rest, CoprodI.NeWord.append_prod,
      middle, hheadProd, htailProd]
    rw [pow_succ', pow_succ']
    group
  rw [← hWProd]
  have hlen : FreeProductCyclic.sylLength W.prod = W.toList.length :=
    FreeProductCyclic.sylLength_eq_of_neWord
      (FreeProductCyclic.equiv_prod W.toWord).symm
  rw [hlen, hWLen]
  omega

private theorem mixed_pos_neg_sylLength
    {M : Bool → Type*} [∀ i, Group (M i)] [∀ i, DecidableEq (M i)]
    {x : M false} {y : M true}
    (_htf : IsPowerTorsionFree (M false))
    (hx : x ≠ 1) (hy : y ≠ 1) (hx2 : x ^ 2 ≠ 1)
    (hxm2 : x⁻¹ ^ 2 ≠ 1) (hxi : x⁻¹ ≠ 1) (hyi : y⁻¹ ≠ 1)
    (n m : ℕ) :
    let u : CoprodI.NeWord M true false :=
      ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
        (CoprodI.NeWord.singleton x hx)).append Bool.false_ne_true
          ((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
            (CoprodI.NeWord.singleton x⁻¹ hxi))
    let v : CoprodI.NeWord M false true := u.inv
    4 * (n + 1) + 4 * (m + 1) ≤
      FreeProductCyclic.sylLength
        (u.prod ^ (n + 1) * CoprodI.of (x ^ 2) *
          v.prod ^ (m + 1) * CoprodI.of (x⁻¹ ^ 2)) := by
  intro u v
  let core : CoprodI.NeWord M true true :=
    ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
      (CoprodI.NeWord.singleton x hx)).append Bool.false_ne_true
        (((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
          (CoprodI.NeWord.singleton (x ^ 2) hx2)).append Bool.false_ne_true
            ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
              ((CoprodI.NeWord.singleton x⁻¹ hxi).append Bool.false_ne_true
                (CoprodI.NeWord.singleton y⁻¹ hyi))))
  let tail : CoprodI.NeWord M false false :=
    CoprodI.NeWord.singleton (x⁻¹ ^ 2) hxm2
  let middle : CoprodI.NeWord M false false :=
    repeatThen Bool.false_ne_true.symm v m tail
  let rest : CoprodI.NeWord M true false :=
    core.append Bool.false_ne_true.symm middle
  let W : CoprodI.NeWord M true false :=
    repeatThen Bool.false_ne_true u n rest
  have huLen : u.toList.length = 4 := by simp [u, CoprodI.NeWord.toList]
  have hvLen : v.toList.length = 4 := by
    simp [v, FreeProductCyclic.toList_length_inv, huLen]
  have hcoreLen : core.toList.length = 7 := by simp [core, CoprodI.NeWord.toList]
  have htailLen : tail.toList.length = 1 := by simp [tail, CoprodI.NeWord.toList]
  have hWLen : W.toList.length = 4 * n + 4 * m + 8 := by
    simp only [W, repeatThen_length, huLen, rest, CoprodI.NeWord.toList,
      List.length_append, hcoreLen, middle, hvLen, htailLen]
    omega
  have hcoreProd : core.prod = u.prod * CoprodI.of (x ^ 2) * v.prod := by
    simp [core, v, u, CoprodI.NeWord.append_prod, pow_two, mul_assoc]
  have hWProd : W.prod =
      u.prod ^ (n + 1) * CoprodI.of (x ^ 2) *
        v.prod ^ (m + 1) * CoprodI.of (x⁻¹ ^ 2) := by
    simp only [W, repeatThen_prod, rest, CoprodI.NeWord.append_prod,
      middle, tail, hcoreProd, CoprodI.NeWord.prod_singleton]
    rw [pow_succ', pow_succ']
    group
  rw [← hWProd]
  have hlen : FreeProductCyclic.sylLength W.prod = W.toList.length :=
    FreeProductCyclic.sylLength_eq_of_neWord
      (FreeProductCyclic.equiv_prod W.toWord).symm
  rw [hlen, hWLen]
  omega

/-- All four orientations of the two axes, including zero exponents. -/
private theorem mixed_zpow_sylLength
    {M : Bool → Type*} [∀ i, Group (M i)] [∀ i, DecidableEq (M i)]
    {x : M false} {y : M true}
    (htf : IsPowerTorsionFree (M false))
    (hx : x ≠ 1) (hy : y ≠ 1) (hx2 : x ^ 2 ≠ 1)
    (hxm2 : x⁻¹ ^ 2 ≠ 1) (hxi : x⁻¹ ≠ 1) (hyi : y⁻¹ ≠ 1)
    (a b : ℤ) :
    let u : CoprodI.NeWord M true false :=
      ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
        (CoprodI.NeWord.singleton x hx)).append Bool.false_ne_true
          ((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
            (CoprodI.NeWord.singleton x⁻¹ hxi))
    4 * (a.natAbs + b.natAbs) ≤
      FreeProductCyclic.sylLength
        (u.prod ^ (-a) * CoprodI.of (x ^ 2) *
          u.prod ^ b * CoprodI.of (x⁻¹ ^ 2)) := by
  intro u
  let v : CoprodI.NeWord M false true := u.inv
  have huLen : u.toList.length = 4 := by simp [u, CoprodI.NeWord.toList]
  have hvLen : v.toList.length = 4 := by
    simp [v, FreeProductCyclic.toList_length_inv, huLen]
  have huOfNat (k : ℕ) : u.prod ^ (Int.ofNat k) = u.prod ^ k := by
    exact zpow_natCast u.prod k
  have huNegSucc (k : ℕ) : u.prod ^ (Int.negSucc k) = v.prod ^ (k + 1) := by
    simp only [zpow_negSucc, v, CoprodI.NeWord.inv_prod]
    rw [inv_pow]
  have huNegOfNatSucc (k : ℕ) :
      u.prod ^ (-(Int.ofNat (k + 1))) = v.prod ^ (k + 1) := by
    rw [zpow_neg, huOfNat]
    rw [← inv_pow]
    simp only [v, CoprodI.NeWord.inv_prod]
  have huNegNegSucc (k : ℕ) :
      u.prod ^ (-(Int.negSucc k)) = u.prod ^ (k + 1) := by
    convert huOfNat (k + 1) using 1 <;> simp
  cases a with
  | ofNat an =>
      cases an with
      | zero =>
          cases b with
          | ofNat bn =>
              cases bn with
              | zero => simp [FreeProductCyclic.sylLength]
              | succ m =>
                  rw [huOfNat (m + 1)]
                  convert cyclic_npow_conj_sylLength_lower
                    Bool.false_ne_true.symm u (CoprodI.of (x ^ 2)) m using 1 <;>
                    simp [Int.natAbs, huLen, huOfNat, mul_assoc] <;>
                    try omega <;> try { congr 1 <;> group }
          | negSucc m =>
              rw [huNegSucc m]
              convert cyclic_npow_conj_sylLength_lower Bool.false_ne_true
                v (CoprodI.of (x ^ 2)) m using 1 <;>
                simp [Int.natAbs, v, CoprodI.NeWord.inv_prod, hvLen,
                  huOfNat, huNegSucc, mul_assoc] <;> try omega <;>
                try { congr 1 <;> group }
      | succ n =>
          cases b with
          | ofNat bn =>
              cases bn with
              | zero =>
                  rw [huNegOfNatSucc n]
                  rw [huOfNat 0]
                  rw [pow_zero, mul_one]
                  have hpow := FreeProductCyclic.sylLength_npow
                    Bool.false_ne_true v n
                  have hw : v.prod ^ (n + 1) * CoprodI.of (x ^ 2) *
                      CoprodI.of (x⁻¹ ^ 2) = v.prod ^ (n + 1) := by
                    rw [show x⁻¹ ^ 2 = (x ^ 2)⁻¹ by rw [inv_pow], map_inv]
                    group
                  rw [hw, hpow, hvLen]
                  simp only [Int.natAbs]
                  omega
              | succ m =>
                  rw [huNegOfNatSucc n, huOfNat (m + 1)]
                  convert mixed_neg_pos_sylLength htf hx hy hx2 hxm2 hxi hyi
                    n m using 1 <;>
                    simp [Int.natAbs, v, CoprodI.NeWord.inv_prod,
                      huOfNat, huNegSucc] <;> try omega <;>
                    try { congr 1 <;> group }
          | negSucc m =>
              rw [huNegOfNatSucc n, huNegSucc m]
              convert mixed_neg_neg_sylLength htf hx hy hx2 hxm2 hxi hyi
                n m using 1 <;>
                simp [Int.natAbs, v, CoprodI.NeWord.inv_prod,
                  huOfNat, huNegSucc] <;> try omega <;>
                try { congr 1 <;> group }
  | negSucc n =>
      cases b with
      | ofNat bn =>
          cases bn with
          | zero =>
              rw [huNegNegSucc n]
              rw [huOfNat 0]
              rw [pow_zero, mul_one]
              have hpow := FreeProductCyclic.sylLength_npow
                Bool.false_ne_true.symm u n
              have hw : u.prod ^ (n + 1) * CoprodI.of (x ^ 2) *
                  CoprodI.of (x⁻¹ ^ 2) = u.prod ^ (n + 1) := by
                rw [show x⁻¹ ^ 2 = (x ^ 2)⁻¹ by rw [inv_pow], map_inv]
                group
              rw [hw, hpow, huLen]
              simp only [Int.natAbs]
              omega
          | succ m =>
              rw [huNegNegSucc n, huOfNat (m + 1)]
              convert mixed_pos_pos_sylLength htf hx hy hx2 hxm2 hxi hyi
                n m using 1 <;>
                simp [Int.natAbs, huOfNat, huNegSucc] <;>
                try omega <;> try { congr 1 <;> group }
      | negSucc m =>
          rw [huNegNegSucc n, huNegSucc m]
          convert mixed_pos_neg_sylLength htf hx hy hx2 hxm2 hxi hyi
            n m using 1 <;>
            simp [Int.natAbs, v, CoprodI.NeWord.inv_prod, huOfNat,
              huNegSucc] <;> try omega <;> try { congr 1 <;> group }

noncomputable local instance factorDecidableEq (i : Bool) :
    DecidableEq (BinaryCoprodNormalForm.factor Envelope i) := Classical.decEq _

/-- The concrete difference words of the crossing element and its separated
conjugate lose at most one edge relative to their full `4(|a|+|b|)` normal
form. -/
theorem crossing_separated_mixed_sylLength (a b : ℤ) :
    4 * (a.natAbs + b.natAbs) ≤
      FreeProductCyclic.sylLength
        (BinaryCoprodNormalForm.toIndexed Envelope
          (crossingDefect ^ (-a) * separatedCrossing ^ b)) := by
  classical
  let x : Envelope := Classical.choose markedDefect_mem_leftFactor
  have hxEq : Monoid.Coprod.inl x = markedDefect :=
    Classical.choose_spec markedDefect_mem_leftFactor
  have hx : x ≠ 1 := by
    intro hxone
    apply markedDefect_ne_one
    exact hxEq.symm.trans (by simp [hxone])
  let y : BinaryCoprodNormalForm.factor Envelope true :=
    MulEquiv.ulift.symm (Multiplicative.ofAdd (1 : ℤ))
  have hy : y ≠ 1 := by
    intro hyone
    have hone' : Multiplicative.ofAdd (1 : ℤ) = 1 := by
      calc
        Multiplicative.ofAdd (1 : ℤ) = MulEquiv.ulift y := by simp [y]
        _ = MulEquiv.ulift 1 := congrArg MulEquiv.ulift hyone
        _ = 1 := map_one _
    norm_num at hone'
  have hxi : x⁻¹ ≠ 1 := inv_ne_one.mpr hx
  have hyi : y⁻¹ ≠ 1 := inv_ne_one.mpr hy
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    exact hx (envelope_isPowerTorsionFree x 2 (by omega) h)
  have hxm2 : x⁻¹ ^ 2 ≠ 1 := by
    intro h
    exact hxi (envelope_isPowerTorsionFree x⁻¹ 2 (by omega) h)
  let u : CoprodI.NeWord (BinaryCoprodNormalForm.factor Envelope) true false :=
    ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
      (CoprodI.NeWord.singleton x hx)).append Bool.false_ne_true
        ((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
          (CoprodI.NeWord.singleton x⁻¹ hxi))
  have huProd : u.prod =
      BinaryCoprodNormalForm.toIndexed Envelope crossingDefect := by
    rw [crossingDefect, map_mul, map_mul, map_mul, map_inv, map_inv]
    simp only [rightShift, BinaryCoprodNormalForm.toIndexed_inr]
    change u.prod = CoprodI.of y *
      BinaryCoprodNormalForm.toIndexed Envelope markedDefect *
        (CoprodI.of y)⁻¹ *
          (BinaryCoprodNormalForm.toIndexed Envelope markedDefect)⁻¹
    rw [← hxEq, BinaryCoprodNormalForm.toIndexed_inl]
    simp [u, CoprodI.NeWord.append_prod, mul_assoc]
  have h := mixed_zpow_sylLength envelope_isPowerTorsionFree
    hx hy hx2 hxm2 hxi hyi a b
  rw [show separatedCrossing ^ b =
      axisConjugator * crossingDefect ^ b * axisConjugator⁻¹ by
        simp only [separatedCrossing, conj_zpow]]
  rw [map_mul, map_mul, map_mul, map_inv, map_zpow, map_zpow]
  rw [← huProd]
  let xLeft : BinaryCoprodNormalForm.factor Envelope false := x
  let ofLeft : BinaryCoprodNormalForm.factor Envelope false →*
      CoprodI (BinaryCoprodNormalForm.factor Envelope) := CoprodI.of
  have haxis : BinaryCoprodNormalForm.toIndexed Envelope axisConjugator =
      ofLeft (xLeft ^ 2) := by
    simp only [axisConjugator, map_pow, ← hxEq,
      BinaryCoprodNormalForm.toIndexed_inl]
    simpa [ofLeft, xLeft] using (map_pow ofLeft xLeft 2).symm
  rw [haxis]
  simpa [u, CoprodI.NeWord.append_prod, ofLeft, xLeft, map_pow,
    mul_assoc] using h

theorem crossing_separated_mixed_displacement_lower (a b : ℤ) :
    (4 * (a.natAbs + b.natAbs) : ℝ) - 1 ≤
      dist (BassSerreFreeProduct.baseLeft Envelope :
          BassSerreHullGeometry.PathVertex Envelope)
        ((crossingDefect ^ (-a) * separatedCrossing ^ b) •
      (BassSerreFreeProduct.baseLeft Envelope :
            BassSerreHullGeometry.PathVertex Envelope)) := by
  classical
  let L := 4 * (a.natAbs + b.natAbs)
  have hlen : L ≤ FreeProductCyclic.sylLength
      (BinaryCoprodNormalForm.toIndexed Envelope
        (crossingDefect ^ (-a) * separatedCrossing ^ b)) :=
    crossing_separated_mixed_sylLength a b
  have hdisp := BassSerreFreeProduct.sylLength_toIndexed_sub_one_le_graph_dist
    Envelope (crossingDefect ^ (-a) * separatedCrossing ^ b)
  by_cases hL0 : L = 0
  · have hreal : (4 * (a.natAbs + b.natAbs) : ℝ) = 0 := by
      exact_mod_cast hL0
    have hnon : 0 ≤ dist
        (BassSerreFreeProduct.baseLeft Envelope :
          BassSerreHullGeometry.PathVertex Envelope)
        ((crossingDefect ^ (-a) * separatedCrossing ^ b) •
          (BassSerreFreeProduct.baseLeft Envelope :
            BassSerreHullGeometry.PathVertex Envelope)) := dist_nonneg
    linarith
  · have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hL0
    have hnat : L - 1 ≤ (BassSerreFreeProduct.graph Envelope).dist
        (BassSerreFreeProduct.baseLeft Envelope)
        ((crossingDefect ^ (-a) * separatedCrossing ^ b) •
          BassSerreFreeProduct.baseLeft Envelope) :=
      (Nat.sub_le_sub_right hlen 1).trans hdisp
    have hcast : (L : ℝ) - 1 ≤
        dist (BassSerreFreeProduct.baseLeft Envelope :
          BassSerreHullGeometry.PathVertex Envelope)
        ((crossingDefect ^ (-a) * separatedCrossing ^ b) •
          (BassSerreFreeProduct.baseLeft Envelope :
            BassSerreHullGeometry.PathVertex Envelope)) := by
      rw [BassSerreHullGeometry.pathVertex_dist]
      rw [show (L : ℝ) - 1 = ((L - 1 : ℕ) : ℝ) by
        rw [Nat.cast_sub hL]; norm_num]
      exact_mod_cast hnat
    simpa [L, Nat.cast_mul, Nat.cast_add] using hcast

theorem separatedCrossing_zpow_displacement_eq (b : ℤ) :
    dist (BassSerreFreeProduct.baseLeft Envelope :
        BassSerreHullGeometry.PathVertex Envelope)
      ((separatedCrossing ^ b) •
        (BassSerreFreeProduct.baseLeft Envelope :
          BassSerreHullGeometry.PathVertex Envelope)) =
    dist (BassSerreFreeProduct.baseLeft Envelope :
        BassSerreHullGeometry.PathVertex Envelope)
      ((crossingDefect ^ b) •
        (BassSerreFreeProduct.baseLeft Envelope :
          BassSerreHullGeometry.PathVertex Envelope)) := by
  let o : BassSerreHullGeometry.PathVertex Envelope :=
    BassSerreFreeProduct.baseLeft Envelope
  have hc : axisConjugator • o = o := axisConjugator_smul_baseLeft
  have hci : axisConjugator⁻¹ • o = o := by
    calc
      axisConjugator⁻¹ • o = axisConjugator⁻¹ • (axisConjugator • o) :=
        congrArg (axisConjugator⁻¹ • ·) hc.symm
      _ = o := inv_smul_smul axisConjugator o
  rw [show separatedCrossing ^ b =
      axisConjugator * crossingDefect ^ b * axisConjugator⁻¹ by
        simp only [separatedCrossing, conj_zpow]]
  calc
    dist o ((axisConjugator * crossingDefect ^ b * axisConjugator⁻¹) • o) =
        dist o (axisConjugator • ((crossingDefect ^ b) • o)) := by
          simp only [mul_smul, hci]
    _ = dist (axisConjugator • o)
        (axisConjugator • ((crossingDefect ^ b) • o)) := by rw [hc]
    _ = dist o ((crossingDefect ^ b) • o) := by
      rw [bassSerre_isometric axisConjugator]

theorem crossing_separated_independent :
    HullGeometry.Independent crossingDefect separatedCrossing
      (BassSerreFreeProduct.baseLeft Envelope :
        BassSerreHullGeometry.PathVertex Envelope) := by
  apply HullGeometry.independent_of_difference_lower bassSerre_isometric 1
  intro a b
  have hga := crossingDefect_zpow_displacement_le a
  have hhb := crossingDefect_zpow_displacement_le b
  rw [← separatedCrossing_zpow_displacement_eq b] at hhb
  have hmix := crossing_separated_mixed_displacement_lower a b
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hga hhb hmix ⊢
  linarith

/-- The amplified normal defect acts non-elementarily on its Bass--Serre
tree, witnessed by the crossing element and its explicit separated
conjugate. -/
theorem amplifiedDefect_actsNonElementarily :
    HullGeometry.ActsNonElementarily amplifiedDefectData.core.defectNormal
      (BassSerreFreeProduct.baseLeft Envelope :
        BassSerreHullGeometry.PathVertex Envelope) := by
  exact HullGeometry.actsNonElementarily_of_normal_conjugate
    bassSerre_isometric crossingDefect_mem crossingDefect_isLoxodromic
    crossing_separated_independent

end

end GroupApproximation.LiteralAffineFreeProductBassSerre

