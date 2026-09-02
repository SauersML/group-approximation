import GroupApproximation.GGT.HullYiOrientationDetector
import GroupApproximation.GGT.HullYiCyclicProductMatch
import GroupApproximation.GGT.HullYiMatchedProductRigidity

/-!
# Orientation-pure products from a prescribed detector triple

Hull's Lemma 5.4 constructs orientation-pure products from three pairwise
non-commensurable loxodromics.  This module keeps the initial triple explicit
and chooses every product letter as a multiple of its centralizer exponent.
Besides loxodromy, orientation purity, and pairwise non-commensurability, the
construction shows that every finite-order element of a product elementary
closure belongs to all three detector elementary closures.

The last clause is the finite part of Hull's `E(h) = ⟨h⟩ × K` calculation.  It
allows a detector which excludes one element of the finite radical candidate
to be replaced by arbitrarily many fresh orientation-pure commensurability
classes without losing that exclusion.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-- **Hull Lemma 5.4 from a prescribed orientation-pure triple.**

All three detector powers are chosen after the orientation, self-match, and
fixed-side separation thresholds.  The final powers in the third peripheral
factor are then chosen by the finite-family form of DGO Corollary 6.12. -/
theorem exists_orientationPure_products_of_triple_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {S : Subgroup G} (q : Fin 3 → G) (r : Fin 3 → ℕ)
    (hqS : ∀ i, q i ∈ S)
    (hqlox : ∀ i, IsLoxodromic (q i) (Cayley.base A.alphabet))
    (hqnc : PairwiseNonCommensurable q)
    (hr : ∀ i, 0 < r i)
    (hcentral : ∀ i, (elementaryClosure (q i) : Set G) =
      {x : G | Commute x (q i ^ (r i : ℤ))})
    (N : ℕ) :
    ∃ (f : Fin N → G) (s : Fin N → ℕ),
      (∀ j, f j ∈ S) ∧
      (∀ j, IsLoxodromic (f j) (Cayley.base A.alphabet)) ∧
      PairwiseNonCommensurable f ∧
      (∀ j, 0 < s j) ∧
      (∀ j, (elementaryClosure (f j) : Set G) =
        {x : G | Commute x (f j ^ (s j : ℤ))}) ∧
      ∀ j (x : G), IsOfFinOrder x → x ∈ elementaryClosure (f j) →
        ∀ i, x ∈ elementaryClosure (q i) := by
  let core : Fin 3 → G := fun i ↦ q i ^ (r i : ℤ)
  have hcoreLox : ∀ i,
      IsLoxodromic (core i) (Cayley.base A.alphabet) := by
    intro i
    exact isLoxodromic_zpow (isIsometricAction_cayley A.alphabet)
      (hqlox i) (Int.ofNat_ne_zero.mpr (ne_of_gt (hr i)))
  let D : RelGenSet G (Fin 3) :=
    coneOffFamily A.alphabet (fun i ↦ elementaryClosure (q i))
  have hemb : D.IsHyperbolicallyEmbedded :=
    isHyperbolicallyEmbedded_elementaryClosure_family A q hqnc hqlox
  have hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet) :=
    hemb.hyperbolic
  obtain ⟨Corient, horient⟩ :=
    exists_depth_hasPositivePowerNormalizer_cyclicProduct_of_dgoLemma421b
      h421b A.alphabet q (k := 2) (by omega) hhyp
  obtain ⟨Cmatch, hmatch⟩ :=
    exists_depth_hasConsecutiveComponentMatchData_of_dgoLemma421b
      h421b A.alphabet q (k := 2) (by omega) hhyp
  obtain ⟨deltaD, hdeltaD⟩ := hhyp
  have hfour : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier ⌈deltaD⌉₊ :=
    isFourPointHyperbolic_of_isHyperbolicSpace_cayley D.alphabet hdeltaD
  obtain ⟨Rsep, hsep⟩ := GGT.HullYi.exists_radius_notMem_fam_mul
    D A.alphabet.symmetricGenerating.inv_mem hfour
  let Call := max Corient Cmatch
  let depthA := max 1 (max Call Rsep)
  have hCorientDepthA : Corient ≤ depthA := by
    dsimp [depthA, Call]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hCmatchDepthA : Cmatch ≤ depthA := by
    dsimp [depthA, Call]
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hRsepDepthA : Rsep ≤ depthA := by
    dsimp [depthA]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hcore0inj : Function.Injective (fun n : ℕ ↦ core 0 ^ n) :=
    injective_pow_of_not_isOfFinOrder
      (not_isOfFinOrder_of_isLoxodromic (hcoreLox 0))
  obtain ⟨ma, hma, haDeep, -⟩ :=
    exists_deep_pow hcore0inj (hemb.locallyFinite 0 depthA) 1
  let a : G := core 0 ^ ma
  have haMem : a ∈ D.fam 0 := by
    dsimp [a, D]
    apply (elementaryClosure (q 0)).pow_mem
    exact Subgroup.zpow_mem _ (self_mem_elementaryClosure (q 0)) _
  have haS : a ∈ S := by
    dsimp [a, core]
    exact S.pow_mem (S.zpow_mem (hqS 0) _) ma
  have haDeepOrient : a ∉ D.relBall 0 Corient :=
    notMem_relBall_of_le hCorientDepthA haDeep
  have haDeepMatch : a ∉ D.relBall 0 Cmatch :=
    notMem_relBall_of_le hCmatchDepthA haDeep
  have haDeepSep : a ∉ D.relBall 0 Rsep :=
    notMem_relBall_of_le hRsepDepthA haDeep
  have haDeepOne : a ∉ D.relBall 0 1 :=
    notMem_relBall_of_le (le_max_left _ _) haDeep
  let depthB := max Call 1
  have hCorientDepthB : Corient ≤ depthB := by
    dsimp [depthB, Call]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCmatchDepthB : Cmatch ≤ depthB := by
    dsimp [depthB, Call]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hcore1inj : Function.Injective (fun n : ℕ ↦ core 1 ^ n) :=
    injective_pow_of_not_isOfFinOrder
      (not_isOfFinOrder_of_isLoxodromic (hcoreLox 1))
  obtain ⟨mb, hmb, hbDeep, -⟩ :=
    exists_deep_pow hcore1inj (hemb.locallyFinite 1 depthB) 1
  let b : G := core 1 ^ mb
  have hbMem : b ∈ D.fam 1 := by
    dsimp [b, D]
    apply (elementaryClosure (q 1)).pow_mem
    exact Subgroup.zpow_mem _ (self_mem_elementaryClosure (q 1)) _
  have hbS : b ∈ S := by
    dsimp [b, core]
    exact S.pow_mem (S.zpow_mem (hqS 1) _) mb
  have hbDeepOrient : b ∉ D.relBall 1 Corient :=
    notMem_relBall_of_le hCorientDepthB hbDeep
  have hbDeepMatch : b ∉ D.relBall 1 Cmatch :=
    notMem_relBall_of_le hCmatchDepthB hbDeep
  have hbDeepOne : b ∉ D.relBall 1 1 :=
    notMem_relBall_of_le (le_max_right _ _) hbDeep
  have hb1 : b ≠ 1 := by
    intro hb1
    apply hbDeepOne
    rw [hb1]
    exact one_mem_relBall D 1 1
  have hab1 : a * b ≠ 1 := by
    intro hab1
    have hab : a = b⁻¹ := by
      calc
        a = a * b * b⁻¹ := by group
        _ = b⁻¹ := by rw [hab1, one_mul]
    apply haDeepOne
    apply mem_relBall_one_of_mem_fam_ne (D := D) (lam := 0) (mu := 1)
      (by decide)
    rw [hab]
    exact inv_mem hbMem
    exact haMem
  have habNot : a * b ∉ D.fam 2 :=
    hsep 0 1 2 a b (by decide) (by decide) haMem hbMem hb1 hab1 haDeepSep
  let extra : Set G := D.relBall 2 Call
  have hcore2E : elementaryClosure (core 2) = elementaryClosure (q 2) := by
    dsimp [core]
    exact elementaryClosure_zpow (q 2)
      (Int.ofNat_ne_zero.mpr (ne_of_gt (hr 2)))
  obtain ⟨c, hcPow, hcExtra, hflox, hfnc⟩ :=
    exists_pairwiseNonCommensurable_mul_powers_of_dgoLemma421b
      h421b A (hcoreLox 2) (by rwa [hcore2E])
        extra (hemb.locallyFinite 2 Call) N
  let f : Fin N → G := fun j ↦ a * b * c j
  have hflox' : ∀ j, IsLoxodromic (f j) (Cayley.base A.alphabet) := by
    intro j
    simpa [f, mul_assoc] using hflox j
  have hfnc' : PairwiseNonCommensurable f := by
    simpa [f, mul_assoc] using hfnc
  have hcMem : ∀ j, c j ∈ D.fam 2 := by
    intro j
    obtain ⟨m, -, hm⟩ := hcPow j
    rw [hm]
    dsimp [D]
    rw [← hcore2E]
    exact (elementaryClosure (core 2)).pow_mem
      (self_mem_elementaryClosure (core 2)) m
  have hcS : ∀ j, c j ∈ S := by
    intro j
    obtain ⟨m, -, hm⟩ := hcPow j
    rw [hm]
    dsimp [core]
    exact S.pow_mem (S.zpow_mem (hqS 2) _) m
  have hcDeepOrient : ∀ j, c j ∉ D.relBall 2 Corient := by
    intro j
    exact notMem_relBall_of_le (le_trans (le_max_left _ _) le_rfl)
      (hcExtra j).1
  have hcDeepMatch : ∀ j, c j ∉ D.relBall 2 Cmatch := by
    intro j
    exact notMem_relBall_of_le (le_trans (le_max_right _ _) le_rfl)
      (hcExtra j).1
  have hcentralA : (elementaryClosure (q 0) : Set G) =
      {x : G | Commute x a} := by
    dsimp [a, core]
    simpa only [zpow_natCast] using
      elementaryClosure_eq_centralizer_zpow_mul
        (Int.ofNat_ne_zero.mpr (ne_of_gt (hr 0))) (hcentral 0)
        (Int.ofNat_ne_zero.mpr (ne_of_gt hma))
  have hcentralB : (elementaryClosure (q 1) : Set G) =
      {x : G | Commute x b} := by
    dsimp [b, core]
    simpa only [zpow_natCast] using
      elementaryClosure_eq_centralizer_zpow_mul
        (Int.ofNat_ne_zero.mpr (ne_of_gt (hr 1))) (hcentral 1)
        (Int.ofNat_ne_zero.mpr (ne_of_gt hmb))
  have hcentralC : ∀ j, (elementaryClosure (q 2) : Set G) =
      {x : G | Commute x (c j)} := by
    intro j
    obtain ⟨m, hm, hcm⟩ := hcPow j
    rw [hcm]
    dsimp [core]
    simpa only [zpow_natCast] using
      elementaryClosure_eq_centralizer_zpow_mul
        (Int.ofNat_ne_zero.mpr (ne_of_gt (hr 2))) (hcentral 2)
        (Int.ofNat_ne_zero.mpr (ne_of_gt hm))
  let I : Subgroup G := elementaryClosure (q 0) ⊓ elementaryClosure (q 1)
  have hIfin : (I : Set G).Finite := by
    have hind : Independent (q 0) (q 1) (Cayley.base A.alphabet) := by
      apply ElementaryMorse.independentOfNoCommonZpow_cayley A
        (q 0) (q 1) (hqlox 0) (hqlox 1)
      intro p z hp hz heq
      exact hqnc 0 1 (by decide) p z hp hz 1 (by simpa using heq)
    by_contra hinf
    exact not_infinite_le_inf_elementaryClosure
      (isIsometricAction_cayley A.alphabet)
      (elementaryClosureVirtuallyCyclic_hullGeneratingSet A)
      (hqlox 0) (hqlox 1) hind inf_le_left inf_le_right hinf
  have hinterFinite : ∀ x : G,
      (∀ i, x ∈ elementaryClosure (q i)) → IsOfFinOrder x := by
    intro x hx
    let y : I := ⟨x, hx 0, hx 1⟩
    letI : Finite I := hIfin.to_subtype
    exact Submonoid.isOfFinOrder_coe.mpr (isOfFinOrder_of_finite y)
  have hnormal : ∀ j, HasPositivePowerNormalizer (f j) := by
    intro j
    let letters : Fin 3 → G := yiTriple a b (c j)
    have hmem : ∀ i, letters i ∈ elementaryClosure (q i) := by
      intro i
      fin_cases i
      · exact haMem
      · exact hbMem
      · exact hcMem j
    have hdeep : ∀ i, letters i ∉ D.relBall i Corient := by
      intro i
      fin_cases i
      · exact haDeepOrient
      · exact hbDeepOrient
      · exact hcDeepOrient j
    have hprod : orderedFinProduct letters = f j := by
      simp [letters, f, yiTriple, orderedFinProduct, mul_assoc]
    rw [← hprod]
    exact horient letters hmem hdeep (by simpa [hprod] using hflox' j)
  have hfiniteIn : ∀ j (x : G), IsOfFinOrder x →
      x ∈ elementaryClosure (f j) →
      ∀ i, x ∈ elementaryClosure (q i) := by
    intro j x hxfinite hxE
    let letters : Fin 3 → G := yiTriple a b (c j)
    have hmem : ∀ i, letters i ∈ elementaryClosure (q i) := by
      intro i
      fin_cases i
      · exact haMem
      · exact hbMem
      · exact hcMem j
    have hdeep : ∀ i, letters i ∉ D.relBall i Cmatch := by
      intro i
      fin_cases i
      · exact haDeepMatch
      · exact hbDeepMatch
      · exact hcDeepMatch j
    have hprod : orderedFinProduct letters = f j := by
      simp [letters, f, yiTriple, orderedFinProduct, mul_assoc]
    have hmatchX := hmatch letters hmem hdeep
      (by simpa [hprod] using hflox' j) x (by simpa [hprod] using hxE)
    have hcentralLetters : ∀ i : Fin 3, ∀ y : G,
        y ∈ elementaryClosure (q i) → Commute y (letters i) := by
      intro i y hy
      fin_cases i
      · exact Set.mem_setOf_eq.mp ((Set.ext_iff.mp hcentralA y).mp hy)
      · exact Set.mem_setOf_eq.mp ((Set.ext_iff.mp hcentralB y).mp hy)
      · exact Set.mem_setOf_eq.mp ((Set.ext_iff.mp (hcentralC j) y).mp hy)
    have hinterComm : ∀ y : G,
        (∀ i, y ∈ elementaryClosure (q i)) → Commute y (f j) := by
      intro y hy
      have hya := hcentralLetters 0 y (hy 0)
      have hyb := hcentralLetters 1 y (hy 1)
      have hyc := hcentralLetters 2 y (hy 2)
      simpa [f, letters, yiTriple, mul_assoc] using
        (hya.mul_right hyb).mul_right hyc
    apply finiteOrder_mem_detectorIntersection_of_matchedProduct
      (fun i ↦ elementaryClosure (q i)) letters (f j)
      hcentralLetters hinterFinite hinterComm
      (not_isOfFinOrder_of_isLoxodromic (hflox' j)) hxfinite
    simpa [hprod] using hmatchX
  have hcentralF : ∀ j, ∃ s : ℕ, 0 < s ∧
      (elementaryClosure (f j) : Set G) =
        {x : G | Commute x (f j ^ (s : ℤ))} := by
    intro j
    exact exists_elementaryClosure_eq_centralizer_pow_of_hasPositivePowerNormalizer
      A (hflox' j) (hnormal j)
  choose s hs hcentralS using hcentralF
  refine ⟨f, s, ?_, hflox', hfnc', hs, hcentralS, hfiniteIn⟩
  intro j
  exact S.mul_mem (S.mul_mem haS hbS) (hcS j)

end HullSC
end GroupApproximation
