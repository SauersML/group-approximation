import GroupApproximation.GGT.HullYiOrientationAggregation
import GroupApproximation.GGT.HullYiCyclicProductProducer
import GroupApproximation.GGT.HullYiCorollary612Family

/-!
# Selecting Hull's matched cyclic-product family

This module proves the combined product-selection interface from
`DGOLemma421b`.  The orientation-pure radical detector is first reduced to an
exact pairwise triple.  DGO Lemma 4.21(b)'s comparison and self-match depths
are then chosen together by the combined producer.

The first two centralizer powers are chosen beyond that common depth and the
fixed triangle-separation radius, so their product is outside the third
elementary closure.  DGO Corollary 6.12 supplies a loxodromy threshold for the
last factor.  Successively separated powers of that last factor give the
required number of distinct candidates, all beyond both thresholds.  The
combined producer immediately packages the products with their consecutive
component matches.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-- **Hull's combined cyclic-product selection from DGO Lemma 4.21(b).** -/
theorem yiOrientationPureProductFamilySelection_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) :
    YiOrientationPureProductFamilySelection.{u} := by
  classical
  intro G _ A T hT F
  obtain ⟨detector, exponent, hdetectorT, hdetectorLox, hdetectorNc,
      hexponent, hcentral, hinter⟩ :=
    exists_orientationPure_triple_trivial_intersection_of_dgoLemma421b
      h421b A hT
  let core : Fin 3 → G := fun i ↦ detector i ^ (exponent i : ℤ)
  have hcoreLox : ∀ i,
      IsLoxodromic (core i) (Cayley.base A.alphabet) := by
    intro i
    exact isLoxodromic_zpow (isIsometricAction_cayley A.alphabet)
      (hdetectorLox i)
      (Int.ofNat_ne_zero.mpr (ne_of_gt (hexponent i)))
  let D : RelGenSet G (Fin 3) :=
    coneOffFamily A.alphabet (fun i ↦ elementaryClosure (detector i))
  have hemb : D.IsHyperbolicallyEmbedded :=
    isHyperbolicallyEmbedded_elementaryClosure_family
      A detector hdetectorNc hdetectorLox
  have hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet) :=
    hemb.hyperbolic
  obtain ⟨Cproduct, hproduct⟩ :=
    exists_depth_preparedProductFamily_of_pairwiseDetector
      h421b A (T := T) (k := 2) (by omega) detector hdetectorT
        hdetectorLox hdetectorNc exponent hexponent hcentral hinter
  obtain ⟨deltaD, hdeltaD⟩ := hhyp
  have hfour : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier ⌈deltaD⌉₊ :=
    isFourPointHyperbolic_of_isHyperbolicSpace_cayley D.alphabet hdeltaD
  obtain ⟨Rsep, hsep⟩ := GGT.HullYi.exists_radius_notMem_fam_mul
    D A.alphabet.symmetricGenerating.inv_mem hfour
  let depthA := max 1 (max Cproduct Rsep)
  have hCproductDepthA : Cproduct ≤ depthA := by
    dsimp [depthA]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
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
    apply (elementaryClosure (detector 0)).pow_mem
    exact Subgroup.zpow_mem _ (self_mem_elementaryClosure (detector 0)) _
  have haDeepProduct : a ∉ D.relBall 0 Cproduct :=
    notMem_relBall_of_le hCproductDepthA haDeep
  have haDeepSep : a ∉ D.relBall 0 Rsep :=
    notMem_relBall_of_le hRsepDepthA haDeep
  have haDeepOne : a ∉ D.relBall 0 1 :=
    notMem_relBall_of_le (le_max_left _ _) haDeep
  let depthB := max Cproduct 1
  have hcore1inj : Function.Injective (fun n : ℕ ↦ core 1 ^ n) :=
    injective_pow_of_not_isOfFinOrder
      (not_isOfFinOrder_of_isLoxodromic (hcoreLox 1))
  obtain ⟨mb, hmb, hbDeep, -⟩ :=
    exists_deep_pow hcore1inj (hemb.locallyFinite 1 depthB) 1
  let b : G := core 1 ^ mb
  have hbMem : b ∈ D.fam 1 := by
    dsimp [b, D]
    apply (elementaryClosure (detector 1)).pow_mem
    exact Subgroup.zpow_mem _ (self_mem_elementaryClosure (detector 1)) _
  have hbDeepProduct : b ∉ D.relBall 1 Cproduct :=
    notMem_relBall_of_le (le_max_left _ _) hbDeep
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
  let prefixLetters : Fin 2 → G := ![a, b]
  let stem : G := a * b
  let word : List (RelLetter G (Fin 3)) :=
    indexedPeripheralWord (fun i : Fin 2 ↦ i.castSucc) prefixLetters
  have hwordLetter : ∀ c ∈ word, D.IsLetter c := by
    apply isLetter_indexedPeripheralWord D
    intro i
    fin_cases i
    · exact haMem
    · exact hbMem
  have hwordValue : RelLetter.listVal word = stem := by
    rw [show word = indexedPeripheralWord
      (fun i : Fin 2 ↦ i.castSucc) prefixLetters from rfl,
      listVal_indexedPeripheralWord]
    simp [stem, prefixLetters, orderedFinProduct]
  have hwordNoLast : ∀ c ∈ word, ¬ c.IsCompOf (2 : Fin 3) := by
    intro c hc
    obtain ⟨i, rfl⟩ := exists_eq_comp_of_mem_indexedPeripheralWord
      (fun i : Fin 2 ↦ i.castSucc) prefixLetters hc
    intro hi
    have hval := congrArg Fin.val hi
    fin_cases i <;> simp at hval
  obtain ⟨Clox, hlox⟩ := exists_threshold_isLoxodromic_mul_of_symm
    D 2 A.alphabet.symmetricGenerating.inv_mem ⟨deltaD, hdeltaD⟩ habNot
      word hwordLetter hwordValue hwordNoLast
  have hbase : IsSymmetricGeneratingSet D.base := by
    simpa [D] using A.alphabet.symmetricGenerating
  let Clast := max Cproduct Clox
  have hcore2inj : Function.Injective (fun n : ℕ ↦ core 2 ^ n) :=
    injective_pow_of_not_isOfFinOrder
      (not_isOfFinOrder_of_isLoxodromic (hcoreLox 2))
  obtain ⟨lastPower, hlastPow, hlastDeep, -, hlastSep⟩ :=
    exists_successivelySeparatedPowers D 2 hbase
      (hemb.locallyFinite 2) hcore2inj ∅ Set.finite_empty Clast 0
        (F.card + 2)
  choose lastMultiplier hlastMultiplierPos hlastPowerEq using hlastPow
  have hlastMem : ∀ j, lastPower j ∈ D.fam 2 := by
    intro j
    rw [hlastPowerEq j]
    dsimp [D]
    exact (elementaryClosure (detector 2)).pow_mem
      (Subgroup.zpow_mem _ (self_mem_elementaryClosure (detector 2)) _)
      (lastMultiplier j)
  have hlastDeepProduct : ∀ j,
      lastPower j ∉ D.relBall 2 Cproduct := by
    intro j
    exact notMem_relBall_of_le (le_max_left _ _) (hlastDeep j).1
  have hlastDeepLox : ∀ j, lastPower j ∉ D.relBall 2 Clox := by
    intro j
    exact notMem_relBall_of_le (le_max_right _ _) (hlastDeep j).1
  have hlastLox : ∀ j,
      IsLoxodromic (stem * lastPower j) (Cayley.base D.alphabet) := by
    intro j
    exact hlox (lastPower j) (hlastMem j) (hlastDeepLox j)
  have hlastMultiplierNe : ∀ i j, i ≠ j →
      lastMultiplier i ≠ lastMultiplier j := by
    intro i j hij heq
    have hpowerEq : lastPower i = lastPower j := by
      rw [hlastPowerEq i, hlastPowerEq j, heq]
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · apply (hlastSep i j hijlt).1
      rw [← hpowerEq]
      exact mem_relBall_of_wordNorm_le hbase (hlastMem i) le_rfl
    · apply (hlastSep j i hjilt).1
      rw [hpowerEq]
      exact mem_relBall_of_wordNorm_le hbase (hlastMem j) le_rfl
  let multiplier : Fin (F.card + 2) → Fin 3 → ℤ := fun j ↦
    ![(ma : ℤ), (mb : ℤ), (lastMultiplier j : ℤ)]
  have hmultiplierNe : ∀ j i, multiplier j i ≠ 0 := by
    intro j i
    refine Fin.lastCases ?_ ?_ i
    · exact Int.ofNat_ne_zero.mpr
        (ne_of_gt (hlastMultiplierPos j))
    · intro z
      fin_cases z
      · exact Int.ofNat_ne_zero.mpr (ne_of_gt hma)
      · exact Int.ofNat_ne_zero.mpr (ne_of_gt hmb)
  have hcommon : ∀ j l (i : Fin 2),
      multiplier j i.castSucc = multiplier l i.castSucc := by
    intro j l i
    fin_cases i <;> rfl
  have hdistinct : ∀ j l, j ≠ l →
      multiplier j (Fin.last 2) ≠ multiplier l (Fin.last 2) := by
    intro j l hjl
    simpa [multiplier] using hlastMultiplierNe j l hjl
  have hdeep : ∀ j i,
      ((detector i ^ (exponent i : ℤ)) ^ multiplier j i) ∉
        D.relBall i Cproduct := by
    intro j i
    fin_cases i
    · simpa [multiplier, core, a, zpow_natCast] using haDeepProduct
    · simpa [multiplier, core, b, zpow_natCast] using hbDeepProduct
    · simpa [multiplier, core, zpow_natCast, hlastPowerEq j] using
        hlastDeepProduct j
  have hproductLox : ∀ j, IsLoxodromic
      (orderedFinProduct (fun i ↦
        (detector i ^ (exponent i : ℤ)) ^ multiplier j i))
      (Cayley.base D.alphabet) := by
    intro j
    have heq :
        orderedFinProduct (fun i ↦
          (detector i ^ (exponent i : ℤ)) ^ multiplier j i) =
          stem * lastPower j := by
      simp [multiplier, core, a, b, stem, orderedFinProduct,
        zpow_natCast, hlastPowerEq j]
      group
    rw [heq]
    exact hlastLox j
  exact hproduct multiplier hmultiplierNe hcommon hdistinct hdeep hproductLox

end HullSC
end GroupApproximation
