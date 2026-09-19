import GroupApproximation.GGT.HullYiCyclicProductAssembly
import GroupApproximation.GGT.HullYiCyclicProductMatch
import GroupApproximation.GGT.HullYiCyclicProductNonCommensurable
import GroupApproximation.GGT.HullYiElementaryClosureFamily

/-!
# The combined producer for Hull's cyclic products

This module packages the outputs obtained after the detecting family and its
deep powers have been chosen.  The two DGO Lemma 4.21(b) thresholds are fixed
first.  A single maximum depth then supplies both the consecutive self-match
and the comparison of distinct candidate products.

The first lemmas isolate the terminal-ratio argument in Hull's proof.  A
nonzero power of one member of a pairwise non-commensurable loxodromic family
cannot lie in the elementary closure of another member.  Applied to distinct
last multipliers, this is the terminal hypothesis of the common-prefix match.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

variable {G : Type u} [Group G]

/-! ## Powers of distinct detector classes -/

/-- A nonzero power of one detector cannot lie in the elementary closure of a
pairwise non-commensurable detector.  The finite-transversal theorem turns
such membership into an equality of nonzero powers. -/
theorem zpow_not_mem_elementaryClosure_of_nonCommensurable
    (A : HullGeneratingSet G) {a b : G}
    (ha : IsLoxodromic a (Cayley.base A.alphabet))
    (hb : IsLoxodromic b (Cayley.base A.alphabet))
    (hnc : ∀ (p q : ℤ), p ≠ 0 → q ≠ 0 → ∀ t : G,
      t * a ^ p * t⁻¹ ≠ b ^ q) {e : ℤ} (he : e ≠ 0) :
    b ^ e ∉ elementaryClosure a := by
  intro hmem
  let K : Subgroup G := Subgroup.zpowers (b ^ e)
  have hKE : K ≤ elementaryClosure a := by
    apply Subgroup.zpowers_le.mpr
    exact hmem
  have hbeLox : IsLoxodromic (b ^ e) (Cayley.base A.alphabet) :=
    isLoxodromic_zpow (isIsometricAction_cayley A.alphabet) hb he
  have hKinf : (K : Set G).Infinite := infinite_coe_zpowers hbeLox
  obtain ⟨p, hp, hpK⟩ := exists_nonzero_zpow_mem_of_finiteTransversal
    (elementaryClosureFiniteTransversal_hullGeneratingSet A ha) K hKE hKinf
  obtain ⟨q, hqeq⟩ := Subgroup.mem_zpowers_iff.mp hpK
  have hq : q ≠ 0 := by
    intro hq0
    subst q
    simp only [zpow_zero] at hqeq
    exact zpow_ne_one_of_isLoxodromic ha hp hqeq.symm
  have heq : a ^ p = b ^ (e * q) := by
    calc
      a ^ p = (b ^ e) ^ q := hqeq.symm
      _ = b ^ (e * q) := by rw [zpow_mul]
  exact hnc p (e * q) hp (mul_ne_zero he hq) 1 (by simpa using heq)

/-- Distinct multipliers of the last detector give the terminal-ratio
separation used by the common-prefix comparison. -/
theorem terminalRatio_notMem_first_of_nonCommensurable
    (A : HullGeneratingSet G) {k : ℕ} (hk : 0 < k)
    (f : Fin (k + 1) → G)
    (hlox : ∀ i, IsLoxodromic (f i) (Cayley.base A.alphabet))
    (hnc : PairwiseNonCommensurable f) (r : Fin (k + 1) → ℕ)
    (hr : ∀ i, 0 < r i) {m n : ℤ} (hmn : m ≠ n) :
    (((f (Fin.last k) ^ (r (Fin.last k) : ℤ)) ^ m)⁻¹ *
        (f (Fin.last k) ^ (r (Fin.last k) : ℤ)) ^ n) ∉
      elementaryClosure (f 0) := by
  have hindex : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro hbad
    have hval := congrArg Fin.val hbad
    simp only [Fin.val_zero, Fin.val_last] at hval
    omega
  have hratio :
      ((f (Fin.last k) ^ (r (Fin.last k) : ℤ)) ^ m)⁻¹ *
          (f (Fin.last k) ^ (r (Fin.last k) : ℤ)) ^ n =
        f (Fin.last k) ^ ((r (Fin.last k) : ℤ) * (n - m)) := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    ring
  rw [hratio]
  apply zpow_not_mem_elementaryClosure_of_nonCommensurable A
    (hlox 0) (hlox (Fin.last k))
  · intro p q hp hq t
    exact hnc 0 (Fin.last k) hindex p q hp hq t
  · exact mul_ne_zero (Int.ofNat_ne_zero.mpr (ne_of_gt (hr (Fin.last k))))
      (sub_ne_zero.mpr hmn.symm)

/-! ## One depth for comparison and self-matching -/

/-- The complete product family once deep multipliers have been selected.

The returned depth is chosen before `multiplier`.  The common-prefix and
distinct-tail clauses are the literal combinatorics of Hull's candidates.  The
product loxodromy is requested in the cone-off alphabet and transferred back
to the prescribed alphabet for the DGO comparison theorem. -/
theorem exists_depth_preparedProductFamily_of_pairwiseDetector
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {T : Subgroup G} {k : ℕ} (hk : 2 ≤ k)
    (detector : Fin (k + 1) → G)
    (hdetectorT : ∀ i, detector i ∈ T)
    (hdetectorLox : ∀ i,
      IsLoxodromic (detector i) (Cayley.base A.alphabet))
    (hdetectorNc : PairwiseNonCommensurable detector)
    (exponent : Fin (k + 1) → ℕ) (hexponent : ∀ i, 0 < exponent i)
    (hcentral : ∀ i,
      (elementaryClosure (detector i) : Set G) =
        {x : G | Commute x (detector i ^ (exponent i : ℤ))})
    (hinter : ∀ x : G,
      (∀ i, x ∈ elementaryClosure (detector i)) → x = 1) :
    ∃ C : ℕ, ∀ {ι : Type v} (multiplier : ι → Fin (k + 1) → ℤ),
      (∀ j i, multiplier j i ≠ 0) →
      (∀ j l (i : Fin k),
        multiplier j i.castSucc = multiplier l i.castSucc) →
      (∀ j l, j ≠ l →
        multiplier j (Fin.last k) ≠ multiplier l (Fin.last k)) →
      (∀ j i,
        ((detector i ^ (exponent i : ℤ)) ^ multiplier j i) ∉
          (coneOffFamily A.alphabet
            (fun s ↦ elementaryClosure (detector s))).relBall i C) →
      (∀ j, IsLoxodromic
        (orderedFinProduct (fun i ↦
          (detector i ^ (exponent i : ℤ)) ^ multiplier j i))
        (Cayley.base (coneOffFamily A.alphabet
          (fun s ↦ elementaryClosure (detector s))).alphabet)) →
      ∃ P : YiOrientationPureProductFamily A T ι,
        P.HasConsecutiveComponentMatch := by
  let E : Fin (k + 1) → Subgroup G :=
    fun i ↦ elementaryClosure (detector i)
  let D : RelGenSet G (Fin (k + 1)) := coneOffFamily A.alphabet E
  have hemb : D.IsHyperbolicallyEmbedded := by
    exact isHyperbolicallyEmbedded_elementaryClosure_family
      A detector hdetectorNc hdetectorLox
  have hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet) :=
    hemb.hyperbolic
  obtain ⟨Cmatch, hmatch⟩ :=
    exists_depth_hasConsecutiveComponentMatchData_of_dgoLemma421b
      h421b A.alphabet detector hk hhyp
  obtain ⟨Ccompare, hcompare⟩ :=
    exists_depth_pairwiseNonCommensurable_cyclicProducts_of_dgoLemma421b
      h421b A.alphabet detector hk hhyp
  refine ⟨max Cmatch Ccompare, ?_⟩
  intro ι multiplier hmult hcommon hdistinct hdeep hloxEnlarged
  let letter : ι → Fin (k + 1) → G := fun j i ↦
    (detector i ^ (exponent i : ℤ)) ^ multiplier j i
  have hletterMem : ∀ j i, letter j i ∈ elementaryClosure (detector i) := by
    intro j i
    dsimp [letter]
    exact Subgroup.zpow_mem _
      (Subgroup.zpow_mem _ (self_mem_elementaryClosure (detector i)) _) _
  have hdeepMatch : ∀ j i, letter j i ∉ D.relBall i Cmatch := by
    intro j i
    exact notMem_relBall_of_le (Nat.le_max_left _ _) (hdeep j i)
  have hdeepCompare : ∀ j i, letter j i ∉ D.relBall i Ccompare := by
    intro j i
    exact notMem_relBall_of_le (Nat.le_max_right _ _) (hdeep j i)
  have hbaseSubset : A.alphabet.carrier ⊆ D.alphabet.carrier := by
    intro x hx
    apply base_subset_alphabet_carrier D
    exact hx
  have hloxBase : ∀ j,
      IsLoxodromic (orderedFinProduct (letter j))
        (Cayley.base A.alphabet) := by
    intro j
    exact isLoxodromic_base_of_subset hbaseSubset (hloxEnlarged j)
  have hcentralLetter : ∀ j (i : Fin k),
      (elementaryClosure (detector i.castSucc) : Set G) =
        {x : G | Commute x (letter j i.castSucc)} := by
    intro j i
    dsimp [letter]
    exact elementaryClosure_eq_centralizer_zpow_mul
      (Int.ofNat_ne_zero.mpr (ne_of_gt (hexponent i.castSucc)))
      (hcentral i.castSucc) (hmult j i.castSucc)
  have hterminal : ∀ j l, j ≠ l →
      (letter j (Fin.last k))⁻¹ * letter l (Fin.last k) ∉
        elementaryClosure (detector 0) := by
    intro j l hjl
    exact terminalRatio_notMem_first_of_nonCommensurable
      A (by omega) detector hdetectorLox hdetectorNc exponent hexponent
        (hdistinct j l hjl)
  have hproductNc :
      PairwiseNonCommensurable (fun j ↦ orderedFinProduct (letter j)) := by
    exact hcompare letter hletterMem hdeepCompare hloxBase
      (fun j l i ↦ by simp only [letter, hcommon j l i])
      hcentralLetter hinter hterminal
  let P : YiOrientationPureProductFamily A T ι :=
    { k := k + 1
      three_le := by omega
      detector := detector
      detector_mem := hdetectorT
      detector_loxodromic := hdetectorLox
      exponent := fun i ↦ (exponent i : ℤ)
      exponent_ne_zero := fun i ↦
        Int.ofNat_ne_zero.mpr (ne_of_gt (hexponent i))
      base_centralizer := hcentral
      multiplier := multiplier
      multiplier_ne_zero := hmult
      letter := letter
      letter_eq := fun _ _ ↦ rfl
      intersection_eq_one := hinter
      productAlphabet := D.alphabet
      base_subset_productAlphabet := hbaseSubset
      product_loxodromic_enlarged := hloxEnlarged
      product_nonCommensurable := hproductNc }
  refine ⟨P, ?_⟩
  intro j t ht
  exact hmatch (letter j) (hletterMem j) (hdeepMatch j)
    (hloxBase j) t ht

end HullSC
end GroupApproximation
