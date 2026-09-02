import GroupApproximation.GGT.HullYiCorollary612Family
import GroupApproximation.GGT.HullYiLemmaC

/-!
# Hull's orientation-pure finite families

This module formalizes Hull's Lemma 5.4 construction.  Starting with the two
independent loxodromics in a non-elementary subgroup, DGO Corollary 6.12 gives
three pairwise non-commensurable loxodromics.  Their elementary closures form
a hyperbolically embedded triple.  Deep powers `a,b` in the first two factors
have `ab` outside the third by Hull's fixed-side Lemma C.  Corollary 6.12 then
chooses the final powers `c_i`, and Lemma 4.21(b)'s forward/reverse match proves
that every `a b c_i` has orientation-preserving elementary closure.
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

/-- The three-letter family used in Hull's Lemma 5.4. -/
def yiTriple (a b c : G) : Fin 3 → G := ![a, b, c]

@[simp] theorem orderedFinProduct_yiTriple (a b c : G) :
    orderedFinProduct (yiTriple a b c) = a * b * c := by
  simp [yiTriple, orderedFinProduct]

/-- Independent loxodromics cannot put the second one in the elementary
closure of the first. -/
theorem not_mem_elementaryClosure_of_independent
    (A : HullGeneratingSet G) {a b : G}
    (ha : IsLoxodromic a (Cayley.base A.alphabet))
    (hb : IsLoxodromic b (Cayley.base A.alphabet))
    (hind : Independent a b (Cayley.base A.alphabet)) :
    b ∉ elementaryClosure a := by
  intro hbE
  have hfin := elementaryClosureFiniteTransversal_hullGeneratingSet A ha
  have hsub : Subgroup.zpowers b ≤ elementaryClosure a := by
    exact Subgroup.zpowers_le.mpr hbE
  obtain ⟨p, hp, hpq⟩ := exists_nonzero_zpow_mem_of_finiteTransversal
    hfin (Subgroup.zpowers b) hsub (infinite_coe_zpowers hb)
  obtain ⟨q, hq⟩ := Subgroup.mem_zpowers_iff.mp hpq
  have hq0 : q ≠ 0 := by
    intro hq0
    subst q
    simp only [zpow_zero] at hq
    have ha1 := zpow_ne_one_of_isLoxodromic
      (isIsometricAction_cayley A.alphabet) ha hp
    exact ha1 hq.symm
  exact not_independent_of_common_zpow
    (isIsometricAction_cayley A.alphabet) ha hp hq0 hq.symm hind

/-- **Hull Lemma 5.4, finite-family form, including the centralizer powers.** -/
theorem exists_orientationPure_family_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {S : Subgroup G} (hS : ActsNonElementarily S (Cayley.base A.alphabet))
    (N : ℕ) :
    ∃ (f : Fin N → G) (r : Fin N → ℕ),
      (∀ i, f i ∈ S) ∧
      (∀ i, IsLoxodromic (f i) (Cayley.base A.alphabet)) ∧
      PairwiseNonCommensurable f ∧
      (∀ i, (elementaryClosure (f i) : Set G) =
        positiveElementaryClosure (f i)) ∧
      (∀ i, 0 < r i) ∧
      ∀ i, (elementaryClosure (f i) : Set G) =
        {x : G | Commute x (f i ^ (r i : ℤ))} := by
  obtain ⟨h, hhS, g, hgS, hhlox, hglox, hind⟩ := hS
  have hgE : g ∉ elementaryClosure h :=
    not_mem_elementaryClosure_of_independent A hhlox hglox hind
  obtain ⟨power0, hpower0, -, hqlox, hqnc⟩ :=
    exists_pairwiseNonCommensurable_mul_powers_of_dgoLemma421b
      h421b A hhlox hgE ∅ Set.finite_empty 3
  let q : Fin 3 → G := fun i ↦ g * power0 i
  have hqS : ∀ i, q i ∈ S := by
    intro i
    obtain ⟨m, -, hm⟩ := hpower0 i
    dsimp [q]
    rw [hm]
    exact S.mul_mem hgS (S.pow_mem hhS m)
  have hqlox' : ∀ i, IsLoxodromic (q i) (Cayley.base A.alphabet) := hqlox
  have hqnc' : PairwiseNonCommensurable q := hqnc
  let D : RelGenSet G (Fin 3) :=
    coneOffFamily A.alphabet (fun i ↦ elementaryClosure (q i))
  have hemb : D.IsHyperbolicallyEmbedded :=
    isHyperbolicallyEmbedded_elementaryClosure_family A q hqnc' hqlox'
  have hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet) :=
    hemb.hyperbolic
  obtain ⟨Corient, horient⟩ :=
    exists_depth_hasPositivePowerNormalizer_cyclicProduct_of_dgoLemma421b
      h421b A.alphabet q (k := 2) (by omega) hhyp
  obtain ⟨deltaD, hdeltaD⟩ := hhyp
  have hfour : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier ⌈deltaD⌉₊ :=
    isFourPointHyperbolic_of_isHyperbolicSpace_cayley D.alphabet hdeltaD
  obtain ⟨Rsep, hsep⟩ := GGT.HullYi.exists_radius_notMem_fam_mul
    D A.alphabet.symmetricGenerating.inv_mem hfour
  let depthA := max 1 (max Corient Rsep)
  have hq0inj : Function.Injective (fun n : ℕ ↦ q 0 ^ n) :=
    injective_pow_of_not_isOfFinOrder
      (not_isOfFinOrder_of_isLoxodromic (hqlox' 0))
  obtain ⟨ma, -, haDeep, -⟩ :=
    exists_deep_pow hq0inj (hemb.locallyFinite 0 depthA) 1
  let a : G := q 0 ^ ma
  have haMem : a ∈ D.fam 0 := by
    dsimp [a, D]
    exact (elementaryClosure (q 0)).pow_mem (self_mem_elementaryClosure (q 0)) ma
  have haS : a ∈ S := S.pow_mem (hqS 0) ma
  have haDeepOrient : a ∉ D.relBall 0 Corient :=
    notMem_relBall_of_le (le_trans (le_max_left _ _) (le_max_right _ _)) haDeep
  have haDeepSep : a ∉ D.relBall 0 Rsep :=
    notMem_relBall_of_le (le_trans (le_max_right _ _) (le_max_right _ _)) haDeep
  have haDeepOne : a ∉ D.relBall 0 1 :=
    notMem_relBall_of_le (le_max_left _ _) haDeep
  let depthB := max Corient 1
  have hq1inj : Function.Injective (fun n : ℕ ↦ q 1 ^ n) :=
    injective_pow_of_not_isOfFinOrder
      (not_isOfFinOrder_of_isLoxodromic (hqlox' 1))
  obtain ⟨mb, -, hbDeep, -⟩ :=
    exists_deep_pow hq1inj (hemb.locallyFinite 1 depthB) 1
  let b : G := q 1 ^ mb
  have hbMem : b ∈ D.fam 1 := by
    dsimp [b, D]
    exact (elementaryClosure (q 1)).pow_mem (self_mem_elementaryClosure (q 1)) mb
  have hbS : b ∈ S := S.pow_mem (hqS 1) mb
  have hbDeepOrient : b ∉ D.relBall 1 Corient :=
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
      calc a = a * b * b⁻¹ := by group
        _ = b⁻¹ := by rw [hab1, one_mul]
    apply haDeepOne
    apply mem_relBall_one_of_mem_fam_ne (D := D) (lam := 0) (mu := 1)
      (by decide)
    rw [hab]
    exact inv_mem hbMem
  have habNot : a * b ∉ D.fam 2 :=
    hsep 0 1 2 a b (by decide) (by decide) haMem hbMem hb1 hab1 haDeepSep
  let extra : Set G := D.relBall 2 Corient
  obtain ⟨c, hcPow, hcExtra, hflox, hfnc⟩ :=
    exists_pairwiseNonCommensurable_mul_powers_of_dgoLemma421b
      h421b A (hqlox' 2) (by simpa [D] using habNot)
        extra (hemb.locallyFinite 2 Corient) N
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
    exact (elementaryClosure (q 2)).pow_mem (self_mem_elementaryClosure (q 2)) m
  have hcS : ∀ j, c j ∈ S := by
    intro j
    obtain ⟨m, -, hm⟩ := hcPow j
    rw [hm]
    exact S.pow_mem (hqS 2) m
  have hcDeepOrient : ∀ j, c j ∉ D.relBall 2 Corient :=
    fun j ↦ (hcExtra j).1
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
  have horientation : ∀ j,
      (elementaryClosure (f j) : Set G) = positiveElementaryClosure (f j) :=
    fun j ↦ elementaryClosure_eq_positive_of_hasPositivePowerNormalizer (hnormal j)
  have hcentral : ∀ j, ∃ r : ℕ, 0 < r ∧
      (elementaryClosure (f j) : Set G) =
        {x : G | Commute x (f j ^ (r : ℤ))} := by
    intro j
    exact exists_elementaryClosure_eq_centralizer_pow_of_hasPositivePowerNormalizer
      A (hflox' j) (hnormal j)
  choose r hr hcentral using hcentral
  refine ⟨f, r, ?_, hflox', hfnc', horientation, hr, hcentral⟩
  intro j
  exact S.mul_mem (S.mul_mem haS hbS) (hcS j)

end HullSC
end GroupApproximation
