import GroupApproximation.GGT.GerasimovaOsinCyclicWord
import GroupApproximation.GGT.LoxodromicCyclicEmbeddedAvoiding
import GroupApproximation.Meta.AxiomGuard

/-!
# An infinite cyclic hyperbolically embedded subgroup with `F H F⁻¹ ∩ H = 1`

Gerasimova and Osin's Lemma 4.2 (arXiv:1910.14524v3) with the standing choices of
their §4, in the two-sided form their Lemma 4.5 consumes: for an acylindrically
hyperbolic group with no nontrivial finite normal subgroup and a finite
`F ⊆ G ∖ {1}` there is `y` of infinite order with `⟨y⟩ ↪_h (G, X)` for a
symmetric `X ⊇ F` and

    f · h · g⁻¹ ∈ ⟨y⟩  ⇒  f · h · g⁻¹ = 1     for all f, g ∈ F and h ∈ ⟨y⟩

(`exists_cyclic_hypEmbedded_twoSided`).

## The construction

1. Two applications of Hull's suitable cyclic pair with finite avoidance
   (closed: `HullSC.yiSuitablePairAvoidingFiniteOneSided_of_dgoLemma421b`) give
   four loxodromic detectors `d₀,…,d₃`: pairwise non-commensurable,
   `E(dᵢ) = ⟨dᵢ⟩`, and commensurable with no element of `F`
   (`exists_four_detectors`).
2. Their elementary closures are hyperbolically embedded over Hull's alphabet
   `A`.  By DGO Corollary 4.27 they remain so over `A' = A ∪ S`, where
   `S = F ∪ F⁻¹ ∪ F·F⁻¹` is finite and symmetric.
3. Choose one exponent `n` so deep that `aᵢ = dᵢⁿ` and `aᵢ⁻¹` avoid the relative
   balls for both the constant of DGO Lemma 4.21(a) over `A'` and the depth of
   Hull's consecutive-component match.  Put `y = a₀ a₁ a₂ a₃`.
4. Lemma 4.21(a) makes `y` loxodromic.  The match data, with the centralizer and
   trivial-intersection algebra of `HullYiMatchedProductRigidity`, give
   `E(y) = ⟨y⟩`.  So `⟨y⟩ ↪_h (G, A)` (Hull's cyclic embedding), and then
   `⟨y⟩ ↪_h (G, A')` by 4.27.
5. A violation `f yᵉ g⁻¹ = yᵇ` with `b ≠ 0` is impossible.  If `e = 0`, the
   `X`-letter `f g⁻¹` times `y⁻ᵇ` is a closed `W`-word of length at least `5`.
   If `e ≠ 0`, the word for `yᵉ · g⁻¹ · y⁻ᵇ` ends at the letter `f⁻¹` and has
   length at least `9`.  The letter `g⁻¹` lies in no `⟨dᵢ⟩`, which is condition
   (W3) at the splice.  Lemma 4.21(a) forbids both.

The route differs from Gerasimova--Osin's.  They take a free subgroup
`F_n ↪_h G` from DGO Theorem 6.14 and its malnormality, and the
hyperbolically embedded basis elements come from DGO Proposition 4.35.  Here
one product of deep detector powers and DGO Lemma 4.21(a) replace all three.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (stable rank one through
Gerasimova--Osin, tex line 1730); certifies no printed sentence on its own.
The statement-level wrapper is
`TorsionFreePrinted.gerasimovaOsinLemma42 : GerasimovaOsinLemma42Statement`.
-/

namespace GroupApproximation
namespace GGT
namespace CyclicTwoSided

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.GGT.OsinComponents

/-- **Four detectors.**  Loxodromic on Hull's Cayley graph, pairwise
non-commensurable, with cyclic elementary closures, and commensurable with no
element of `F`. -/
theorem exists_four_detectors {G : Type} [Group G] (A : HullGeneratingSet G)
    (hrad : ∀ N : Subgroup G, N.Normal → Finite N → N = ⊥) (F : Finset G) :
    ∃ det : Fin 4 → G,
      (∀ i, IsLoxodromic (det i) (Cayley.base A.alphabet)) ∧
      HullSC.PairwiseNonCommensurable det ∧
      (∀ i, Elementary.elementaryClosure (det i) = Subgroup.zpowers (det i)) ∧
      ∀ i, ∀ f ∈ F, ¬ HullSC.AreCommensurable (det i) f := by
  classical
  have hT := CyclicEmbeddedChoice.suitable_top_of_trivialFiniteRadical A hrad
  have hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{0} :=
    HullSC.yiSuitablePairAvoidingFiniteOneSided_of_dgoLemma421b
      (OsinComponents.dgoLemma421b_of_uniform414
        OsinComponents.dgoProposition414Uniform)
  obtain ⟨g₁, -, hlox₁, hnc₁, hcyc₁, hav₁⟩ := hyi A hT F
  obtain ⟨g₂, -, hlox₂, hnc₂, hcyc₂, hav₂⟩ :=
    hyi A hT (insert (g₁ false) (insert (g₁ true) F))
  have hmem₀ : g₁ false ∈ insert (g₁ false) (insert (g₁ true) F) :=
    Finset.mem_insert_self _ _
  have hmem₁ : g₁ true ∈ insert (g₁ false) (insert (g₁ true) F) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmemF : ∀ f ∈ F, f ∈ insert (g₁ false) (insert (g₁ true) F) :=
    fun f hf => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hf)
  refine ⟨![g₁ false, g₁ true, g₂ false, g₂ true], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hlox₁ false
    · exact hlox₁ true
    · exact hlox₂ false
    · exact hlox₂ true
  · intro i j hij p q hp hq t heq
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · exact hnc₁ false true (by decide) p q hp hq t heq
    · exact hav₂ false (g₁ false) hmem₀
        (HullSC.areCommensurable_symm ⟨p, q, t, hp, hq, heq⟩)
    · exact hav₂ true (g₁ false) hmem₀
        (HullSC.areCommensurable_symm ⟨p, q, t, hp, hq, heq⟩)
    · exact hnc₁ true false (by decide) p q hp hq t heq
    · exact hij rfl
    · exact hav₂ false (g₁ true) hmem₁
        (HullSC.areCommensurable_symm ⟨p, q, t, hp, hq, heq⟩)
    · exact hav₂ true (g₁ true) hmem₁
        (HullSC.areCommensurable_symm ⟨p, q, t, hp, hq, heq⟩)
    · exact hav₂ false (g₁ false) hmem₀ ⟨p, q, t, hp, hq, heq⟩
    · exact hav₂ false (g₁ true) hmem₁ ⟨p, q, t, hp, hq, heq⟩
    · exact hij rfl
    · exact hnc₂ false true (by decide) p q hp hq t heq
    · exact hav₂ true (g₁ false) hmem₀ ⟨p, q, t, hp, hq, heq⟩
    · exact hav₂ true (g₁ true) hmem₁ ⟨p, q, t, hp, hq, heq⟩
    · exact hnc₂ true false (by decide) p q hp hq t heq
    · exact hij rfl
  · intro i
    fin_cases i
    · exact hcyc₁ false
    · exact hcyc₁ true
    · exact hcyc₂ false
    · exact hcyc₂ true
  · intro i f hf
    fin_cases i
    · exact hav₁ false f hf
    · exact hav₁ true f hf
    · exact hav₂ false f (hmemF f hf)
    · exact hav₂ true f (hmemF f hf)

/-- **Gerasimova--Osin's Lemma 4.2, two-sided.**  An element `y` of infinite
order, a symmetric relative generating set `X ⊇ F` with `⟨y⟩ ↪_h (G, X)`, and
`f h g⁻¹ ∈ ⟨y⟩ ⇒ f h g⁻¹ = 1` for `f, g ∈ F`, `h ∈ ⟨y⟩`. -/
theorem exists_cyclic_hypEmbedded_twoSided (G : Type) [Group G]
    [IsAcylindricallyHyperbolic G]
    (hrad : ∀ N : Subgroup G, N.Normal → Finite N → N = ⊥) (F : Finset G)
    (hF : (1 : G) ∉ F) :
    ∃ (y : G) (D : RelGenSet G Unit),
      ¬ IsOfFinOrder y ∧ D.fam () = Subgroup.zpowers y ∧ (F : Set G) ⊆ D.base ∧
        DGO421BaseSymmetric D ∧ D.IsHyperbolicallyEmbedded ∧
          ∀ f ∈ F, ∀ g ∈ F, ∀ h ∈ Subgroup.zpowers y,
            f * h * g⁻¹ ∈ Subgroup.zpowers y → f * h * g⁻¹ = 1 := by
  classical
  obtain ⟨A⟩ := CyclicEmbeddedChoice.nonempty_hullGeneratingSet G
  obtain ⟨det, hdetLox, hdetNc, hdetCyc, hdetAvoid⟩ := exists_four_detectors A hrad F
  -- the finite symmetric set adjoined to Hull's alphabet
  let S : Set G :=
    ((F : Set G) ∪ {x : G | x⁻¹ ∈ F}) ∪ {x : G | ∃ f ∈ F, ∃ g ∈ F, x = f * g⁻¹}
  have hSfin : S.Finite := by
    refine ((F.finite_toSet.union (F.finite_toSet.preimage inv_injective.injOn)).union
      ((F.finite_toSet.prod F.finite_toSet).image
        fun p : G × G => p.1 * p.2⁻¹)).subset ?_
    rintro x ((hx | hx) | ⟨f, hf, g, hg, rfl⟩)
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr ⟨(f, g), ⟨hf, hg⟩, rfl⟩
  have hSinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    rintro x ((hx | hx) | ⟨f, hf, g, hg, rfl⟩)
    · exact Or.inl (Or.inr (by simpa using hx))
    · exact Or.inl (Or.inl hx)
    · exact Or.inr ⟨g, hg, f, hf, by group⟩
  let A' : Alphabet G :=
    { carrier := A.alphabet.carrier ∪ S
      symmetricGenerating := by
        refine ⟨?_, ?_⟩
        · rintro x (hx | hx)
          · exact Or.inl (A.alphabet.symmetricGenerating.inv_mem x hx)
          · exact Or.inr (hSinv x hx)
        · refine eq_top_iff.mpr ?_
          rw [← A.alphabet.symmetricGenerating.closure_eq]
          exact Subgroup.closure_mono fun x hx => Or.inl hx }
  have hAA' : A.alphabet.carrier ⊆ A'.carrier := fun x hx => Or.inl hx
  have hFA' : ∀ f ∈ F, f ∈ A'.carrier := fun f hf => Or.inr (Or.inl (Or.inl hf))
  have hFinvA' : ∀ f ∈ F, f⁻¹ ∈ A'.carrier := fun f hf =>
    Or.inr (Or.inl (Or.inr (by simpa using hf)))
  have hFFA' : ∀ f ∈ F, ∀ g ∈ F, f * g⁻¹ ∈ A'.carrier := fun f hf g hg =>
    Or.inr (Or.inr ⟨f, hf, g, hg, rfl⟩)
  have hfinBase :
      ((A.alphabet.carrier \ A'.carrier) ∪ (A'.carrier \ A.alphabet.carrier)).Finite := by
    refine hSfin.subset ?_
    rintro x (⟨hx0, hx1⟩ | ⟨hx1, hx0⟩)
    · exact absurd (hAA' hx0) hx1
    · rcases hx1 with hx | hx
      · exact absurd hx hx0
      · exact hx
  -- the detector collection over the enlarged alphabet
  let E : Fin 4 → Subgroup G := fun i => Elementary.elementaryClosure (det i)
  let D₀ : RelGenSet G (Fin 4) := HullSC.coneOffFamily A.alphabet E
  let D' : RelGenSet G (Fin 4) := HullSC.coneOffFamily A' E
  have hemb₀ : D₀.IsHyperbolicallyEmbedded :=
    HullSC.isHyperbolicallyEmbedded_elementaryClosure_family A det hdetNc hdetLox
  have hemb' : D'.IsHyperbolicallyEmbedded :=
    (RelGenSet.dgoCorollary427 G (Fin 4) D₀ D' rfl hfinBase).mp hemb₀
  have hbase' : DGO421BaseSymmetric D' := fun x hx =>
    A'.symmetricGenerating.inv_mem x hx
  obtain ⟨Ca, hquasi⟩ := OsinComponents.dgoLemma421a G (Fin 4) D' hemb'.hyperbolic hbase'
  have h421b : DGOLemma421b.{0, 0} :=
    OsinComponents.dgoLemma421b_of_uniform414 OsinComponents.dgoProposition414Uniform
  obtain ⟨Cm, hmatch⟩ :=
    HullSC.exists_depth_hasConsecutiveComponentMatchData_of_dgoLemma421b
      (k := 3) h421b A' det (by norm_num) hemb'.hyperbolic
  -- one deep exponent for both depths
  have hball : (⋃ i : Fin 4, D'.relBall i (max Ca Cm)).Finite :=
    Set.finite_iUnion fun i => hemb'.locallyFinite i (max Ca Cm)
  have hinj : ∀ i, Function.Injective (fun n : ℕ => det i ^ n) := fun i =>
    HullSC.injective_pow_of_not_isOfFinOrder
      (not_isOfFinOrder_of_isLoxodromic (hdetLox i))
  obtain ⟨n, hn1, hdeepn⟩ := HullSC.exists_deep_pow_finite_family det hinj hball 1
  let a : Fin 4 → G := fun i => det i ^ n
  have ha : ∀ i, a i ∈ D'.fam i := fun i =>
    Subgroup.pow_mem _ (Elementary.self_mem_elementaryClosure (det i)) n
  have hdeepBall : ∀ i, a i ∉ D'.relBall i (max Ca Cm) ∧
      (a i)⁻¹ ∉ D'.relBall i (max Ca Cm) := fun i =>
    ⟨fun hx => (hdeepn i).1 (Set.mem_iUnion.mpr ⟨i, hx⟩),
      fun hx => (hdeepn i).2 (Set.mem_iUnion.mpr ⟨i, hx⟩)⟩
  have hdeepA : ∀ i, a i ∉ D'.relBall i Ca ∧ (a i)⁻¹ ∉ D'.relBall i Ca := fun i =>
    ⟨HullSC.notMem_relBall_of_le (le_max_left _ _) (hdeepBall i).1,
      HullSC.notMem_relBall_of_le (le_max_left _ _) (hdeepBall i).2⟩
  have hdeepM : ∀ i, a i ∉ D'.relBall i Cm := fun i =>
    HullSC.notMem_relBall_of_le (le_max_right _ _) (hdeepBall i).1
  -- the product is loxodromic: Lemma 4.21(a) on its positive powers
  have hxLoxD : IsLoxodromic (a 0 * a 1 * a 2 * a 3) (Cayley.base D'.alphabet) := by
    refine ⟨1, one_pos, 1, zero_le_one, ?_⟩
    intro N
    have hbound := hquasi 1 (posWord a N) (isLetter_posWord D' ha N) (isWOne_posWord a N)
      (isWTwo_posWord D' hdeepA N) (isWThree_posWord D' a N) 0 (posWord a N).length
      (Nat.zero_le _) le_rfl
    rw [OsinComponents.vertex_zero, OsinComponents.vertex_length, one_mul, listVal_posWord,
      length_posWord, Nat.sub_zero] at hbound
    have hreal : ((4 * N : ℕ) : ℝ) ≤
        4 * (wordDist D'.alphabet.carrier 1 ((a 0 * a 1 * a 2 * a 3) ^ N) : ℝ) + 4 := by
      exact_mod_cast hbound
    rw [Cayley.dist_eq, Cayley.val_base, Cayley.val_smul, Cayley.val_base, mul_one]
    push_cast at hreal ⊢
    linarith
  have hxLoxA' : IsLoxodromic (a 0 * a 1 * a 2 * a 3) (Cayley.base A') :=
    HullSC.isLoxodromic_base_of_subset (A := A') (A₁ := D'.alphabet)
      (fun z hz => Set.mem_union_left _ hz) hxLoxD
  have hxLoxA : IsLoxodromic (a 0 * a 1 * a 2 * a 3) (Cayley.base A.alphabet) :=
    HullSC.isLoxodromic_base_of_subset (A := A.alphabet) (A₁ := A') hAA' hxLoxA'
  -- cyclic elementary closure: Hull's matched-product rigidity
  have hord : HullSC.orderedFinProduct a = a 0 * a 1 * a 2 * a 3 := by
    show a 0 * (a 1 * (a 2 * (a 3 * 1))) = a 0 * a 1 * a 2 * a 3
    group
  have hcentral : ∀ i : Fin 4,
      (Elementary.elementaryClosure (det i) : Set G) = {z : G | Commute z (a i)} := by
    intro i
    ext z
    constructor
    · intro hz
      have hz' : z ∈ Subgroup.zpowers (det i) := by
        rw [← hdetCyc i]
        exact hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
      exact ((Commute.refl (det i)).zpow_left k).pow_right n
    · intro hz
      have hz' : Commute z (det i ^ n) := hz
      refine Elementary.mem_elementaryClosure.mpr ⟨(n : ℤ), (n : ℤ), ?_, ?_, ?_⟩
      · exact_mod_cast (show n ≠ 0 by omega)
      · exact_mod_cast (show n ≠ 0 by omega)
      · rw [zpow_natCast]
        have hc : z * det i ^ n = det i ^ n * z := hz'.eq
        rw [hc, mul_inv_cancel_right]
  have hinter : ∀ z : G,
      (∀ i : Fin 4, z ∈ Elementary.elementaryClosure (det i)) → z = 1 := by
    intro z hz
    by_contra hne
    have h0 : z ∈ Subgroup.zpowers (det 0) := by
      rw [← hdetCyc 0]
      exact hz 0
    have h1 : z ∈ Subgroup.zpowers (det 1) := by
      rw [← hdetCyc 1]
      exact hz 1
    obtain ⟨p, hp⟩ := Subgroup.mem_zpowers_iff.mp h0
    obtain ⟨q, hq⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact hne (by rw [← hp, zpow_zero])
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact hne (by rw [← hq, zpow_zero])
    exact hdetNc 0 1 (by decide) p q hp0 hq0 1 (by rw [one_mul, inv_one, mul_one, hp, hq])
  have hloxOrd : IsLoxodromic (HullSC.orderedFinProduct a) (Cayley.base A') := by
    rw [hord]
    exact hxLoxA'
  have hxcyc : Elementary.elementaryClosure (a 0 * a 1 * a 2 * a 3) =
      Subgroup.zpowers (a 0 * a 1 * a 2 * a 3) := by
    have h := HullSC.elementaryClosure_eq_zpowers_of_matchedProduct (by norm_num) det a
      (HullSC.orderedFinProduct a) hcentral hinter (hmatch a ha hdeepM hloxOrd)
    rwa [hord] at h
  -- `⟨y⟩ ↪_h (G, A)`, then over the enlarged alphabet
  let D₀x : RelGenSet G Unit :=
    HullSC.coneOffFamily A.alphabet (fun _ : Unit => Subgroup.zpowers (a 0 * a 1 * a 2 * a 3))
  let Dx : RelGenSet G Unit :=
    HullSC.coneOffFamily A' (fun _ : Unit => Subgroup.zpowers (a 0 * a 1 * a 2 * a 3))
  have hembx₀ : D₀x.IsHyperbolicallyEmbedded :=
    HullSC.isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional A
      (fun _ : Unit => a 0 * a 1 * a 2 * a 3)
      (HullSC.pairwiseNonCommensurable_of_subsingleton _) (fun _ => hxLoxA) (fun _ => hxcyc)
  have hembx : Dx.IsHyperbolicallyEmbedded :=
    (RelGenSet.dgoCorollary427 G Unit D₀x Dx rfl hfinBase).mp hembx₀
  refine ⟨a 0 * a 1 * a 2 * a 3, Dx, not_isOfFinOrder_of_isLoxodromic hxLoxA, rfl,
    fun f hf => hFA' f hf, fun z hz => A'.symmetricGenerating.inv_mem z hz, hembx, ?_⟩
  -- the two-sided clause
  intro f hf g hg h hh hmem
  obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp hmem
  by_cases hb0 : b = 0
  · rw [← hb, hb0, zpow_zero]
  · exfalso
    by_cases he0 : e = 0
    · subst he0
      rw [zpow_zero, mul_one] at hb
      have hy : f * g⁻¹ ∈ D'.base := hFFA' f hf g hg
      refine base_mul_zpow_ne_one hquasi ha hdeepA hy (neg_ne_zero.mpr hb0) ?_
      rw [zpow_neg, ← hb, mul_inv_cancel]
    · have hy : g⁻¹ ∈ D'.base := hFinvA' g hg
      have hz : f⁻¹ ∈ D'.alphabet.carrier :=
        Set.mem_union_left _ (hFinvA' f hf)
      have hynot : ∀ lam : Fin 4, g⁻¹ ∉ D'.fam lam := by
        intro lam hmem'
        have hz' : g⁻¹ ∈ Subgroup.zpowers (det lam) := by
          rw [← hdetCyc lam]
          exact hmem'
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [zpow_zero] at hk
          have hg1 : g = 1 := inv_eq_one.mp hk.symm
          exact hF (hg1 ▸ hg)
        exact hdetAvoid lam g hg ⟨-k, 1, 1, neg_ne_zero.mpr hk0, one_ne_zero, by
          rw [one_mul, inv_one, mul_one, zpow_neg, hk, inv_inv, zpow_one]⟩
      refine zpow_mul_base_mul_zpow_ne hquasi ha hdeepA hy hynot hz he0
        (neg_ne_zero.mpr hb0) ?_
      have h1 : (a 0 * a 1 * a 2 * a 3) ^ e * g⁻¹ =
          f⁻¹ * (a 0 * a 1 * a 2 * a 3) ^ b := by
        rw [hb]
        group
      rw [h1, zpow_neg, mul_inv_cancel_right]

end CyclicTwoSided
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.CyclicTwoSided.exists_four_detectors
#audit_axioms GroupApproximation.GGT.CyclicTwoSided.exists_cyclic_hypEmbedded_twoSided
