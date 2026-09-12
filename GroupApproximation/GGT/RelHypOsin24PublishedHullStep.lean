import GroupApproximation.GGT.RelHypOsin24FromHull
import GroupApproximation.GGT.HullSCLemma44BoundedJointRespellingHullRelator
import GroupApproximation.GGT.HullSCLemma44BoundedBridge
import GroupApproximation.GGT.HullSCUnconeThin
import GroupApproximation.GGT.HullSCBoundedImageEmbedding
import GroupApproximation.GGT.HullSCAuxiliaryAdjoinFinite
import GroupApproximation.GGT.DGOProposition435JointPrescribed
import GroupApproximation.GGT.DGOCorollary427PairLocal
import GroupApproximation.GGT.HullSCLemma44FamilyAssembly
import GroupApproximation.GGT.HullYiFiniteFamilyInduction
import GroupApproximation.GGT.HullYiCyclicProductClosure
import GroupApproximation.GGT.DGOLemma421FromUniform414
import GroupApproximation.GGT.DGOProposition414General
import GroupApproximation.GGT.HullSCFillingSelectionTheorem316
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Theorem 2.4, one target, at Hull's published relator

`osin24HullStep_of_data` (`GGT/RelHypOsin24FromHull.lean`) reads the original-family and joint
conjuncts of the family form of Hull's Lemma 4.4, whose producer carries the uniform re-spelling
admission.  This module proves the same one-target step, `Osin24HullStepStatement`, on the
source's route instead (`osin24HullStep_of_boundedLeaves`):

* the selected family and Lemma 4.4 at it are the bounded canonical statement, on the exact published
  relator `t⁻¹u` of Hull's §6;
* the joint collection `{H_λ} ∪ {⟨f₁⟩, ⟨f₂⟩}` is hyperbolically embedded over a finite enlargement of
  the original base (Proposition 4.35 through Proposition 4.14), its base is adjoined to the selected
  base (`AuxiliaryPeripheralFamily.exists_adjoinFinite`) together with the target, and the published
  relator is read in joint letters (`HullSC.exists_publishedRelator_boundedJointRespelling`), as Hull
  does in the proof of his Corollary 7.4;
* Osin's Lemma 5.1 at the joint collection makes its image hyperbolically embedded
  (`HullSC.BoundedImageEmbeddingStatement`);
* the original collection in the quotient is the joint image with the cyclic members un-coned into the
  base (`GGT.cyclicPeripheralRemovalStatement`, Proposition 4.35 in its printed direction), which
  adjoins finitely many generators to the base.

Everything else is `osin24HullStep_of_data` verbatim.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **The one-target Osin step**, in the form the finite iteration consumes. -/
def Osin24HullStepStatement : Prop :=
  ∀ {G : Type} [Group G] {I : Type} {Hfam : I → Subgroup G} {H : Subgroup G},
    RelativeHullContinuationData Hfam H → ∀ t : G, Osin24HullStepConclusion Hfam H t

/-- **Osin's Theorem 2.4 at one target, from the bounded canonical Lemma 4.4, Lemma 5.1 in image form
and Lemma 4.9.** -/
theorem osin24HullStep_of_boundedLeaves
    (h44 : HullSC.BoundedHullLemma44CanonicalQuotientStatement.{0})
    (hemb : HullSC.BoundedImageEmbeddingStatement.{0, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{0, 0}) :
    Osin24HullStepStatement := by
  intro G _ I Hfam H B t
  classical
  have hselect : HullSC.SimultaneousAuxiliaryPeripheralSelection.{0} :=
    HullSC.simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
      (HullSC.yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided.mpr
        (HullSC.yiSuitablePairAvoidingFiniteOneSided_of_dgoLemma421b
          (GGT.OsinComponents.dgoLemma421b_of_uniform414
            GGT.OsinComponents.dgoProposition414Uniform)))
  let emptyFamily : Fin 0 → Subgroup G := Fin.elim0
  obtain ⟨D₀⟩ := hselect B.hull emptyFamily B.suitable (by
    intro j
    exact Fin.elim0 j)
  obtain ⟨E₀, htBase₀, hacy₀⟩ := D₀.exists_acylindricalAdjoinPair t
  have hOriginalAlphabet : B.rel.alphabet.carrier ⊆ B.hull.alphabet.carrier :=
    B.rel_alphabet_subset
  -- the joint collection over a finite enlargement of the original base
  obtain ⟨joint₀, hjointInv₀, hinl₀, hinr₀, hjointEmb₀, T₀, hT₀, hT₀sub, hjointSub₀⟩ :=
    HullSC.jointAuxiliaryPeripheralEmbedding_of_proposition414Uniform
      GGT.OsinComponents.dgoProposition414Uniform E₀ B.rel hOriginalAlphabet B.embedded
  -- its enlargement adjoined to the selected base
  obtain ⟨D, hcores, hbaseD, hT₀D, hcarrierD⟩ :=
    HullSC.AuxiliaryPeripheralFamily.exists_adjoinFinite E₀ hT₀ hT₀sub
  have hacyD := HullSC.isAcylindrical_of_alphabet_eq
    (GGT.OsinComponents.alphabet_eq_of_carrier_eq hcarrierD) hacy₀
  have htD : t⁻¹ ∈ D.rel.base := hbaseD htBase₀
  -- the target adjoined to the joint base
  have hjointEmb : (joint₀.adjoinPair t).IsHyperbolicallyEmbedded :=
    GGT.RelGenSet.isHyperbolicallyEmbedded_adjoinPair_of_localFiniteness
      GGT.RelGenSet.pairLocalFiniteness joint₀ hjointEmb₀ t
  have hjointInv : ∀ x ∈ (joint₀.adjoinPair t).base, x⁻¹ ∈ (joint₀.adjoinPair t).base := by
    intro x hx
    simp only [GGT.RelGenSet.adjoinPair_base, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with hx | rfl | rfl
    · exact Or.inl (hjointInv₀ x hx)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl (inv_inv t))
  have hinl : ∀ lam : I, (joint₀.adjoinPair t).fam (Sum.inl lam) = B.rel.fam lam := hinl₀
  have hinr : ∀ i : HullSC.AuxiliaryPeripheralIndex 0,
      (joint₀.adjoinPair t).fam (Sum.inr i) = D.cores.peripheral i := by
    intro i
    rw [hcores]
    exact hinr₀ i
  have hbaseSub : (joint₀.adjoinPair t).base ⊆ D.rel.base := by
    intro x hx
    simp only [GGT.RelGenSet.adjoinPair_base, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | rfl | rfl
    · rcases hjointSub₀ hx with hx | hx
      · exact hbaseD (E₀.base_le (hOriginalAlphabet (Or.inl hx)))
      · exact hT₀D hx
    · simpa using D.base_inv _ htD
    · exact htD
  have htJoint : t⁻¹ ∈ (joint₀.adjoinPair t).base := Or.inr (Or.inr rfl)
  -- the parameters
  obtain ⟨eps₄₄, rho₄₄, mu₄₄, hmu₄₄, hgood₄₄⟩ := h44 D 1
  obtain ⟨eps₄₉, rho₄₉, mu₄₉, hmu₄₉, hgood₄₉⟩ := h49 D.rel D.embedded hacyD
  let mu : ℝ := min (min mu₄₄ mu₄₉) (1 / 1000)
  have hmu : 0 < mu := lt_min (lt_min hmu₄₄ hmu₄₉) (by norm_num)
  have hmuUpper : mu ≤ 1 / 1000 := min_le_right _ _
  obtain ⟨epsJ, rhoJ, hgoodJ⟩ := hemb (joint₀.adjoinPair t) hjointEmb mu hmu hmuUpper
  let eps : ℕ := max (max eps₄₄ eps₄₉) epsJ
  let rho : ℕ := max (max (max rho₄₄ rho₄₉) rhoJ) (20 * (eps + 1))
  have hepsJ : epsJ ≤ eps := Nat.le_max_right _ _
  have hrhoJ : rhoJ ≤ rho := le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have h20 : 20 * (eps + 1) ≤ rho := Nat.le_max_right _ _
  -- the published relator, read in joint letters
  obtain ⟨u, hu, v, hval, hsc, hscb, hresp⟩ :=
    HullSC.exists_publishedRelator_boundedJointRespelling D B.suitable B.rel
      (joint₀.adjoinPair t) hOriginalAlphabet hbaseSub hjointInv hinl hinr t htD htJoint
      epsJ rhoJ eps rho mu hmu hepsJ hrhoJ h20
  let W := HullSC.RelWord.symmetrized v
  let K : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  let Q : Type 0 := HasQuotient.Quotient G K
  let eta : G →* Q := QuotientGroup.mk' K
  have hsurj : Function.Surjective eta := QuotientGroup.mk'_surjective K
  have hker : eta.ker = K := QuotientGroup.ker_mk' K
  have hvW : v ∈ W := HullSC.RelWord.self_mem_symmetrized v
  have hsc₄₄ : HullSC.RelWord.IsBoundedLemma44Input D.rel W eps₄₄ mu₄₄ rho₄₄ :=
    hscb.mono_parameters
      (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      (le_trans (min_le_left _ _) (min_le_left _ _))
      (le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) (Nat.le_max_left _ _))
  have hsc₄₉ : HullSC.RelWord.IsLemma49Input D.rel W eps₄₉ mu₄₉ rho₄₉ :=
    hsc.mono_parameters
      (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      (le_trans (min_le_left _ _) (min_le_right _ _))
      (le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) (Nat.le_max_left _ _))
  have hkerW : eta.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) := by
    rw [hker, HullSC.RelWord.normalClosure_listVal_image_symmetrized]
  obtain ⟨hball, ⟨Pselected⟩⟩ := hgood₄₄ W eta hsc₄₄ hsurj hkerW
  have hpower : HullSC.KernelPowerCorrection K :=
    hgood₄₉ W v hvW hsc₄₉
  have htorsion : IsOsin24TorsionConclusion eta := by
    apply isOsin24TorsionConclusion_of_kernelPowerCorrection eta hsurj
    rwa [hker]
  -- the joint image
  obtain ⟨W', eps', rho', heps', hrho', h20', hclosure, hscJ⟩ := hresp
  have hkerW' : eta.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W') := by
    rw [hclosure]
    exact hkerW
  obtain ⟨JQ, hJQinv, hJQinl, hJQinr, hJQemb, hJQbase⟩ :
      ∃ JQ : GGT.RelGenSet Q (Sum I (HullSC.AuxiliaryPeripheralIndex 0)),
        (∀ x ∈ JQ.base, x⁻¹ ∈ JQ.base) ∧
          (∀ lam : I, JQ.fam (Sum.inl lam) = (Hfam lam).map eta) ∧
            (∀ i : HullSC.AuxiliaryPeripheralIndex 0,
              JQ.fam (Sum.inr i) = (D.cores.peripheral i).map eta) ∧
              JQ.IsHyperbolicallyEmbedded ∧
                JQ.base ⊆ eta '' (B.rel.base ∪ (T₀ ∪ {t, t⁻¹})) := by
    refine ⟨(joint₀.adjoinPair t).mapSurjective eta hsurj, ?_, ?_, ?_,
      hgoodJ eps' rho' W' eta hsurj heps' hrho' h20' hscJ hkerW', ?_⟩
    · intro x hx
      rw [GGT.RelGenSet.base_mapSurjective] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y⁻¹, hjointInv y hy, map_inv eta y⟩
    · intro lam
      show ((joint₀.adjoinPair t).fam (Sum.inl lam)).map eta = (Hfam lam).map eta
      rw [hinl lam, B.fam_eq]
    · intro i
      show ((joint₀.adjoinPair t).fam (Sum.inr i)).map eta = (D.cores.peripheral i).map eta
      rw [hinr i]
    · intro x hx
      rw [GGT.RelGenSet.base_mapSurjective] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only [GGT.RelGenSet.adjoinPair_base, Set.mem_union,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | rfl | rfl
      · rcases hjointSub₀ hy with hy | hy
        · exact ⟨y, Or.inl hy, rfl⟩
        · exact ⟨y, Or.inr (Or.inl hy), rfl⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
  -- the original collection: the joint image with the cyclic members un-coned
  have hloxMem : ∀ i : HullSC.AuxiliaryPeripheralIndex 0,
      D.cores.lox i ∈ D.cores.peripheral i := by
    intro i
    rw [D.cores.peripheral_eq_zpowers i]
    exact Subgroup.mem_zpowers _
  have hg : ∀ i : HullSC.AuxiliaryPeripheralIndex 0,
      JQ.fam (Sum.inr i) = Subgroup.zpowers (eta (D.cores.lox i)) := by
    intro i
    rw [hJQinr i, D.cores.peripheral_eq_zpowers i, MonoidHom.map_zpowers]
  have hinf : ∀ i : HullSC.AuxiliaryPeripheralIndex 0, ¬ IsOfFinOrder (eta (D.cores.lox i)) :=
    fun i => Pselected.not_isOfFinOrder_map i (hloxMem i)
      (HullGeometry.not_isOfFinOrder_of_isLoxodromic (D.cores.isLoxodromic_lox i))
  have hremoved := GGT.cyclicPeripheralRemovalStatement JQ (fun i => eta (D.cores.lox i)) hg
    hJQinv hinf hJQemb
  have Poriginal :
      HullSC.CanonicalQuotientFamilyPreservation eta B.rel D.rel.alphabet.carrier := by
    refine
      { rel := GGT.removeCyclicPeripherals JQ (fun i => eta (D.cores.lox i)) hg hJQinv
        base_map := ?_
        fam_map := ?_
        embedded := hremoved
        injOn_peripheralUnion := ?_ }
    · refine ⟨T₀ ∪ ({t, t⁻¹} ∪ ⋃ i : HullSC.AuxiliaryPeripheralIndex 0,
          ({D.cores.lox i, (D.cores.lox i)⁻¹} : Set G)), ?_, ?_, ?_⟩
      · exact hT₀.union (((Set.finite_singleton _).insert _).union
          (Set.finite_iUnion fun _ => (Set.finite_singleton _).insert _))
      · rintro x (hx | hx | hx)
        · rw [hcarrierD]
          exact hT₀sub hx
        · rcases hx with rfl | rfl
          · exact Or.inl (by simpa using D.base_inv _ htD)
          · exact Or.inl htD
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          rcases hi with rfl | rfl
          · refine Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩)
            rw [D.fam_eq i]
            exact hloxMem i
          · refine Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩)
            rw [D.fam_eq i]
            exact inv_mem (hloxMem i)
      · rintro x (hx | hx)
        · obtain ⟨y, hy, rfl⟩ := hJQbase hx
          rcases hy with hy | hy | hy
          · exact ⟨y, Or.inl hy, rfl⟩
          · exact ⟨y, Or.inr (Or.inl hy), rfl⟩
          · exact ⟨y, Or.inr (Or.inr (Or.inl hy)), rfl⟩
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          rcases hi with rfl | rfl
          · exact ⟨D.cores.lox i,
              Or.inr (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inl rfl⟩))), rfl⟩
          · exact ⟨(D.cores.lox i)⁻¹,
              Or.inr (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inr rfl⟩))), map_inv eta _⟩
    · intro lam
      show JQ.fam (Sum.inl lam) = (B.rel.fam lam).map eta
      rw [hJQinl lam, B.fam_eq]
    · exact hball.mono
        (HullSC.originalPeripheralUnion_subset_cayleyBall_one B.rel hOriginalAlphabet)
  -- from here on, `osin24HullStep_of_data` with the joint image for `Pjoint.rel`
  have hrelative : IsOsin24RelativeQuotientConclusion Hfam eta := by
    refine ⟨?_, ?_⟩
    · refine ⟨Poriginal.rel, Poriginal.base_finite B.base_finite, ?_,
        Poriginal.embedded⟩
      funext i
      rw [Poriginal.fam_map i, B.fam_eq]
    · intro x hx y hy hxy
      apply Poriginal.injOn_peripheralUnion
      · rw [B.fam_eq]
        exact hx
      · rw [B.fam_eq]
        exact hy
      · exact hxy
  let C := D.cores.coreN
  let i₀ : HullSC.AuxiliaryPeripheralIndex 0 := (none, false)
  let i₁ : HullSC.AuxiliaryPeripheralIndex 0 := (none, true)
  have hf₀Peripheral : C.lox false ∈ D.cores.peripheral i₀ :=
    C.lox_mem false
  have hf₁Peripheral : C.lox true ∈ D.cores.peripheral i₁ :=
    C.lox_mem true
  have hf₀Infinite : ¬ IsOfFinOrder (eta (C.lox false)) :=
    Pselected.not_isOfFinOrder_map i₀ hf₀Peripheral
      (HullGeometry.not_isOfFinOrder_of_isLoxodromic
        (C.lox_isLoxodromic false))
  have hf₁Infinite : ¬ IsOfFinOrder (eta (C.lox true)) :=
    Pselected.not_isOfFinOrder_map i₁ hf₁Peripheral
      (HullGeometry.not_isOfFinOrder_of_isLoxodromic
        (C.lox_isLoxodromic true))
  have hord₀ : ∀ n : ℕ, 0 < n → eta (C.lox false) ^ n ≠ 1 := by
    intro n hn hpow
    exact hf₀Infinite (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩)
  have hord₁ : ∀ n : ℕ, 0 < n → eta (C.lox true) ^ n ≠ 1 := by
    intro n hn hpow
    exact hf₁Infinite (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩)
  have hf₀Joint : eta (C.lox false) ∈ JQ.fam (Sum.inr i₀) := by
    rw [hJQinr i₀]
    exact Subgroup.mem_map_of_mem eta hf₀Peripheral
  have hf₁Joint : eta (C.lox true) ∈ JQ.fam (Sum.inr i₁) := by
    rw [hJQinr i₁]
    exact Subgroup.mem_map_of_mem eta hf₁Peripheral
  have hhyper₀Joint : IsHyperbolicElement
      (fun i => JQ.fam (Sum.inl i)) (eta (C.lox false)) :=
    isHyperbolicElement_of_mem_distinct_jointPeripheral JQ
      hJQinv hJQemb Sum.inl Sum.inr
      (fun _ _ => Sum.inl_ne_inr) hf₀Joint hord₀
  have hhyper₁Joint : IsHyperbolicElement
      (fun i => JQ.fam (Sum.inl i)) (eta (C.lox true)) :=
    isHyperbolicElement_of_mem_distinct_jointPeripheral JQ
      hJQinv hJQemb Sum.inl Sum.inr
      (fun _ _ => Sum.inl_ne_inr) hf₁Joint hord₁
  have hjointOriginal : (fun i => JQ.fam (Sum.inl i)) =
      (fun i => (Hfam i).map eta) := by
    funext i
    exact hJQinl i
  rw [hjointOriginal] at hhyper₀Joint hhyper₁Joint
  have hnc : ¬ OsinCommensurable (eta (C.lox false)) (eta (C.lox true)) :=
    not_osinCommensurable_of_mem_distinct_jointPeripherals JQ
      hJQinv hJQemb (by simp [i₀, i₁])
      hf₀Joint hf₁Joint hord₀
  have hinjPair : Set.InjOn eta
      ((D.cores.peripheral i₀ : Set G) ∪ (D.cores.peripheral i₁ : Set G)) := by
    intro x hx y hy hxy
    apply Pselected.injOn_peripheralUnion
    · rcases hx with hx | hx
      · exact Set.mem_iUnion.mpr ⟨i₀, hx⟩
      · exact Set.mem_iUnion.mpr ⟨i₁, hx⟩
    · rcases hy with hy | hy
      · exact Set.mem_iUnion.mpr ⟨i₀, hy⟩
      · exact Set.mem_iUnion.mpr ⟨i₁, hy⟩
    · exact hxy
  have hinter : ∀ q, q ∈ osinElementaryClosure (eta (C.lox false)) →
      q ∈ osinElementaryClosure (eta (C.lox true)) → q = 1 := by
    intro q hq₀ hq₁
    exact eq_one_of_preserved_osinElementaryClosures eta JQ
      hJQinv hJQemb (Sum.inr i₀) (Sum.inr i₁)
      (D.cores.peripheral i₀) (D.cores.peripheral i₁)
      (hJQinr i₀) (hJQinr i₁) hinjPair
      hf₀Peripheral hf₁Peripheral hord₀ hord₁
      (fun x hx₀ hx₁ => C.disjoint x hx₀ hx₁) hq₀ hq₁
  have hsuitable : IsOsin24SuitabilityConclusion Hfam H eta :=
    isOsin24SuitabilityConclusion_of_mapWitnesses eta
      (C.le false (C.lox_mem false)) (C.le true (C.lox_mem true))
      hhyper₀Joint hhyper₁Joint hord₀ hord₁ hnc hinter
  have htarget : ∀ x ∈ ({t} : Set G), eta x ∈ H.map eta := by
    intro x hx
    have hxt : x = t := Set.mem_singleton_iff.mp hx
    subst x
    have hrelator : eta (t⁻¹ * u) = 1 := by
      rw [← hval, ← MonoidHom.mem_ker, hker]
      exact Subgroup.subset_normalClosure rfl
    have hetau : eta t = eta u := by
      rw [map_mul, map_inv] at hrelator
      exact inv_mul_eq_one.mp hrelator
    rw [hetau]
    exact Subgroup.mem_map_of_mem eta hu
  have hquotient : IsOsin24Quotient Hfam H ({t} : Set G) Q eta :=
    ⟨hsurj, hrelative.1, htarget, hrelative.2, hsuitable, htorsion⟩
  have hkernelFinite : eta.ker.IsFinitelyNormallyGenerated := by
    refine ⟨{GGT.RelLetter.listVal v}, Set.finite_singleton _, ?_⟩
    exact hker.symm
  obtain ⟨BQ, hperiphMap, hactsMap, _hactsFamily⟩ :=
    HullSC.hullLemma58SuitableFamily_unconditional eta D Pselected
  have hnormalMap : HullSuitable.NormalizesNoNontrivialFinite (H.map eta) :=
    IsSuitableSubgroup.normalizesNoNontrivialFinite hsuitable
  have hHullSuitableMap : Suitable BQ.hullSet.alphabet (H.map eta) :=
    ⟨hactsMap, hnormalMap⟩
  have hnextAlphabet : Poriginal.rel.alphabet.carrier ⊆
      BQ.hullSet.alphabet.carrier := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ :=
      canonicalPreserved_alphabet_carrier_subset_image Poriginal hy
    rcases hx with hx | hx
    · exact BQ.alphabet_image x (B.rel_alphabet_subset hx)
    · exact hperiphMap x hx
  let Bnext : RelativeHullContinuationData
      (fun i => (Hfam i).map eta) (H.map eta) :=
    { rel := Poriginal.rel
      base_finite := Poriginal.base_finite B.base_finite
      fam_eq := by
        funext i
        rw [Poriginal.fam_map i, B.fam_eq]
      embedded := Poriginal.embedded
      hull := BQ.hullSet
      rel_alphabet_subset := hnextAlphabet
      suitable := hHullSuitableMap }
  exact ⟨Q, inferInstance, eta, hquotient, hkernelFinite, ⟨Bnext⟩⟩

end RelHyp
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.RelHyp.osin24HullStep_of_boundedLeaves
