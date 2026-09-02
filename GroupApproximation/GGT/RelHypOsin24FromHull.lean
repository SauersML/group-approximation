import GroupApproximation.GGT.RelHypOsin24SuitabilityGlue
import GroupApproximation.GGT.RelHypOsin24Action
import GroupApproximation.GGT.RelHypOsin24ContinuationData
import GroupApproximation.GGT.RelHypOsin24Iteration
import GroupApproximation.GGT.HullSCAuxiliaryRelatorPublished
import GroupApproximation.GGT.HullSCLemma44FamilyInclusionStatement
import GroupApproximation.GGT.HullYiFiniteFamilyInduction

/-!
# The exact current Hull assembly boundary for Osin's Theorem 2.4

This module records the part of the proposed specialization that follows from
the current Hull interfaces without changing their statements.

`HullLemma44CanonicalQuotientFamilyStatement` specializes to the existing
canonical statement, which immediately implies the older
peripheral-preservation-only interface.  Combining the canonical Lemmas 4.4
and 4.9 with the one-sided Yi finite-avoidance theorem gives Hull's one-step
theorem.  The proved Theorem 3.16 assembly supplies the simultaneously
hyperbolically embedded elementary closures, so no `HeGXFamily` input remains.

No relator-selection hypothesis occurs: the exact published `C₁` relator is
already constructed unconditionally by
`exists_auxiliaryRelatorOfBaseLetterPublished_exact` in
`HullSCAuxiliaryRelatorPublished`.

The family Lemma 4.4 interface is the slot for Osin's arbitrary original
peripheral family.  Once `CompatibleRelativeHullActionStatement` supplies the
pre-quotient action on that same labelled relative alphabet, this module proves
the literal one-relator step and `RelHypOsin24Iteration` handles every finite
target set.  Thus the compatible action is the only additional input below;
all quotient conclusions and finite normal generation are proved here.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- The canonical form of Hull Lemma 4.4 contains the exact preserved-family
interface used by the earlier filling assembly; its additional conclusion is
injectivity on the requested Cayley ball. -/
theorem hullLemma44PreservedPeripheralFamily_of_family
    (h44family :
      HullSC.HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, 0}) :
    HullSC.HullLemma44PreservedPeripheralFamily.{u} := by
  have h44 : HullSC.HullLemma44CanonicalQuotientStatement.{u} :=
    HullSC.hullLemma44CanonicalQuotientStatement_of_familyInclusion h44family
  intro G _ A N k S D
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := h44 D 0
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hsurj hker
  obtain ⟨_hinj, hpreserve⟩ := hgood W q hinput hsurj hker
  exact hpreserve

/-- The exact generic Hull one-step theorem from the three shared lane inputs.
Yi finite avoidance supplies the finite Yi family, the proved Theorem 3.16
assembly constructs one jointly embedded auxiliary family, and the family
form of Lemma 4.4 specializes to the current canonical quotient theorem.
Lemma 4.9 and the published relator theorem then complete the literal
one-relator quotient. -/
theorem hullOneStepStatement_of_lemma44family_of_lemma49_of_yi
    (h44family :
      HullSC.HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{u, 0})
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{u}) :
    HullSC.HullOneStepStatement.{u} := by
  have hfiniteYi : HullSC.YiSuitableFiniteFamily.{u} :=
    HullSC.yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided.mpr hyi
  have hselect : HullSC.SimultaneousAuxiliaryPeripheralSelection.{u} :=
    HullSC.simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
      hfiniteYi
  have h44 : HullSC.HullLemma44CanonicalQuotientStatement.{u} :=
    HullSC.hullLemma44CanonicalQuotientStatement_of_familyInclusion h44family
  have hquot : HullSC.TorsionFreeHullCanonicalQuotientStatement.{u} :=
    HullSC.torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49
      hselect h44 h49
  intro G _ hG A N hN k S hS t R
  obtain ⟨D, eps, rho, mu, ht, hmu, hgood⟩ :=
    hquot hG A N hN S hS t R
  obtain ⟨u, hu, v, hval, hsc⟩ :=
    HullSC.AuxiliaryPeripheralFamily.exists_auxiliaryRelatorOfBaseLetterPublished_exact
      D hN t ht eps rho mu hmu
  obtain ⟨Q⟩ := hgood (HullSC.RelWord.symmetrized v) v
    (HullSC.RelWord.self_mem_symmetrized v) hsc
  have hrel : Q.q (t⁻¹ * u) = 1 := by
    rw [← hval, ← MonoidHom.mem_ker, Q.ker_eq]
    exact Subgroup.subset_normalClosure rfl
  have hqt : Q.q t = Q.q u := by
    rw [map_mul, map_inv] at hrel
    exact inv_mul_eq_one.mp hrel
  refine ⟨{ step := Q.toHullStep
            mem_map := ?_
            kerNormallyGenerated := ⟨{t⁻¹ * u}, by simp, ?_⟩ }⟩
  · intro _
    show Q.q t ∈ N.map Q.q
    rw [hqt]
    exact Subgroup.mem_map_of_mem _ hu
  · show Q.q.ker =
      Subgroup.normalClosure ((({t⁻¹ * u} : Finset G)) : Set G)
    rw [Q.ker_eq, hval, Finset.coe_singleton]

/-! ## The relatively hyperbolic one-target specialization -/

/-- One literal Hull filling step together with the relative/Hull data needed
to apply the construction again in its quotient. -/
def Osin24HullStepConclusion
    {G : Type} [Group G] {I : Type} (Hfam : I → Subgroup G)
    (H : Subgroup G) (t : G) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (eta : G →* Q),
    IsOsin24Quotient Hfam H ({t} : Set G) Q eta ∧
      eta.ker.IsFinitelyNormallyGenerated ∧
        Nonempty (RelativeHullContinuationData
          (fun i => (Hfam i).map eta) (H.map eta))

/-- The arbitrary-family Lemma 4.4, Lemma 4.9, and Yi selection give the
one-target Osin quotient from compatible relative Hull data.  The quotient is
the literal quotient by Hull's one relator `t⁻¹u`, so finite normal generation
is part of the construction.  Hull Lemma 5.8 supplies a quotient Hull alphabet,
and Osin suitability supplies its finite-normalizer clause, so the output can
be iterated. -/
theorem osin24HullStep_of_data
    (h44family :
      HullSC.HullLemma44CanonicalQuotientFamilyInclusionStatement.{0, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{0, 0})
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{0})
    {G : Type} [Group G] {I : Type} {Hfam : I → Subgroup G}
    {H : Subgroup G} (B : RelativeHullContinuationData Hfam H) (t : G) :
    Osin24HullStepConclusion Hfam H t := by
  have hfiniteYi : HullSC.YiSuitableFiniteFamily.{0} :=
    HullSC.yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided.mpr hyi
  have hselect : HullSC.SimultaneousAuxiliaryPeripheralSelection.{0} :=
    HullSC.simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
      hfiniteYi
  let emptyFamily : Fin 0 → Subgroup G := Fin.elim0
  obtain ⟨D₀⟩ := hselect B.hull emptyFamily B.suitable (by
    intro j
    exact Fin.elim0 j)
  obtain ⟨D, htBase, hacyD⟩ := D₀.exists_acylindricalAdjoinPair t
  have hOriginalAlphabet : B.rel.alphabet.carrier ⊆
      B.hull.alphabet.carrier := B.rel_alphabet_subset
  obtain ⟨eps₄₄, rho₄₄, mu₄₄, hmu₄₄, hgood₄₄⟩ :=
    h44family D B.rel hOriginalAlphabet B.embedded 1
  obtain ⟨eps₄₉, rho₄₉, mu₄₉, hmu₄₉, hgood₄₉⟩ :=
    h49 D.rel D.embedded hacyD
  let eps := max eps₄₄ eps₄₉
  let rho := max rho₄₄ rho₄₉
  let mu := min mu₄₄ mu₄₉
  have hmu : 0 < mu := lt_min hmu₄₄ hmu₄₉
  obtain ⟨u, hu, v, hval, hsc⟩ :=
    HullSC.AuxiliaryPeripheralFamily.exists_auxiliaryRelatorOfBaseLetterPublished_exact
      D B.suitable t htBase eps rho mu hmu
  let W := HullSC.RelWord.symmetrized v
  let K : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  let Q : Type 0 := HasQuotient.Quotient G K
  let eta : G →* Q := QuotientGroup.mk' K
  have hsurj : Function.Surjective eta := QuotientGroup.mk'_surjective K
  have hker : eta.ker = K := QuotientGroup.ker_mk' K
  have hvW : v ∈ W := HullSC.RelWord.self_mem_symmetrized v
  have hsc₄₄ : HullSC.RelWord.IsLemma44Input D.rel W eps₄₄ mu₄₄ rho₄₄ :=
    hsc.toIsLemma44Input.mono_parameters
      (Nat.le_max_left _ _) (min_le_left _ _) (Nat.le_max_left _ _)
  have hsc₄₉ : HullSC.RelWord.IsLemma49Input D.rel W eps₄₉ mu₄₉ rho₄₉ :=
    hsc.mono_parameters
      (Nat.le_max_right _ _) (min_le_right _ _) (Nat.le_max_right _ _)
  have hkerW : eta.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) := by
    rw [hker, HullSC.RelWord.normalClosure_listVal_image_symmetrized]
  obtain ⟨_hball, ⟨Pselected⟩, ⟨Poriginal⟩, ⟨Pjoint⟩⟩ :=
    hgood₄₄ W eta hsc₄₄ hsurj hkerW
  have hpower : HullSC.KernelPowerCorrection K :=
    hgood₄₉ W v hvW hsc₄₉
  have htorsion : IsOsin24TorsionConclusion eta := by
    apply isOsin24TorsionConclusion_of_kernelPowerCorrection eta hsurj
    rwa [hker]
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
  have hf₀Joint : eta (C.lox false) ∈ Pjoint.rel.fam (Sum.inr i₀) := by
    rw [Pjoint.fam_selected i₀]
    exact Subgroup.mem_map_of_mem eta hf₀Peripheral
  have hf₁Joint : eta (C.lox true) ∈ Pjoint.rel.fam (Sum.inr i₁) := by
    rw [Pjoint.fam_selected i₁]
    exact Subgroup.mem_map_of_mem eta hf₁Peripheral
  have hhyper₀Joint : IsHyperbolicElement
      (fun i => Pjoint.rel.fam (Sum.inl i)) (eta (C.lox false)) :=
    isHyperbolicElement_of_mem_distinct_jointPeripheral Pjoint.rel
      Pjoint.base_inv Pjoint.embedded Sum.inl Sum.inr
      (fun _ _ => Sum.inl_ne_inr) hf₀Joint hord₀
  have hhyper₁Joint : IsHyperbolicElement
      (fun i => Pjoint.rel.fam (Sum.inl i)) (eta (C.lox true)) :=
    isHyperbolicElement_of_mem_distinct_jointPeripheral Pjoint.rel
      Pjoint.base_inv Pjoint.embedded Sum.inl Sum.inr
      (fun _ _ => Sum.inl_ne_inr) hf₁Joint hord₁
  have hjointOriginal : (fun i => Pjoint.rel.fam (Sum.inl i)) =
      (fun i => (Hfam i).map eta) := by
    funext i
    rw [Pjoint.fam_original i, B.fam_eq]
  rw [hjointOriginal] at hhyper₀Joint hhyper₁Joint
  have hnc : ¬ OsinCommensurable (eta (C.lox false)) (eta (C.lox true)) :=
    not_osinCommensurable_of_mem_distinct_jointPeripherals Pjoint.rel
      Pjoint.base_inv Pjoint.embedded (by simp [i₀, i₁])
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
    exact eq_one_of_preserved_osinElementaryClosures eta Pjoint.rel
      Pjoint.base_inv Pjoint.embedded (Sum.inr i₀) (Sum.inr i₁)
      (D.cores.peripheral i₀) (D.cores.peripheral i₁)
      (Pjoint.fam_selected i₀) (Pjoint.fam_selected i₁) hinjPair
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
  obtain ⟨BQ, hactsMap, _hactsFamily⟩ :=
    HullSC.hullLemma58SuitableFamily_unconditional eta D Pselected
  have hnormalMap : HullSuitable.NormalizesNoNontrivialFinite (H.map eta) :=
    IsSuitableSubgroup.normalizesNoNontrivialFinite hsuitable
  have hHullSuitableMap : Suitable BQ.hullSet.alphabet (H.map eta) :=
    ⟨hactsMap, hnormalMap⟩
  have hnextAlphabet : Poriginal.rel.alphabet.carrier ⊆
      BQ.hullSet.alphabet.carrier := by
    rw [canonicalPreserved_alphabet_carrier_eq_image Poriginal]
    rintro y ⟨x, hx, rfl⟩
    exact BQ.alphabet_image x (B.rel_alphabet_subset hx)
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

/-- A compatible-action producer specializes the reusable Hull-data step to
the singleton statement used by the general finite induction. -/
theorem osin24SingletonStep_of_hull_of_compatibleAction
    (h44family :
      HullSC.HullLemma44CanonicalQuotientFamilyInclusionStatement.{0, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{0, 0})
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{0})
    (haction : CompatibleRelativeHullActionStatement.{0, 0}) :
    Osin24SingletonStepStatement := by
  intro G instG I Hfam hrel H hsuit t
  letI : Group G := instG
  obtain ⟨B⟩ := haction G instG I Hfam hrel H hsuit
  obtain ⟨Q, instQ, eta, hquotient, hkernel, _hnext⟩ :=
    osin24HullStep_of_data h44family h49 hyi B.toContinuation t
  exact ⟨Q, instQ, eta, hquotient, hkernel⟩

/-- Finite iteration turns the conditional one-target specialization into the
full finite-presentation addendum. -/
theorem osinTheorem24FinitePresentationAddendum_of_hull_of_compatibleAction
    (h44family :
      HullSC.HullLemma44CanonicalQuotientFamilyInclusionStatement.{0, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{0, 0})
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{0})
    (haction : CompatibleRelativeHullActionStatement.{0, 0}) :
    OsinTheorem24FinitePresentationAddendum :=
  osinTheorem24FinitePresentationAddendum_of_singletonStep
    (osin24SingletonStep_of_hull_of_compatibleAction h44family h49 hyi haction)

end RelHyp
end GGT
end GroupApproximation
