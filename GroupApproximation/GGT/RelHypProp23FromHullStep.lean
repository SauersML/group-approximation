import GroupApproximation.GGT.RelHypOsin24PublishedHullStep
import GroupApproximation.GGT.RelHypProp23FromHullOsin24
import GroupApproximation.Meta.AxiomGuard

/-!
# Fournier--Facio Proposition 2.3 from the one-target Osin step

`GGT/RelHypOsin24HullIteration.lean`, `GGT/RelHypOsin24FreeProductIteration.lean` and
`GGT/RelHypProp23FromHullOsin24.lean` thread the three Hull inputs into `osin24HullStep_of_data` and
nowhere else.  This module restates the three over the step itself, `Osin24HullStepStatement`, so
that any producer of the step serves:

* `exists_osin24Quotient_of_hullStep` — one relator per target, over a finite target set;
* `exists_osin24Quotient_freeProduct_of_hullStep` — the free product `U ∗ H` of Proposition 2.3;
* `fournierFacioProposition23_of_hullStep`, `fournierFacioQuotientStatement_of_hullStep`.

The Yi pair used for suitability of the hyperbolic factor is the closed finite-avoidance theorem.
`fournierFacioQuotientStatement_of_boundedLeaves` is the manuscript quotient field on the step at
Hull's published relator (`osin24HullStep_of_boundedLeaves`).
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI

/-- A finite target set can be filled from one compatible continuation datum, using one step per
target. -/
theorem exists_osin24Quotient_of_hullStep (hstep : Osin24HullStepStatement)
    {G : Type} [Group G] {I : Type} (Hfam : I → Subgroup G)
    (hrel : IsRelativelyHyperbolic G Hfam) (H : Subgroup G)
    (hsuit : IsSuitableSubgroup Hfam H)
    (B : RelativeHullContinuationData Hfam H)
    (targets : Set G) (htargets : targets.Finite) :
    ∃ (Q : Type) (_ : Group Q) (eta : G →* Q),
      IsOsin24Quotient Hfam H targets Q eta ∧
        eta.ker.IsFinitelyNormallyGenerated := by
  classical
  have hind : ∀ s : Finset G,
      ∃ (Q : Type) (_ : Group Q) (eta : G →* Q),
        IsOsin24Quotient Hfam H (s : Set G) Q eta ∧
          eta.ker.IsFinitelyNormallyGenerated ∧
            Nonempty (RelativeHullContinuationData
              (fun i => (Hfam i).map eta) (H.map eta)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        refine ⟨G, inferInstance, MonoidHom.id G, ?_⟩
        have hmodel := osin24SingletonStep_identityModel Hfam hrel H hsuit
          (t := (1 : G)) H.one_mem
        obtain ⟨hone, hker⟩ := hmodel
        obtain ⟨hsurj, hrelQ, _htarget, hinj, hsuitQ, htorsion⟩ := hone
        refine ⟨⟨hsurj, hrelQ, ?_, hinj, hsuitQ, htorsion⟩, hker, ?_⟩
        · intro x hx
          cases hx
        · simpa only [Subgroup.map_id] using (show
            Nonempty (RelativeHullContinuationData Hfam H) from ⟨B⟩)
    | @insert a s ha ih =>
        obtain ⟨Q, instQ, phi, hphi, hkerPhi, ⟨BQ⟩⟩ := ih
        letI : Group Q := instQ
        obtain ⟨P, instP, psi, hpsi, hkerPsi, ⟨BP⟩⟩ := hstep BQ (phi a)
        letI : Group P := instP
        refine ⟨P, instP, psi.comp phi, ?_, ?_, ?_⟩
        · simpa only [Finset.coe_insert] using
            isOsin24Quotient_comp_insert Hfam H (s : Set G) a
              phi psi hphi hpsi
        · exact ker_comp_isFinitelyNormallyGenerated phi hphi.1 psi
            hkerPhi hkerPsi
        · simpa only [Subgroup.map_map] using (show
            Nonempty (RelativeHullContinuationData
              (fun i => ((Hfam i).map phi).map psi)
              ((H.map phi).map psi)) from ⟨BP⟩)
  obtain ⟨Q, instQ, eta, hq, hker, _hnext⟩ := hind htargets.toFinset
  exact ⟨Q, instQ, eta,
    by simpa only [Set.Finite.coe_toFinset] using hq, hker⟩

/-- Osin's finite-target quotient conclusion for the free-product configuration of Fournier--Facio
Proposition 2.3, from the one-target step. -/
theorem exists_osin24Quotient_freeProduct_of_hullStep (hstep : Osin24HullStepStatement)
    (U H : Type) [Group U] [Group H]
    (hhyp : Hyperbolic.IsHyperbolicGroup H)
    (hsuit : IsSuitableSubgroup
      (fun _ : Unit => freeProductPeripheral U H)
      (MonoidHom.range (freeProductPartnerHom U H)))
    (targets : Set (CoprodI (pairFamily U H))) (htargets : targets.Finite) :
    ∃ (Q : Type) (_ : Group Q)
        (eta : CoprodI (pairFamily U H) →* Q),
      IsOsin24Quotient
          (fun _ : Unit => freeProductPeripheral U H)
          (MonoidHom.range (freeProductPartnerHom U H)) targets Q eta ∧
        eta.ker.IsFinitelyNormallyGenerated := by
  have hrel : IsRelativelyHyperbolic (CoprodI (pairFamily U H))
      (fun _ : Unit => freeProductPeripheral U H) :=
    freeProductRelativelyHyperbolicStatement_proved U H inferInstance
      inferInstance hhyp
  obtain ⟨B⟩ := nonempty_relativeHullData_freeProduct U H hhyp hsuit
  exact exists_osin24Quotient_of_hullStep hstep
    (fun _ : Unit => freeProductPeripheral U H) hrel
    (MonoidHom.range (freeProductPartnerHom U H)) hsuit B.toContinuation
    targets htargets

/-- **Fournier--Facio Proposition 2.3 from the one-target Osin step.** -/
theorem fournierFacioProposition23_of_hullStep (hstep : Osin24HullStepStatement) :
    FournierFacioProposition23 := by
  have hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{0} :=
    HullSC.yiSuitablePairAvoidingFiniteOneSided_of_dgoLemma421b
      (GGT.OsinComponents.dgoLemma421b_of_uniform414
        GGT.OsinComponents.dgoProposition414Uniform)
  have hpair : HyperbolicNonCommensurablePairStatement :=
    hyperbolicNonCommensurablePairStatement_of_yi
      (yiSuitablePair_of_avoidingFiniteOneSided hyi)
  have hSuit : HyperbolicSuitabilityStatement :=
    hyperbolicSuitabilityStatement_of_nonCommensurablePair hpair
  intro K Lam instK instLam hne htfLam hfpK htfK g hgfin
  haveI := hfpK
  haveI : Group.IsFinitelyPresented Lam :=
    @Hyperbolic.isFinitelyPresented_of_isHyperbolicGroup Lam instLam hne.1
  have hsuit : IsSuitableSubgroup
      (fun _ : Unit => freeProductPeripheral K Lam)
      (MonoidHom.range (freeProductPartnerHom K Lam)) :=
    @isSuitableSubgroup_freeProduct_of_hyperbolicSuitability hSuit K Lam instK
      instLam hne htfLam
  obtain ⟨Q, instQ, eta, hquot, hker⟩ :=
    exists_osin24Quotient_freeProduct_of_hullStep hstep K Lam hne.1
      hsuit g hgfin
  have hsourceTf : IsPowerTorsionFree
      (Monoid.CoprodI (pairFamily K Lam)) :=
    OsinWeightedMetric.isPowerTorsionFree_coprodI
      (isPowerTorsionFree_pairFamily htfK htfLam)
  have hQtf : IsPowerTorsionFree Q := hquot.isPowerTorsionFree hsourceTf
  obtain ⟨hsurj, -, hmem, hinjOn, -, -⟩ := hquot
  refine ⟨Q, instQ, eta, hsurj, ?_, hQtf, ?_, ?_⟩
  · exact Group.IsFinitelyPresented.of_surjective eta hsurj hker
  · intro a b hab
    have hmemA :
        (freeProductSourceHom K Lam a : Monoid.CoprodI (pairFamily K Lam))
          ∈ ⋃ _ : Unit,
            ((freeProductPeripheral K Lam :
              Subgroup (Monoid.CoprodI (pairFamily K Lam))) :
                Set (Monoid.CoprodI (pairFamily K Lam))) :=
      Set.mem_iUnion.mpr ⟨(), ⟨a, rfl⟩⟩
    have hmemB :
        (freeProductSourceHom K Lam b : Monoid.CoprodI (pairFamily K Lam))
          ∈ ⋃ _ : Unit,
            ((freeProductPeripheral K Lam :
              Subgroup (Monoid.CoprodI (pairFamily K Lam))) :
                Set (Monoid.CoprodI (pairFamily K Lam))) :=
      Set.mem_iUnion.mpr ⟨(), ⟨b, rfl⟩⟩
    exact Monoid.CoprodI.of_injective false (hinjOn hmemA hmemB hab)
  · intro x hx
    have h := hmem x hx
    rwa [← MonoidHom.range_comp] at h

/-- The manuscript quotient field from the one-target Osin step. -/
theorem fournierFacioQuotientStatement_of_hullStep (hstep : Osin24HullStepStatement) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement :=
  fournierFacioQuotientStatement_of_prop23 (fournierFacioProposition23_of_hullStep hstep)

/-- **The manuscript quotient field at Hull's published relator**: the bounded canonical Lemma 4.4,
Osin's Lemma 5.1 in image form and Lemma 4.9, with no re-spelling admission. -/
theorem fournierFacioQuotientStatement_of_boundedLeaves
    (h44 : HullSC.BoundedHullLemma44CanonicalQuotientStatement.{0})
    (hemb : HullSC.BoundedImageEmbeddingStatement.{0, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{0, 0}) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement :=
  fournierFacioQuotientStatement_of_hullStep (osin24HullStep_of_boundedLeaves h44 hemb h49)

end RelHyp
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.RelHyp.exists_osin24Quotient_of_hullStep
#audit_axioms GroupApproximation.GGT.RelHyp.exists_osin24Quotient_freeProduct_of_hullStep
#audit_axioms GroupApproximation.GGT.RelHyp.fournierFacioProposition23_of_hullStep
#audit_axioms GroupApproximation.GGT.RelHyp.fournierFacioQuotientStatement_of_hullStep
#audit_axioms GroupApproximation.GGT.RelHyp.fournierFacioQuotientStatement_of_boundedLeaves
