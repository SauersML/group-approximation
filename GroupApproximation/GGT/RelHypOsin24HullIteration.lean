import GroupApproximation.GGT.RelHypOsin24FromHull

/-!
# Iterating Hull fillings while retaining the relative structure

`osin24HullStep_of_data` returns a quotient Hull alphabet, the mapped suitable
subgroup, and the image of the original finite-base relative structure.  This
module iterates that output over a finite target set.

The quotient clauses compose by `isOsin24Quotient_comp_insert`.  Finite normal
generation composes by `ker_comp_isFinitelyNormallyGenerated`.  The only new
bookkeeping is the continuation record: `Subgroup.map_map` identifies the
twice-mapped family with the family mapped by the composite quotient.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

/-- A finite target set can be filled from one compatible continuation datum,
using one constructed relator per target. -/
theorem exists_osin24Quotient_of_hullContinuation
    (h44family :
      HullSC.HullLemma44CanonicalQuotientFamilyInclusionStatement.{0, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{0, 0})
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{0})
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
        obtain ⟨P, instP, psi, hpsi, hkerPsi, ⟨BP⟩⟩ :=
          osin24HullStep_of_data h44family h49 hyi BQ (phi a)
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

end RelHyp
end GGT
end GroupApproximation
