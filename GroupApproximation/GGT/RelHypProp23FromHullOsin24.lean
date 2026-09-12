import GroupApproximation.GGT.RelHypOsin24FreeProductIteration
import GroupApproximation.GGT.RelHypFournierFacioProp23SharpReduction

/-!
# Fournier--Facio Proposition 2.3 from the Hull realization of Osin 2.4

The free-product action and finite quotient iteration give exactly the Osin
quotient needed by Fournier--Facio Proposition 2.3.  The finite-avoidance Yi
statement also specializes to the two-element Yi statement, which supplies
the non-commensurable pair used to prove suitability of the hyperbolic factor.

Thus the proposition and the manuscript quotient field use only the three
Hull inputs: arbitrary-family Lemma 4.4, kernel-power Lemma 4.9, and Yi's
finite-avoidance pair.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid

/-- Fournier--Facio Proposition 2.3 from the family form of Hull Lemma 4.4,
Hull Lemma 4.9, and Yi's finite-avoidance pair. -/
theorem fournierFacioProposition23_of_hull_osin24
    (h44family :
      HullSC.HullLemma44CanonicalQuotientFamilyInclusionStatement.{0, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{0, 0})
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{0}) :
    FournierFacioProposition23 := by
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
    exists_osin24Quotient_freeProduct_of_hull h44family h49 hyi K Lam hne.1
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

/-- The manuscript quotient field from the same three Hull inputs. -/
theorem fournierFacioQuotientStatement_of_hull_osin24
    (h44family :
      HullSC.HullLemma44CanonicalQuotientFamilyInclusionStatement.{0, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{0, 0})
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{0}) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement :=
  fournierFacioQuotientStatement_of_prop23
    (fournierFacioProposition23_of_hull_osin24 h44family h49 hyi)

end RelHyp
end GGT
end GroupApproximation
