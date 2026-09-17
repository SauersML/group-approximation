import GroupApproximation.PropertyT.IntegralColumnPlaneClosure
import GroupApproximation.Meta.AxiomGuard

/-!
# nm-chain-14: the EJZ route through the free ring (carto re-audit)

`non_mf_groups_exist.tex`, proof of `prop:bilateral-three` (tex 1556):

> It is finitely generated, so $L=\EL_3(S)$ has property~\textup{(T)}.

## Audit (carto re-audit OK; bounded generation not used)

The repository proves EJZ Theorem 1.1 by the Ershov--Jaikin-Zapirain route, not by
Shalom--Vaserstein bounded generation:

1. **Column-plane mass bound over `ℤ⟨X⟩`.**
   `IntegralColumnPlaneClosure.integralFreeColumnPlaneMassBounds :
   IntegralFreeColumnPlaneMassBounds` is a closed theorem (no Statement parameter), audited
   with `#audit_closed_axioms` in `PropertyT/IntegralColumnPlaneClosure.lean`.
2. **Rank propagation.** `integralFreeColumnPlaneMassBounds_implies_freeIntegralGeneralRank`
   (`PropertyT/EJZIntegralGeneralRankReduction.lean:160`) pads the rank-three control
   estimate to every `n ≥ 3` and combines it with the unconditional root-subset Kazhdan
   constant from `A2MagicExponentFree`.
3. **Quotient step.** `freeIntegralGeneralRank_implies_finitelyGeneratedRingGeneralRank`
   (`PropertyT/EJZIntegralReduction.lean:50`) writes a finitely generated `A` as a quotient
   of a finite-rank free `ℤ`-algebra (`exists_finite_freeAlgebraInt_ringHom_surjection`),
   maps `EL_n` onto `EL_n` (`elementaryGroupMap_surjective_of_surjective`) and descends (T)
   along the surjection (`HasKazhdanPropertyT.of_surjective`).

A scan of the import closure of `IntegralColumnPlaneClosure` (110 modules) found no
Vaserstein, Shalom, or bounded-generation input.  The two theorems below re-derive the
endpoint along exactly these steps, so the chain is visible in one place.
-/

namespace GroupApproximation.Manuscript.NonMF.ChainCarto14

/-- Property (T) for `EL_n(ℤ⟨X⟩)`, every finite `X` and every `n ≥ 3`, from the closed
integral column-plane mass bound. -/
theorem freeIntegralGeneralRankElementaryPropertyT :
    GroupApproximation.FreeIntegralGeneralRankElementaryPropertyT :=
  GroupApproximation.integralFreeColumnPlaneMassBounds_implies_freeIntegralGeneralRank
    GroupApproximation.IntegralColumnPlaneClosure.integralFreeColumnPlaneMassBounds

#audit_axioms freeIntegralGeneralRankElementaryPropertyT

/-- EJZ Theorem 1.1 (tex 1556), descended from the free ring along the free-ring
surjection. -/
theorem finitelyGeneratedRingGeneralRankElementaryPropertyT_viaFreeRingQuotient :
    GroupApproximation.FinitelyGeneratedRingGeneralRankElementaryPropertyT :=
  GroupApproximation.freeIntegralGeneralRank_implies_finitelyGeneratedRingGeneralRank
    freeIntegralGeneralRankElementaryPropertyT

#audit_axioms finitelyGeneratedRingGeneralRankElementaryPropertyT_viaFreeRingQuotient

end GroupApproximation.Manuscript.NonMF.ChainCarto14
