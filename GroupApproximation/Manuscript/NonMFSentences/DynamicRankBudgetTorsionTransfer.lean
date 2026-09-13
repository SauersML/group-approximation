import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudget
import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents
import GroupApproximation.Leavitt.ElementaryNoFiniteQuotients
import GroupApproximation.Leavitt.CongruenceSubgroups
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the elementary transfer over other finite fields

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`, tex 1760–1766:

> For other finite fields, if $R_X$ is not directly finite then neither
> is $P_C$ ... Transfer one nonzero invisible defect root using
> Proposition~\ref{prop:bilateral-three} in general linear rank $nr\ge3$,
> or Proposition~\ref{prop:torsion-defect-ring} in elementary rank
> $nr\ge4$.

This module proves the elementary half, `TorsionDefectTransferStatement`, from the closed
`manuscriptTorsionComplementaryIdempotents` (Proposition `prop:torsion-defect-ring`):

* a ring that is not directly finite has `t s = 1` and `e = 1 - s t ≠ 0`;
* over a finite coefficient field every element of `R_X` has finite additive order
  (`ringChar_nsmul_eq_zero`), so `e` does;
* `prop:torsion-defect-ring` puts `EL_n(R_X, R e R)` in the MF radical of `EL_n(R_X)`, `n ≥ 4`, and
  its root `e_{21}(e)` is not the identity.

`printedDynamicRankBudget_of_residuals` is the printed assembly with this piece discharged.
-/

namespace GroupApproximation
namespace ChainCore
namespace DynamicRankBudget

open MFQuotientUnits Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents

/-- Over a finite coefficient ring `k`, `char k` annihilates every element of `R_X`. -/
theorem ringChar_nsmul_eq_zero {X : Type} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Ring k]
    (x : ClopenCrossedProduct T k) : ringChar k • x = 0 := by
  have hk : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k (ringChar k)
  have hR : ((ringChar k : ℕ) : ClopenCrossedProduct T k) = 0 := by
    rw [← map_natCast ((ClopenCrossedProduct.coeff T k).comp
      (LocallyConstant.constRingHom : k →+* LocallyConstant X k)) (ringChar k), hk, map_zero]
  rw [nsmul_eq_mul, hR, zero_mul]

/-- **`prop:torsion-defect-ring` transferred to `R_X`** (tex 1765): over a finite field, if `R_X`
is not directly finite, then `EL_n(R_X)`, `n ≥ 4`, has a nontrivial element in its MF radical. -/
theorem torsionDefectTransferStatement_of_countable (hCount : CountableCrossedProductStatement) :
    TorsionDefectTransferStatement := by
  intro X _ _ _ _ T k _ _ n hn hnot
  haveI := hCount X T k
  obtain ⟨t, s, hts, hst⟩ : ∃ t s : ClopenCrossedProduct T k, t * s = 1 ∧ s * t ≠ 1 := by
    by_contra h
    push Not at h
    exact hnot ⟨fun {a b} hab ↦ h a b hab⟩
  have he : (1 : ClopenCrossedProduct T k) - s * t ≠ 0 := sub_ne_zero.mpr (Ne.symm hst)
  have hfin : ∃ m : ℕ, 1 ≤ m ∧ m • (1 - s * t) = 0 :=
    ⟨ringChar k, Nat.one_le_iff_ne_zero.mpr (CharP.char_ne_zero_of_finite (R := k) (ringChar k)),
      ringChar_nsmul_eq_zero T k _⟩
  have hle := (manuscriptTorsionComplementaryIdempotents (ClopenCrossedProduct T k) s t hts
    hfin).1 n hn
  have h01 : (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := Fin.ne_of_val_ne (by norm_num)
  refine ⟨elGen (⟨1, by omega⟩ : Fin n) ⟨0, by omega⟩ h01 (1 - s * t), hle ?_, ?_⟩
  · exact elGen_mem_relativeElementary _ _ h01 (TwoSidedIdeal.subset_span (Set.mem_singleton _))
  · intro h1
    apply he
    have h2 := congrArg Subtype.val h1
    have hval : elementaryUnit (⟨1, by omega⟩ : Fin n) ⟨0, by omega⟩ h01 (1 - s * t) =
        elementaryUnit (⟨1, by omega⟩ : Fin n) ⟨0, by omega⟩ h01 0 := by
      rw [elementaryUnit_zero]
      exact h2
    exact elementaryUnit_injective _ _ h01 hval

/-- **The proof of `cor:dynamic-rank-budget`, with the elementary transfer discharged.** -/
theorem printedDynamicRankBudget_of_residuals (hRefl : CoreRingReflectionStatement)
    (hModels : CoreModelsLEFStatement) (hCount : CountableCrossedProductStatement)
    (hRad : CoreMFRadicalKillStatement) (hBil : BilateralThreeTransferStatement)
    (hUnitLF : UnitKernelLocallyFiniteStatement) (hTower : ReturnEmbeddingStatement) :
    PrintedDynamicRankBudget :=
  printedDynamicRankBudget_of_pieces hRefl hModels hCount hRad hBil
    (torsionDefectTransferStatement_of_countable hCount) hUnitLF hTower

end DynamicRankBudget
end ChainCore
end GroupApproximation

/-! ### Audit -/

#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.ringChar_nsmul_eq_zero
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.torsionDefectTransferStatement_of_countable
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.printedDynamicRankBudget_of_residuals
