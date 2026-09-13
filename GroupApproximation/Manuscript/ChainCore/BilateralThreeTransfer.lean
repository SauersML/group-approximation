import GroupApproximation.Manuscript.ChainCore.BilateralThreeStatement
import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudget
import GroupApproximation.Meta.AxiomGuard

/-!
# `prop:bilateral-three` as the transfer piece of `cor:dynamic-rank-budget`

`non_mf_groups_exist.tex`, proof of Proposition `prop:bilateral-three` (tex 1599–1600):

> If `R_X` is not directly finite, some defect is nonzero, so `GL_n(R_X)` is not MF.

and proof of Corollary `cor:dynamic-rank-budget` (tex 1760–1766):

> For other finite fields, if `R_X` is not directly finite then neither is `P_C` [...].
> Transfer one nonzero invisible defect root using Proposition~`prop:bilateral-three` in general
> linear rank `nr ≥ 3` [...].

The corollary's assembly (`DynamicRankBudget.printedDynamicRankBudget_of_pieces`, lane
ct-rank-budget) consumes the proposition through `DynamicRankBudget.BilateralThreeTransferStatement`:
over a finite field, if `R_X` is not directly finite then `GL_n(R_X)`, `n ≥ 3`, has a nontrivial
element in its MF radical.  The nontrivial element is the printed invisible root `e₂₁(d)` of a
nonzero compressed-clopen defect `d`, extended by identity.

* `exists_mem_mfHomKernel_ne_one_of_defect`: a nonzero defect gives a nontrivial element of
  `Rad_MF(GL_n(R_X))`, from the cell kill (`rootThree_killed_of_cell`) and extension by identity
  (`glThreeBlockEmbedding_elementaryUnit`);
* `bilateralThreeTransferStatement_of_pieces`: the transfer piece over the three-coordinate cell,
  countability of `R_X`, and "some defect is nonzero".
-/

namespace GroupApproximation
namespace Manuscript
namespace ChainCore
namespace BilateralThree

/-- **Printed (tex 1599–1600, 1763–1765):** a nonzero compressed-clopen defect `d` gives the
invisible root `e₂₁(d)` of `GL_n(R_X)`, `n ≥ 3`: a nontrivial element of the MF radical. -/
theorem exists_mem_mfHomKernel_ne_one_of_defect (hcell : BilateralThreeCellStatement)
    {X : Type} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Field k] [Finite k]
    [Countable (ClopenCrossedProduct T k)] {n : ℕ} (hn : 3 ≤ n)
    {d : ClopenCrossedProduct T k} (hd : d ∈ clopenDefectSet T k) (hne : d ≠ 0) :
    ∃ x ∈ MFQuotientUnits.mfHomKernel (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T k))ˣ,
      x ≠ 1 := by
  have hij : threeIdx hn 1 ≠ threeIdx hn 0 := (threeIdx_injective hn).ne idxOneNeZero
  refine ⟨elementaryUnit (threeIdx hn 1) (threeIdx hn 0) hij d, ?_, ?_⟩
  · rw [MFQuotientUnits.mem_mfHomKernel_iff]
    intro M _ hM f
    have h := rootThree_killed_of_cell hcell T k d hd M hM
      (f.comp (glThreeBlockEmbedding (R := ClopenCrossedProduct T k) hn))
    rwa [MonoidHom.comp_apply, glThreeBlockEmbedding_elementaryUnit] at h
  · intro h1
    exact hne (elementaryUnit_injective (threeIdx hn 1) (threeIdx hn 0) hij
      (h1.trans (elementaryUnit_zero (R := ClopenCrossedProduct T k)
        (threeIdx hn 1) (threeIdx hn 0) hij).symm))

/-- **`DynamicRankBudget.BilateralThreeTransferStatement` over the pieces of
`prop:bilateral-three`** (tex 1599–1600, 1763–1765): the three-coordinate cell, countability of
`R_X` (`DynamicRankBudget.CountableCrossedProductStatement`, the corollary's own spelling), and
"some defect is nonzero" (`ClopenCrossedProductNonzeroDefectStatement`). -/
theorem bilateralThreeTransferStatement_of_pieces (hcell : BilateralThreeCellStatement)
    (hcount : GroupApproximation.ChainCore.DynamicRankBudget.CountableCrossedProductStatement)
    (hdef : ClopenCrossedProductNonzeroDefectStatement) :
    GroupApproximation.ChainCore.DynamicRankBudget.BilateralThreeTransferStatement := by
  intro X _ _ _ _ T k _ _ n hn hdf
  haveI : Countable (ClopenCrossedProduct T k) := hcount X T k
  obtain ⟨d, hd, hne⟩ := hdef X T k hdf
  exact exists_mem_mfHomKernel_ne_one_of_defect hcell T k hn hd hne

end BilateralThree
end ChainCore
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.Manuscript.ChainCore.BilateralThree.exists_mem_mfHomKernel_ne_one_of_defect
#audit_axioms GroupApproximation.Manuscript.ChainCore.BilateralThree.bilateralThreeTransferStatement_of_pieces
