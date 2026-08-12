import GroupApproximation.Endpoint.MainResults
import GroupApproximation.KOne.PaperStatements
import GroupApproximation.PropertyTT.PaperStatements

/-!
# A nonsofic group with property `(TT)/T`

This file intentionally sits outside the dependency closure of the rigidity
theorems.  It combines the `(TT)/T` endpoint proved in this development with the previously established
nonsoficity theorem for the same elementary group.  The nonsoficity input and
its proof mechanism belong to the prior OpenAI work; the conjunction below is
only a corollary.
-/

namespace GroupApproximation
namespace PropertyTTPaper

/-- For every `n ≥ 2`, the elementary group over the binary Leavitt algebra
over `F₂` has property `(TT)/T` and is nonsofic.

The `(TT)/T` assertion is the rigidity result of this development.  The
nonsoficity assertion is imported from the prior nonsofic-group theorem and is
not claimed here as a new proof or mechanism. -/
theorem binaryLeavitt_elementaryGroup_hasTTmodT_and_not_isSofic
    (n : ℕ) (hn : 2 ≤ n) :
    HasTTmodT.{0, 0}
        (elementaryGroup (Fin n) BinaryL) ∧
      ¬ IsSofic (elementaryGroup (Fin n) BinaryL) := by
  refine ⟨binaryLeavitt_elementaryGroup_hasTTmodT n hn, ?_⟩
  let d : BinaryLeavittUnits (ZMod 2) →*
      elementaryGroup (Fin 2) BinaryL :=
    MatrixDiagonalization.diagUnitHom.codRestrict
      (elementaryGroup (Fin 2) BinaryL)
      (fun u ↦ KOnePaper.diagUnit_mem_elementary (ZMod 2) u)
  have hd : Function.Injective d := by
    intro u v huv
    apply Units.ext
    have hentry := congrArg
      (fun M : elementaryGroup (Fin 2) BinaryL ↦
        ((M.1 : Matrix (Fin 2) (Fin 2) BinaryL) 0 0)) huv
    simpa [d, MatrixDiagonalization.diagUnitHom,
      MatrixDiagonalization.diagUnit] using hentry
  let e : elementaryGroup (Fin 2) BinaryL ≃*
      elementaryGroup (Fin n) BinaryL :=
    leavitt_elementaryRankEquivalence BinaryL
      (BinaryLeavitt.family (ZMod 2)) 2 n (by omega) hn
  let f : BinaryLeavittUnits (ZMod 2) →*
      elementaryGroup (Fin n) BinaryL :=
    e.toMonoidHom.comp d
  have hf : Function.Injective f := e.injective.comp hd
  intro hsofic
  exact binaryLeavittUnits_not_isSofic (ZMod 2)
    (isSofic_of_injective f hf hsofic)

end PropertyTTPaper
end GroupApproximation
