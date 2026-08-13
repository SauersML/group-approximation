import GroupApproximation.Endpoint.MainResults
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
  intro hsofic
  exact binaryLeavittUnits_not_isSofic (ZMod 2)
    ((isSofic_mulEquiv_iff
      (binaryLeavitt_elementaryEquivUnits n hn)).mp hsofic)

end PropertyTTPaper
end GroupApproximation
