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

/-- For every `n ≥ 3`, the elementary group over the binary Leavitt algebra
over `F₂` has property `(TT)/T` and is nonsofic.

The `(TT)/T` assertion is the rigidity result of this development.  The
nonsoficity assertion is imported from the prior nonsofic-group theorem and is
not claimed here as a new proof or mechanism. -/
theorem binaryLeavitt_elementaryGroup_hasTTmodT_and_not_isSofic
    (n : ℕ) (hn : 3 ≤ n) :
    HasTTmodT.{0, 0}
        (elementaryGroup (Fin n) LeavittAllRanksTT.L) ∧
      ¬ IsSofic (elementaryGroup (Fin n) LeavittAllRanksTT.L) := by
  have hpositive : 1 ≤ n - 1 := by omega
  have hrank : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hnonsofic :
      ¬ IsSofic (BinaryLeavittEL (ZMod 2) (n - 1)) :=
    (binaryLeavitt_finiteField_profile (ZMod 2) (n - 1) hpositive).2.2.2
  refine ⟨binaryLeavitt_elementaryGroup_hasTTmodT n hn, ?_⟩
  rw [← hrank]
  exact hnonsofic

end PropertyTTPaper
end GroupApproximation
