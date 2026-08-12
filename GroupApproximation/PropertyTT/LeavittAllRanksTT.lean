import GroupApproximation.PropertyTT.FiniteTypeLeavittTT
import GroupApproximation.Leavitt.UniversalLeavitt

/-!
# Property `(TT)/T` in every rank over the binary Leavitt algebra

The binary Leavitt algebra discharges the four structural hypotheses of the
general finite-type Leavitt theorem: its four-generator quotient
presentation, matrix self-similarity, single-sandwich division, and trivial
elementary diagonal class.
-/

namespace GroupApproximation
namespace LeavittAllRanksTT

abbrev L := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

/-- **All-ranks theorem.** For every `n ≥ 2`, the elementary group
`ELₙ(L_{𝔽₂}(1,2))` has property `(TT)/T`.

Every hypothesis used here is discharged inside the Lean development: the
rank-four theorem has no external rigidity premise, and the rank transport is
the explicit prefix-code equivalence for the binary Leavitt algebra. -/
theorem elementaryGroup_hasTTmodT (n : ℕ) (hn : 2 ≤ n) :
    HasTTmodT.{0, 0} (elementaryGroup (Fin n) L) := by
  exact FiniteTypeLeavittTT.elementaryGroup_hasTTmodT
    BinaryLeavitt.Generator
    (BinaryLeavitt.quotientMap (ZMod 2)).toRingHom
    (RingQuot.mkAlgHom_surjective (ZMod 2)
      (BinaryLeavitt.Relation (ZMod 2)))
    (BinaryLeavitt.family (ZMod 2))
    (BinaryLeavitt.hasSingleSandwichDivision (ZMod 2))
    (BinaryLeavitt.hasElementaryDiagonalClass (ZMod 2))
    n hn

end LeavittAllRanksTT
end GroupApproximation
