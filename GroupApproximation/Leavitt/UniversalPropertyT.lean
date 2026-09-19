import GroupApproximation.PropertyT.FiniteTypeCharacteristicTwoPropertyT
import GroupApproximation.Leavitt.LeavittRankEquivalence
import GroupApproximation.Leavitt.UniversalRankFour

/-!
# Property `(T)` for the universal binary Leavitt compression groups

The universal binary Leavitt algebra is a finite-type `ZMod 2`-algebra, so the
general characteristic-two rank-three theorem applies directly. The explicit
Leavitt rank equivalence transfers property `(T)` to rank four.
-/

namespace GroupApproximation
namespace UniversalRankFour

universe v

/-- The universal-Leavitt rank-three core has property `(T)`, at every
representation-space universe. -/
theorem core_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, v} Core :=
  finiteTypeElementaryThree_hasKazhdanPropertyT.{v} (R := CoefficientRing)

/-- The universal-Leavitt rank-four ambient compression group has property
`(T)`, at every representation-space universe. -/
theorem ambient_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, v} Ambient :=
  family.rankFour_propertyT_of_rankThree core_hasKazhdanPropertyT

end UniversalRankFour
end GroupApproximation
