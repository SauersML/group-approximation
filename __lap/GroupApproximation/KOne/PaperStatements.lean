import GroupApproximation.KOne.RefineLoopDischarge

/-!
# Paper statements for unstable elementary generation

These declarations isolate the finite-rank information used by the property
`(TT)/T` paper.  Stable `K₁`-vanishing for binary Leavitt algebras is known
from the Leavitt-path-algebra `K`-theory literature.  Together with the
GE-ring and unit-abelianization theorems for purely infinite simple rings, it
also implies the unstable rank-two equality below.  No priority is claimed
for that equality.
-/

namespace GroupApproximation
namespace KOnePaper

open BinaryLeavitt
open MatrixDiagonalization

variable (k : Type) [Field k]

/-- Every unit of the binary Leavitt algebra has elementary diagonal
stabilization already in rank two. -/
theorem diagUnit_mem_elementary
    [Nontrivial (BinaryLeavittAlgebra k)]
    (u : (BinaryLeavittAlgebra k)ˣ) :
    diagUnit u ∈ elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) :=
  (mem_stableUnits_iff u).mp (K1_trivial k u)

/-- The unstable rank-two statement conventionally written
`GL₂(L_k(1,2)) = E₂(L_k(1,2))`. -/
theorem elementaryGroup_two_eq_top
    [Nontrivial (BinaryLeavittAlgebra k)] :
    elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) = ⊤ := by
  apply le_antisymm le_top
  intro M _
  exact glTwo_eq_elementary_holds k M

end KOnePaper
end GroupApproximation
