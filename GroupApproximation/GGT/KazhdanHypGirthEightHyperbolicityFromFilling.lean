import GroupApproximation.GGT.KazhdanHypGirthEightHyperbolicityBridge
import GroupApproximation.GGT.KazhdanHypLiteralFilling
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Hyperbolicity from the torsion lane's least literal discs

`KazhdanHypLiteralFilling.LeastLiteralDiscLocalData T` (P2) supplies, at a table
passing `GirthEightChecks`, a least-area disc with triangular local data for every
nonempty cyclically reduced trivial word.  Its first two conclusions are exactly
`KazhdanHypGirthEightLinearIsoperimetric.CyclicallyReducedLocalDataFilling T`, so
`GirthEightHyperbolicity` follows from P2 at every table through the linear
isoperimetric inequality and Gromov's theorem
(`KazhdanHypGirthEightHyperbolicityBridge.girthEightHyperbolicity_of_filling`).
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightHyperbolicityFromFilling

open GroupApproximation.KazhdanHyp
open KazhdanHypGirthEightLinearIsoperimetric

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- P2 at a checked table gives the filling input of the isoperimetric module. -/
theorem cyclicallyReducedLocalDataFilling_of_least
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (hleast : KazhdanHypLiteralFilling.LeastLiteralDiscLocalData T)
    (hchecks : GirthEightChecks T d) :
    CyclicallyReducedLocalDataFilling T := by
  intro word hne hcyc htriv
  obtain ⟨Delta, hbd, hloc, -⟩ := hleast d hchecks word hne hcyc htriv
  exact ⟨Delta, hbd, hloc⟩

end Table

/-- **`GirthEightHyperbolicity` from P2 at every table.** -/
theorem girthEightHyperbolicity_of_leastLiteralDiscLocalData
    (hleast : ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
      (_ : DecidableEq Generator) (_ : Fintype TriangleIndex)
      (_ : DecidableEq TriangleIndex)
      (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
      KazhdanHypLiteralFilling.LeastLiteralDiscLocalData T) :
    GirthEightHyperbolicity :=
  KazhdanHypGirthEightHyperbolicityBridge.girthEightHyperbolicity_of_filling
    (fun Generator TriangleIndex fg dg ft dt T _d hchecks =>
      cyclicallyReducedLocalDataFilling_of_least
        (hleast Generator TriangleIndex fg dg ft dt T) hchecks)

end KazhdanHypGirthEightHyperbolicityFromFilling
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightHyperbolicityFromFilling.cyclicallyReducedLocalDataFilling_of_least
#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightHyperbolicityFromFilling.girthEightHyperbolicity_of_leastLiteralDiscLocalData
