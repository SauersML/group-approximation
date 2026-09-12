import GroupApproximation.GGT.KazhdanHypGirthEightLinearIsoperimetric
import GroupApproximation.Algebra.LinearIsoperimetricHyperbolic
import GroupApproximation.Meta.AxiomGuard

/-!
# Gromov's theorem discharges the hyperbolicity statement

`KazhdanHypGirthEightLinearIsoperimetric.lean` proves `GirthEightHyperbolicity`
from two inputs: the local-data filling of cyclically reduced trivial words, and
`LinearIsoperimetricHyperbolicityStatement`, Gromov's theorem that a finite
presentation with a linear isoperimetric inequality presents a hyperbolic group.
The second input is `DiscreteStokes.isHyperbolicGroup_presentedGroup_of_linearIsoperimetric`
(`Algebra/LinearIsoperimetricHyperbolic.lean`), whose lower area bound is the
discrete Stokes inequality and whose metric step is Bowditch's slim-triangle
criterion.  This module identifies the two, so `GirthEightHyperbolicity`
rests on the filling input alone.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightHyperbolicityBridge

open GroupApproximation.KazhdanHyp
open KazhdanHypGirthEightLinearIsoperimetric

/-- **Gromov's theorem, in the form the girth-eight assembly consumes.** -/
theorem linearIsoperimetricHyperbolicityStatement :
    LinearIsoperimetricHyperbolicityStatement := by
  intro α _ _ R hbound K hiso
  exact DiscreteStokes.isHyperbolicGroup_presentedGroup_of_linearIsoperimetric R hbound hiso

/-- **`GirthEightHyperbolicity` from the local-data filling input.**  A table
passing `GirthEightChecks` whose cyclically reduced trivial words bound discs
with triangular local data presents a hyperbolic group. -/
theorem girthEightHyperbolicity_of_filling
    (hfill : ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
      (_ : DecidableEq Generator) (_ : Fintype TriangleIndex)
      (_ : DecidableEq TriangleIndex)
      (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ),
      GirthEightChecks T d → CyclicallyReducedLocalDataFilling T) :
    GirthEightHyperbolicity :=
  girthEightHyperbolicity_of_localDataFilling linearIsoperimetricHyperbolicityStatement hfill

end KazhdanHypGirthEightHyperbolicityBridge
end GGT
end GroupApproximation

#audit_closed_axioms GroupApproximation.GGT.KazhdanHypGirthEightHyperbolicityBridge.linearIsoperimetricHyperbolicityStatement
#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightHyperbolicityBridge.girthEightHyperbolicity_of_filling
