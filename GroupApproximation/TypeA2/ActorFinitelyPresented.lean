import GroupApproximation.TypeA2.Witness
import GroupApproximation.TypeA2.SemidirectFinitePresentation
import GroupApproximation.GroupTheory.HigmanThompson.GeometricF

/-!
# The witness group is finitely presented

`WitnessGroup = geoF 0 ⋊ FreeGroup (Fin 2)` is finitely presented, because `geoF 0` is
(`HigmanThompson.geoF_isFinitelyPresented`) and a semidirect product of a finitely presented
group by a finitely generated free group is.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation.TypeA2

open HigmanThompson

theorem witnessGroup_isFinitelyPresented : Group.IsFinitelyPresented WitnessGroup :=
  haveI := geoF_isFinitelyPresented 0
  isFinitelyPresented_semidirectProduct_freeGroup _

end GroupApproximation.TypeA2
