import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXGroups
import GroupApproximation.Sofic.CliffordWitnessLocallyRFByInt

/-!
# Problem X(1) via the affine--Clifford witness

This gives a second, conceptually direct witness for the negative answer to
Problem X(1).  The explicit affine--Clifford group `W` is non-operator-MF, but
its canonical maximal trace is amenable because

`W ≃ (CliffordLamp X ⋊ Telescope) ⋊ ℤ`

and the inner group is locally residually finite.  A quasidiagonal canonical
trace would make `W` operator-MF, yielding the required contradiction.
-/

namespace GroupApproximation
namespace NinetyNineProblems

open LiteralNonMFLinearWitness LiteralWitnessConsequences
open CliffordWitnessLocallyRFByInt

noncomputable section

/-- The affine--Clifford witness has an amenable canonical maximal trace which
is not quasidiagonal. -/
theorem witnessCanonicalTrace_amenable_not_quasidiagonal :
    Quasidiagonal.IsAmenableTrace
        (fun a : MaximalGroupCStar WitnessGroup ↦
          canonicalMaximalTrace WitnessGroup a) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar WitnessGroup ↦
          canonicalMaximalTrace WitnessGroup a) :=
  canonicalMaximalTrace_amenable_not_isQuasidiagonalTrace_of_not_isOperatorMF
    WitnessGroup witnessCanonicalMaximalTrace_isAmenableTrace
      witnessGroup_not_isOperatorMF

end
end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_closed_axioms witnessCanonicalTrace_amenable_not_quasidiagonal
