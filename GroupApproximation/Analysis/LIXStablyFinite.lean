import GroupApproximation.Analysis.LIXLimitAlgebra
import GroupApproximation.Analysis.LIXLimitSimple
import GroupApproximation.Analysis.LIXLimitTrace
import GroupApproximation.Analysis.LIXLimitTraceFaithful
import GroupApproximation.Analysis.LIXStageTrace
import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Meta.AxiomGuard

/-!
# The LIX counterexample algebra is stably finite

At every rank `n ≠ 0` the counterexample algebra `LIX.Gen.LIXLimit n` carries a faithful tracial
state, so every isometry in every nonempty matrix amplification of it is a unitary.

* Each stage algebra carries a tracial state, the normalized fibre trace at a point
  (`STW59.Gen.stageTracialState`).
* Hence the inductive limit carries one (`CStarTower.nonempty_tracialState_limit`, by compactness
  of the trace spaces).
* The limit is C⋆-simple (`LIX.Gen.lixLimit_isSimpleCStar`), so that tracial state is faithful
  (`TraceFaithful.faithfulTracialStateOfIsSimpleCStar`).
* A faithful tracial state amplifies to every matrix algebra, where the defect `1 - v v⋆` of an
  isometry is a projection of trace zero (`FaithfulTracialState.matrix_mul_star_eq_one_of_star_mul_eq_one`).

Nothing about the bundle obstruction is used: stable finiteness holds at every rank for the same
reason, and it is independent of `LemmaTwoHoldsAtPowers`.
-/

namespace GroupApproximation
namespace LIX
namespace Gen

noncomputable section

/-- **The rank-`n` counterexample algebra carries a tracial state.** -/
theorem nonempty_tracialState_lixLimit (n : ℕ) [NeZero n] :
    Nonempty (TracialState (LIXLimit n)) :=
  (lixTower n).nonempty_tracialState_limit fun i =>
    STW59.Gen.nonempty_tracialState_stageAlgebra n i

/-- **A faithful tracial state on the rank-`n` counterexample algebra**: any tracial state, made
faithful by simplicity. -/
def lixLimitFaithfulTracialState (n : ℕ) [NeZero n] : FaithfulTracialState (LIXLimit n) :=
  TraceFaithful.faithfulTracialStateOfIsSimpleCStar (lixLimit_isSimpleCStar n)
    (Classical.choice (nonempty_tracialState_lixLimit n))

/-- **Stable finiteness of the rank-`n` counterexample algebra**: every isometry in every nonempty
matrix amplification is a unitary. -/
theorem lixLimit_mul_star_eq_one_of_star_mul_eq_one (n : ℕ) [NeZero n] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (hι : Nonempty ι) {v : CStarMatrix ι ι (LIXLimit n)} (hv : star v * v = 1) :
    v * star v = 1 :=
  (lixLimitFaithfulTracialState n).matrix_mul_star_eq_one_of_star_mul_eq_one ι hι hv

end

end Gen
end LIX
end GroupApproximation

#audit_axioms GroupApproximation.LIX.Gen.nonempty_tracialState_lixLimit
#audit_axioms GroupApproximation.LIX.Gen.lixLimitFaithfulTracialState
#audit_axioms GroupApproximation.LIX.Gen.lixLimit_mul_star_eq_one_of_star_mul_eq_one
