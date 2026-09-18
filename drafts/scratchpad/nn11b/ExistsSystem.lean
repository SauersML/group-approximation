import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.SystemSem
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.Decide

/-!
# Feasibility of polynomial systems is decidable

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  Whether a system
`p = 0 (p ∈ S.1)`, `0 ≤ q (q ∈ S.2)` of integer polynomials has a real solution is a
computable predicate (`computablePred_existsSystem`).  The decider is
`decidePrenex ∘ systemPrenex`.  Its correctness is `existsSystem_iff_decidePrenex`, and
its computability is `computable_decidePrenex` together with `computable_systemPrenex`.
-/

namespace GroupApproximation.Full.NN11b

/-- **Feasibility of polynomial systems over `ℝ` is decidable.** -/
theorem computablePred_existsSystem :
    ComputablePred (fun S : List MvP × List MvP =>
      ∃ x : ℕ → ℝ, (∀ p ∈ S.1, mvEval x p = 0) ∧ ∀ p ∈ S.2, 0 ≤ mvEval x p) :=
  ComputablePred.computable_iff.2
    ⟨fun S => decidePrenex (systemPrenex S), computable_decidePrenex.comp computable_systemPrenex,
      funext fun S => propext (existsSystem_iff_decidePrenex S)⟩

end GroupApproximation.Full.NN11b
