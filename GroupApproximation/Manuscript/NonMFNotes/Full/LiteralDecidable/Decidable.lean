import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.Bridge
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.ExistsSystem

/-!
# The literal predicate is decidable (lane NN02c)

Manuscript: `thm:mf-radical-arithmetic` (non_mf_group_notes.tex), sentence
"This is decidable over the real closed field" (Tarski 1951, Seidenberg 1954).

`D(P,v,n,d)` many-one reduces to real solvability of integer polynomial systems
(`literalD_manyOneReducible_existsSystem`), and that solvability is decidable by the
proved real-closed-field decision procedure of lane NN11b (`NN11b.computablePred_existsSystem`).
No decision procedure is assumed: both ingredients are theorems.
-/

namespace GroupApproximation.Full.NN02c

/-- **The literal predicate `D(P,v,n,d)` is decidable** (`thm:mf-radical-arithmetic`,
"This is decidable over the real closed field"; Tarski 1951, Seidenberg 1954). -/
theorem computablePred_literalD :
    ComputablePred
      (fun z : (PresentationCodes.PresentationCode × List (ℕ × Bool)) × ℕ × ℕ =>
        NN02b.LiteralD z.1.1 z.1.2 z.2.1 z.2.2) :=
  ComputablePred.computable_of_manyOneReducible literalD_manyOneReducible_existsSystem
    NN11b.computablePred_existsSystem

end GroupApproximation.Full.NN02c
