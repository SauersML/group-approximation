import GroupApproximation.Computability.MFRadicalGodel
import Mathlib.Computability.Halting

/-!
# A halting-complete promise problem invisible to every matrix observer

`MFRadicalComputer` compiles a partial-recursive program code `c` to a word
`codeWord c` in one fixed finitely presented group.  Every compiled word is
killed by every norm-matrix-corona representation, while it is equal to the
identity exactly when `c` halts on input zero.

This file packages that construction as a promise problem.  The promise is
semantic and uniform: every input word is MF-invisible.  Even under that
promise, triviality is recursively enumerable but undecidable, and
nontriviality is not recursively enumerable.  Thus no computably checkable
certificate system can be sound and complete for strict nontriviality after
all finite-dimensional matrix observers have identified the word with the
identity.
-/

namespace GroupApproximation
namespace MFObserverBlindPromise

open Nat.Partrec
open MFRadicalComputer

noncomputable section

/-- YES instances: the compiled observer-blind word is genuinely trivial. -/
def Trivial (c : Code) : Prop :=
  codeWord c = 1

/-- NO instances: the compiled observer-blind word is genuinely nontrivial. -/
def Nontrivial (c : Code) : Prop :=
  codeWord c ≠ 1

/-- The compiler promise holds for every input, not merely for YES or NO
instances. -/
theorem promise (c : Code) : NormMFInvisible (codeWord c) :=
  codeWord_normMFInvisible c

/-- Exact compiler semantics: YES is the halting problem at input zero. -/
theorem trivial_iff_halting (c : Code) :
    Trivial c ↔ (Code.eval c 0).Dom :=
  codeWord_eq_one_iff_eval_dom c

/-- Exact compiler semantics: NO is the complement of the halting problem. -/
theorem nontrivial_iff_nonhalting (c : Code) :
    Nontrivial c ↔ ¬ (Code.eval c 0).Dom :=
  not_congr (codeWord_eq_one_iff_eval_dom c)

/-- YES instances are recursively enumerable by executing the input program. -/
theorem trivial_re : REPred Trivial := by
  have heval : Partrec fun c : Code ↦ Code.eval c 0 :=
    Code.eval_part.comp Computable.id (Computable.const 0)
  exact heval.dom_re.of_eq fun c ↦ (trivial_iff_halting c).symm

/-- NO instances are not recursively enumerable.  This rules out every sound
and complete computably checkable certificate system for nontriviality on the
promised family. -/
theorem nontrivial_not_re : ¬ REPred Nontrivial := by
  intro hre
  exact ComputablePred.halting_problem_not_re 0
    (hre.of_eq fun c ↦ nontrivial_iff_nonhalting c)

/-- The promised triviality problem is undecidable. -/
theorem trivial_not_computable : ¬ ComputablePred Trivial := by
  intro hdec
  exact ComputablePred.halting_problem 0
    (hdec.of_eq fun c ↦ trivial_iff_halting c)

/-- There is no Boolean decider for the promised triviality problem. -/
theorem no_triviality_decider :
    ¬ ∃ f : Code → Bool,
      Computable f ∧ ∀ c, f c = true ↔ Trivial c := by
  rintro ⟨f, hf, hcorrect⟩
  exact trivial_not_computable
    (ComputablePred.computable_iff.mpr
      ⟨f, hf, funext fun c ↦ propext (hcorrect c).symm⟩)

/-- The actual promise-problem predicate: a nontrivial word which every
norm-matrix observer maps to the identity. -/
def StrictlyObserverBlind (c : Code) : Prop :=
  Nontrivial c ∧ NormMFInvisible (codeWord c)

/-- The promise-problem NO side is exactly nonhalting. -/
theorem strictlyObserverBlind_iff_nonhalting (c : Code) :
    StrictlyObserverBlind c ↔ ¬ (Code.eval c 0).Dom := by
  rw [StrictlyObserverBlind, nontrivial_iff_nonhalting]
  simp [promise]

/-- Strict observer-blindness has no recursively enumerable complete
certificate system. -/
theorem strictlyObserverBlind_not_re : ¬ REPred StrictlyObserverBlind := by
  intro hre
  exact nontrivial_not_re
    (hre.of_eq fun c ↦ by
      rw [StrictlyObserverBlind]
      simp [promise])

/-- Closed CS endpoint: one fixed finitely presented group supports a
computable observer-blind compiler whose equality problem is HALT and whose
strict-nontriviality side is not recursively enumerable. -/
theorem closed_package :
    Group.IsFinitelyPresented Carrier ∧
      ¬ IsOperatorMF Carrier ∧
      Computable codeRawWord ∧
      (∀ c : Code, NormMFInvisible (codeWord c)) ∧
      (∀ c : Code, Trivial c ↔ (Code.eval c 0).Dom) ∧
      REPred Trivial ∧
      ¬ ComputablePred Trivial ∧
      ¬ REPred StrictlyObserverBlind :=
  ⟨carrier_isFinitelyPresented, carrier_not_isOperatorMF,
    computable_codeRawWord, promise, trivial_iff_halting,
    trivial_re, trivial_not_computable, strictlyObserverBlind_not_re⟩

end

end MFObserverBlindPromise
end GroupApproximation
