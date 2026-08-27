import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode

/-!
# One code whose halting is undecidable

`Computability.TM0WordProblem` reduces the word problem of an explicitly
presented monoid to the halting of a Post--Turing machine, and isolates the one
missing input as `UndecidableTM0`: a *finite* machine with an undecidable
halting family.

Supplying it splits cleanly in two, and only the first half is about
computability:

1. **an undecidable source** --- a single partial recursive code whose halting,
   as its input varies, is not decidable;
2. **a machine realising it** --- turning that code into a finite Post--Turing
   machine, by way of Mathlib's `PartrecToTM2`, `TM2to1` and `TM1to0`.

This file does the first half, and it is short, because Mathlib has the pieces:
`Nat.Partrec.Code.eval_part` says evaluation is itself partial recursive, so
there is a code that runs other codes, and `ComputablePred.halting_problem` says
deciding which codes halt is impossible.

The second half is machine construction with no computability content left in
it.  It is not done here, and two obstacles in it are worth recording rather
than rediscovering: the state type of Mathlib's `PartrecToTM2` machine is
*infinite* (its states carry continuations, which carry codes), so a finite
machine has to come from restricting to a supported finite set --- `trStmts₁`
and `Λ'.Supports` are the relevant machinery --- and `PartrecToTM2.init c v`
starts in a state depending on `c`, whereas `TM2.init` starts in `default`, so
the two initialisations have to be reconciled before `TM2to1.tr_eval_dom`
applies.
-/

namespace GroupApproximation
namespace Computability

open Nat.Partrec Nat.Partrec.Code

/-- Computability of a predicate transports along a computable substitution. -/
theorem computablePred_comp {α : Type*} [Primcodable α] {p : ℕ → Prop}
    (hp : ComputablePred p) {g : α → ℕ} (hg : Computable g) :
    ComputablePred fun a => p (g a) := by
  obtain ⟨_, hD⟩ := hp
  classical
  exact ⟨fun a => Classical.dec _, by
    simpa using (hD.comp hg).of_eq fun a => by simp⟩

/-- **A universal code at a fixed input.**  Evaluation is partial recursive in
both arguments, so there is a single code `u` which, given the number coding a
code `c`, halts exactly when `c` halts on the fixed input `n`. -/
theorem exists_universal_code (n : ℕ) :
    ∃ u : Code, ∀ c : Code, (eval u (Encodable.encode c)).Dom ↔ (eval c n).Dom := by
  have hpartrec : Partrec fun m : ℕ => eval (Denumerable.ofNat Code m) n := by
    have hcode : Computable fun m : ℕ => Denumerable.ofNat Code m :=
      Computable.ofNat Code
    exact (eval_part.comp hcode (Computable.const n)).of_eq fun m => by simp
  obtain ⟨u, hu⟩ := exists_code.mp hpartrec
  refine ⟨u, fun c => ?_⟩
  rw [hu]
  simp

/-- **The halting of that one code is undecidable.**  Deciding it would decide,
for every code, whether that code halts on `n`, which is
`ComputablePred.halting_problem`. -/
theorem exists_code_not_computablePred (n : ℕ) :
    ∃ u : Code, ¬ ComputablePred fun m : ℕ => (eval u m).Dom := by
  obtain ⟨u, hu⟩ := exists_universal_code n
  refine ⟨u, fun hcomp => ?_⟩
  have hcode : Computable fun c : Code => Encodable.encode c :=
    Computable.encode
  have : ComputablePred fun c : Code => (eval u (Encodable.encode c)).Dom :=
    computablePred_comp hcomp hcode
  have hfinal : ComputablePred fun c : Code => (eval c n).Dom := by
    have hiff : (fun c : Code => (eval u (Encodable.encode c)).Dom) =
        fun c : Code => (eval c n).Dom :=
      funext fun c => propext (hu c)
    exact hiff ▸ this
  exact ComputablePred.halting_problem n hfinal

end Computability
end GroupApproximation
