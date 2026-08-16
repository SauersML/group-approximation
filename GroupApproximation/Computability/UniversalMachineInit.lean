import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Starting Mathlib's TM2 model where it needs to start

`Computability.TM0WordProblem` needs a Post--Turing machine whose halting is
undecidable, and Mathlib's route to one is
`PartrecToTM2 → TM2to1 → TM1to0`.  Composing those hits an initialisation
mismatch that looks fatal and is not.

`PartrecToTM2.init c v` starts in the state `trNormal c Cont'.halt`, which
depends on the code being run.  Everything downstream --- `TM2to1.tr_eval_dom`,
and through it `TM1to0.tr_eval` --- is phrased in terms of `TM2.eval`, which
initialises with `TM2.init k L`, and that starts in `default`.  Two different
starting states, so the theorems do not compose as written.

The way through is that `default` is not fixed: it is whatever the `Inhabited`
instance says.  Choosing the instance `⟨trNormal c Cont'.halt⟩` makes
`TM2.init K'.main (trList v)` *equal* to `PartrecToTM2.init c v`, and then the
downstream theorems apply unchanged.  The only thing to check is the stacks, and
`K'.elim a b c d` is `update (fun _ ↦ []) K'.main` on the relevant argument
because `K'` has four constructors with `main` first.

That is what this file proves.  It is deliberately one small statement: it is
the hinge the rest of the chain turns on, and if it is wrong the rest is not
worth writing.
-/

namespace GroupApproximation
namespace Computability

open Turing Turing.PartrecToTM2

/-- With the starting state chosen as the instance, Mathlib's generic TM2
initialisation is exactly the one `PartrecToTM2` uses. -/
theorem tm2_init_eq (c : ToPartrec.Code) (v : List ℕ) :
    letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
    TM2.init K'.main (trList v) = init c v := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  show (⟨some default, default, Function.update (fun _ => []) K'.main (trList v)⟩ : Cfg') = _
  rw [init]
  congr 1
  funext k
  cases k <;> simp [Function.update, K'.elim]

/-! ## The chain composes

With the initialisation aligned, the three translations compose at the level of
domains, which is all an undecidability argument needs:

* `PartrecToTM2.tr_eval` --- the TM2 model evaluates the code;
* `TM2to1.tr_eval_dom` --- already a `Dom ↔ Dom`;
* `TM1to0.tr_eval` --- an equality of `Part`s, so its domains agree too.

The result is a *single* Post--Turing machine, independent of the code, whose
halting on the encoded input decides whether the code halts. -/

/-- **A Post--Turing machine that runs `c`.**  Mathlib's three translations,
composed, with the starting state supplied as the `Inhabited` instance. -/
theorem tm0_eval_dom_iff (c : ToPartrec.Code) (v : List ℕ) :
    letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
    (TM0.eval (TM1to0.tr (TM2to1.tr tr))
        (TM2to1.trInit K'.main (trList v))).Dom ↔ (ToPartrec.Code.eval c v).Dom := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  rw [TM1to0.tr_eval, TM2to1.tr_eval_dom, TM2.eval, tm2_init_eq c v, tr_eval]
  simp

end Computability
end GroupApproximation
