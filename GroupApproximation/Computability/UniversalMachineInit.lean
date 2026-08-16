import Mathlib.Computability.TuringMachine.ToPartrec

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

end Computability
end GroupApproximation
