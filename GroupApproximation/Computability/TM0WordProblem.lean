import GroupApproximation.Computability.PostMachineTM0
import GroupApproximation.Computability.PostMachineHalting

/-!
# One word equation decides whether a Post--Turing machine terminates

Two chains meet here.

`Computability.PostMachineHalting` ends at `haltingSystem_mk_eq_finalWord_iff`:
for an explicitly listed finite rewriting system, a single equation between a
configuration word and a fixed four-letter word holds exactly when the machine
halts from that configuration.  Its machine is the one defined in
`Computability.PostMachine`.

`Computability.PostMachineTM0` ends at `eval_dom_iff`: that machine, started
from an input list, halts exactly when Mathlib's `TM0.eval` on the same input
list terminates.

Composing them gives the statement in the shape everything downstream wants ---
`Turing.TM0.eval` on the left, one word equation on the right:

    (TM0.eval M l).Dom  ↔  mk R (encode (liftCfg (ofInput l))) = mk R finalWord

with `R` an explicit computable list of rules, and the right-hand word fixed.
Nothing here is specific to any particular machine, so any theorem that produces
an undecidable `TM0.eval` --- for instance by way of Mathlib's
`ToPartrec.exists_code`, `PartrecToTM2.tr_eval`, `TM2to1.tr_eval` and
`TM1to0.tr_eval` --- hands its undecidability straight to this word problem.

That last step is not taken here.  What is taken is everything that does not
depend on which machine is chosen.
-/

namespace GroupApproximation
namespace StringRewriting
namespace PostMachine

open Turing

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

/-- The rewriting system attached to a Post--Turing machine: the rules of the
lifted machine together with the cleanup rules, as a finite list. -/
def tm0System (M : TM0.Machine Γ Λ) (states : List Λ) (tapes : List Γ) :
    RewriteSystem (Letter Γ (HState Λ)) :=
  haltingSystem (ofTM0 M) states tapes

/-- **Termination of `TM0.eval` is one word equation.**  For a Post--Turing
machine `M` and an input list `l`, Mathlib's evaluation terminates exactly when
the word of the starting configuration equals the fixed final word in the monoid
presented by `tm0System M`.

Both sides are explicit: the rules are a computable list built from the two
enumerations, and the right-hand word is `[endL, done, blank, endR]`, which does
not mention `M` or `l`. -/
theorem tm0_eval_dom_iff_mk_eq_finalWord (M : TM0.Machine Γ Λ)
    {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes)
    (l : List Γ) :
    (TM0.eval M l).Dom ↔
      StringRewriting.mk (tm0System M states tapes)
          (encode (liftCfg (ofInput l))) =
        StringRewriting.mk (tm0System M states tapes) finalWord := by
  rw [tm0System,
    haltingSystem_mk_eq_finalWord_iff (ofTM0 M) hstates htapes (ofInput l)]
  exact eval_dom_iff M l

/-- The same, for finite alphabets, where the enumerations always exist.  This
is an existence statement, so it may use the noncomputable `Finset.toList`; the
computable form is the theorem above. -/
theorem exists_system_tm0_eval_dom_iff [Fintype Γ] [Fintype Λ]
    (M : TM0.Machine Γ Λ) :
    ∃ R : RewriteSystem (Letter Γ (HState Λ)), ∀ l : List Γ,
      ((TM0.eval M l).Dom ↔
        StringRewriting.mk R (encode (liftCfg (ofInput l))) =
          StringRewriting.mk R finalWord) :=
  ⟨tm0System M (Finset.univ : Finset Λ).toList (Finset.univ : Finset Γ).toList,
    fun l => tm0_eval_dom_iff_mk_eq_finalWord M (fun _ => by simp) (fun _ => by simp) l⟩

end PostMachine
end StringRewriting
end GroupApproximation
