import GroupApproximation.Computability.UniversalCodeHalting
import GroupApproximation.Computability.UniversalMachineInit

/-!
# A Post--Turing machine whose halting is undecidable

`UniversalCodeHalting` produces a `Nat.Partrec.Code` whose halting is
undecidable.  `UniversalMachineInit` produces a Post--Turing machine that runs a
`Turing.ToPartrec.Code`.  Those are *different* code types, and this file is the
bridge: `Nat.Partrec'.part_iff₁` turns the partial recursive function underlying
the first into the vector form `ToPartrec.exists_code` consumes.

The result is `tm0_halting_not_computablePred`: a single Post--Turing machine,
and a family of inputs, on which no algorithm decides halting.

## What is still missing, and it is only one thing

The machine's state type `Turing.PartrecToTM2.Λ'` is infinite --- its states
carry continuations, which carry codes.  A *finitely presented* monoid needs a
machine with finitely many states, so the machine has to be cut down to the
states a run actually visits.  `Computability.MachineRestrict` does the cutting
and proves nothing is lost; what is not proved anywhere yet is that the visited
set is finite, which is what `PartrecToTM2.trStmts₁` and `Λ'.Supports` are for.

Until that is done this file does not feed `TM0WordProblem`: it gives an
undecidable machine, not an undecidable *finite* machine.
-/

namespace GroupApproximation
namespace Computability

open Turing Turing.PartrecToTM2

/-- **A `ToPartrec` code whose halting is undecidable.**  The code runs the
`m`-th partial recursive code on a fixed input, so deciding whether it halts
would decide which codes halt. -/
theorem exists_toPartrec_code_not_computablePred (n : ℕ) :
    ∃ c : ToPartrec.Code,
      ¬ ComputablePred fun m : ℕ => (ToPartrec.Code.eval c [m]).Dom := by
  have hpartrec :
      Partrec fun m : ℕ => Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code m) n := by
    have hcode : Computable fun m : ℕ => Denumerable.ofNat Nat.Partrec.Code m :=
      Computable.ofNat Nat.Partrec.Code
    exact (Nat.Partrec.Code.eval_part.comp hcode (Computable.const n)).of_eq fun m => by simp
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hpartrec)
  refine ⟨c, fun hcomp => ?_⟩
  -- the two halting predicates coincide
  have hdom : ∀ m : ℕ, (ToPartrec.Code.eval c [m]).Dom ↔
      (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code m) n).Dom := by
    intro m
    have := hc ⟨[m], rfl⟩
    simp only [List.Vector.head] at this
    rw [this]
    simp
  have hstep : ComputablePred fun m : ℕ =>
      (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code m) n).Dom := by
    have : (fun m : ℕ => (ToPartrec.Code.eval c [m]).Dom) =
        fun m : ℕ => (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code m) n).Dom :=
      funext fun m => propext (hdom m)
    exact this ▸ hcomp
  -- and deciding those decides the halting problem
  have hcode : Computable fun d : Nat.Partrec.Code => Encodable.encode d := Computable.encode
  have hfinal : ComputablePred fun d : Nat.Partrec.Code => (Nat.Partrec.Code.eval d n).Dom := by
    have := computablePred_comp hstep hcode
    simpa using this
  exact ComputablePred.halting_problem n hfinal

/-- **The machine, and the undecidability.**  A single Post--Turing machine
whose halting on the inputs `trInit K'.main (trList [m])` is not decidable in
`m`. -/
theorem tm0_halting_not_computablePred (n : ℕ) :
    ∃ c : ToPartrec.Code,
      letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
      ¬ ComputablePred fun m : ℕ =>
        (TM0.eval (TM1to0.tr (TM2to1.tr tr))
          (TM2to1.trInit K'.main (trList [m]))).Dom := by
  obtain ⟨c, hc⟩ := exists_toPartrec_code_not_computablePred n
  refine ⟨c, ?_⟩
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  intro hcomp
  refine hc ?_
  have : (fun m : ℕ => (TM0.eval (TM1to0.tr (TM2to1.tr tr))
      (TM2to1.trInit K'.main (trList [m]))).Dom) =
      fun m : ℕ => (ToPartrec.Code.eval c [m]).Dom :=
    funext fun m => propext (tm0_eval_dom_iff c [m])
  exact this ▸ hcomp

end Computability
end GroupApproximation
