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

## The finiteness this needed, and where it came from

The machine's state type `Turing.PartrecToTM2.Λ'` is infinite --- its states
carry continuations, which carry codes.  A *finitely presented* monoid needs a
machine with finitely many states, so the machine has to be cut down to the
states a run actually visits.  `Computability.MachineRestrict` does the cutting
and proves nothing is lost.

That the visited set is finite was once recorded here as unproved anywhere.  It
was already in Mathlib: `PartrecToTM2.tr_supports` on the finite set
`codeSupp c k`, then `TM2to1.tr_supports`, then `TM1to0.tr_supports`, whose
conclusion is `TM0.Supports (tr M) ↑(trStmts M S)` with a `Finset` carrier ---
which is exactly the hypothesis
`FiniteMachineWordProblem.not_computablePred_wordProblem_of_finite` asks for.

So this file does feed `TM0WordProblem`, and `Computability.MarkovPost` is the
composition: a finitely presented monoid with undecidable word problem, with no
hypothesis and no literature input.
-/

namespace GroupApproximation
namespace Computability

open Turing Turing.PartrecToTM2

/-- A `ToPartrec` code which runs the numeral-indexed universal partial
function on the fixed input `n`.  Unlike the undecidability corollary below,
this retains the pointwise simulation theorem needed by later fixed-point
constructions. -/
theorem exists_toPartrec_universal_code (n : ℕ) :
    ∃ c : ToPartrec.Code, ∀ m : ℕ,
      (ToPartrec.Code.eval c [m]).Dom ↔
        (Nat.Partrec.Code.eval
          (Denumerable.ofNat Nat.Partrec.Code m) n).Dom := by
  have hpartrec :
      Partrec fun m : ℕ =>
        Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code m) n := by
    have hcode : Computable fun m : ℕ => Denumerable.ofNat Nat.Partrec.Code m :=
      Computable.ofNat Nat.Partrec.Code
    exact (Nat.Partrec.Code.eval_part.comp hcode (Computable.const n)).of_eq
      fun m => by simp
  obtain ⟨c, hc⟩ :=
    ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hpartrec)
  refine ⟨c, fun m => ?_⟩
  have h := hc ⟨[m], rfl⟩
  simp only [List.Vector.head] at h
  rw [h]
  simp

/-- **A `ToPartrec` code whose halting is undecidable.**  The code runs the
`m`-th partial recursive code on a fixed input, so deciding whether it halts
would decide which codes halt. -/
theorem exists_toPartrec_code_not_computablePred (n : ℕ) :
    ∃ c : ToPartrec.Code,
      ¬ ComputablePred fun m : ℕ => (ToPartrec.Code.eval c [m]).Dom := by
  obtain ⟨c, hdom⟩ := exists_toPartrec_universal_code n
  refine ⟨c, fun hcomp => ?_⟩
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
