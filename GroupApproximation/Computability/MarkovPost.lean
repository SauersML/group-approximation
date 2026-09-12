import GroupApproximation.Computability.FiniteMachineWordProblem
import GroupApproximation.Computability.UniversalMachineUndecidable

/-!
# Markov--Post, with no literature input

There is a finitely presented monoid whose word problem is undecidable.

Every piece has been assembled elsewhere in this development; this file is the
composition.

* `UniversalMachineUndecidable` gives a Post--Turing machine whose halting on a
  computable family of inputs is undecidable.
* `FiniteMachineWordProblem` turns such a machine into a finite presentation
  with undecidable word problem --- *provided* the states it visits lie in a
  finite set closed under the transition function.
* That last condition is Mathlib's own `TM0.Supports`, and Mathlib proves it
  along the whole translation chain: `PartrecToTM2.tr_supports` on the finite
  set `codeSupp c k`, then `TM2to1.tr_supports`, then `TM1to0.tr_supports`,
  whose conclusion is `TM0.Supports (tr M) ↑(trStmts M S)` --- a `Finset`.

`TM0.Supports M S` unfolds to `default ∈ S` together with closure of `S` under
transitions, which is exactly the hypothesis `not_computablePred_wordProblem_of_finite`
asks for.  So the finiteness that looked like the remaining obstacle was already
in Mathlib, one namespace away from the theorems that produce the machine.

## Noncomputability

The construction is noncomputable, for one reason that does not affect the
statement: the TM0 state type is `Option (TM1.Stmt Γ Λ σ) × σ`, and `TM1.Stmt`
contains function types, so it has no decidable equality.  `restrict` needs to
decide membership in a `Finset` of states, and here that decision is classical.
The monoid is still presented by a finite list of rules --- which is all
"finitely presented" means --- and the undecidability is of its word problem,
not of finding its presentation.
-/

-- Mathlib derives `DecidableEq` and `Inhabited` for the four-stack index type but
-- not `Fintype`, and the tape alphabet's finiteness needs it.
deriving instance Fintype for Turing.PartrecToTM2.K'

namespace GroupApproximation
namespace StringRewriting
namespace PostMachine

open Turing Turing.PartrecToTM2

/-- **Markov--Post.**  There are finite alphabets and a finite rewriting system
over them whose word problem --- equality against one fixed four-letter word ---
is undecidable.

Unconditional: no hypothesis, and no literature input. -/
theorem exists_undecidable_wordProblem (n : ℕ) :
    ∃ (Γ₀ Λ₀ : Type) (_ : Inhabited Γ₀) (_ : Fintype Γ₀) (_ : Fintype Λ₀)
      (R : RewriteSystem (Letter Γ₀ (HState Λ₀)))
      (g : ℕ → List (Letter Γ₀ (HState Λ₀))),
      ¬ ComputablePred fun m : ℕ =>
        StringRewriting.mk R (g m) = StringRewriting.mk R finalWord := by
  classical
  obtain ⟨c, hc⟩ := Computability.tm0_halting_not_computablePred n
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  -- Mathlib's support chain: TM2, then TM1, then TM0
  have hs2 : TM2.Supports tr (codeSupp c Cont'.halt) := tr_supports c Cont'.halt
  have hs1 := TM2to1.tr_supports tr hs2
  have hs0 := TM1to0.tr_supports (TM2to1.tr tr) hs1
  set M₀ := TM1to0.tr (TM2to1.tr tr) with hM₀
  set S₀ := TM1to0.trStmts (TM2to1.tr tr) (TM2to1.trSupp tr (codeSupp c Cont'.halt)) with hS₀
  -- `TM0.Supports` is exactly the hypothesis the capstone wants
  have hdef : (default : TM1to0.Λ' (TM2to1.tr tr)) ∈ S₀ := hs0.1
  have hclosed : Closed (ofTM0 M₀) S₀ := by
    intro q hq a q' act hstep
    simp only [ofTM0] at hstep
    cases hM : M₀ q a with
    | none => rw [hM] at hstep; simp at hstep
    | some p =>
      obtain ⟨q'', s⟩ := p
      rw [hM] at hstep
      have hp1 : q'' = q' := congrArg Prod.fst (Option.some.inj hstep)
      have hin := hs0.2 (q' := q'') (s := s) (Option.mem_def.mpr hM) (Finset.mem_coe.mpr hq)
      rw [hp1] at hin
      exact Finset.mem_coe.mp hin
  -- `TM2to1.Γ'` is a def, so instance search will not see through it on its own
  letI : Fintype (TM2to1.Γ' K' (fun _ : K' => Γ')) := TM2to1.Γ'.fintype
  obtain ⟨R, g, hRg⟩ :=
    not_computablePred_wordProblem_of_finite M₀
      (fun m => TM2to1.trInit K'.main (trList [m])) hc hdef hclosed
  exact ⟨_, _, inferInstance, inferInstance, inferInstance, R, g, hRg⟩

end PostMachine
end StringRewriting
end GroupApproximation
