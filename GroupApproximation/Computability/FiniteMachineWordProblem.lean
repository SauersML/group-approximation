import GroupApproximation.Computability.MachineRestrict
import GroupApproximation.Computability.TM0WordProblem

/-!
# From an undecidable machine to an undecidable word problem

`Computability.UniversalMachineUndecidable` produces a Post--Turing machine
whose halting is undecidable, and `Computability.TM0WordProblem` turns halting
into a single word equation.  They do not compose yet, for one reason: the
machine's state type is infinite, and a *finitely presented* monoid needs
finitely many states.

This file closes everything except that.  Given

* a Post--Turing machine over a finite tape alphabet whose halting on a family
  of inputs is undecidable, and
* a `Finset` of states containing the initial state and closed under the
  transition function,

the word problem of an explicitly presented finite monoid is undecidable.  The
restriction is `Computability.MachineRestrict`, which loses nothing; the rest is
`TM0WordProblem`.

So the entire remaining gap is a single statement about Mathlib's construction:
that the states its machine visits are contained in some finite closed set.
Mathlib's `PartrecToTM2.trStmts₁` and `Λ'.Supports` are what that would be
proved from.  Nothing else is missing, and nothing else is assumed.
-/

namespace GroupApproximation
namespace StringRewriting
namespace PostMachine

open Turing

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]

/-- The starting configuration, with its state seen as an element of `S`. -/
def restrictedInput (S : Finset Λ) (hdef : (default : Λ) ∈ S) (l : List Γ) :
    Cfg Γ {q // q ∈ S} :=
  ⟨⟨default, hdef⟩, [], l.headI, l.tail⟩

omit [DecidableEq Λ] in
@[simp] theorem unrestrictCfg_restrictedInput (S : Finset Λ) (hdef : (default : Λ) ∈ S)
    (l : List Γ) :
    unrestrictCfg (restrictedInput S hdef l) = ofInput l := rfl

/-- **Halting is unchanged by the restriction.**  A run of the full machine from
the initial configuration halts exactly when the restricted machine does. -/
theorem restricted_halts_iff (M : TM0.Machine Γ Λ) {S : Finset Λ}
    (hdef : (default : Λ) ∈ S) (hclosed : Closed (ofTM0 M) S) (l : List Γ) :
    (∃ e, Reach (step (restrict (ofTM0 M) S)) (restrictedInput S hdef l) e ∧
        step (restrict (ofTM0 M) S) e = none) ↔ (TM0.eval M l).Dom := by
  rw [eval_dom_iff M l]
  constructor
  · rintro ⟨e, he, hnone⟩
    refine ⟨unrestrictCfg e, ?_, ?_⟩
    · have := reach_unrestrict hclosed he
      simpa using this
    · exact (step_restrict_eq_none_iff (ofTM0 M) hclosed e).mp hnone
  · rintro ⟨e, he, hnone⟩
    rw [← unrestrictCfg_restrictedInput S hdef l] at he
    obtain ⟨d, hd, rfl⟩ := (reach_iff hclosed).mp he
    exact ⟨d, hd, (step_restrict_eq_none_iff (ofTM0 M) hclosed d).mpr hnone⟩

/-- **The capstone.**  An undecidable machine with finitely many relevant states
gives a finitely presented monoid with undecidable word problem.

Everything is explicit except the enumerations, which are existential only
because `Finset.toList` is noncomputable; the rules are built from them by a
computable `flatMap`, and the target word is four letters. -/
theorem not_computablePred_wordProblem_of_finite [Fintype Γ]
    (M : TM0.Machine Γ Λ) (f : ℕ → List Γ)
    (hund : ¬ ComputablePred fun m : ℕ => (TM0.eval M (f m)).Dom)
    {S : Finset Λ} (hdef : (default : Λ) ∈ S) (hclosed : Closed (ofTM0 M) S) :
    ∃ (R : RewriteSystem (Letter Γ (HState {q // q ∈ S})))
      (g : ℕ → List (Letter Γ (HState {q // q ∈ S}))),
      ¬ ComputablePred fun m : ℕ =>
        StringRewriting.mk R (g m) = StringRewriting.mk R finalWord := by
  obtain ⟨states, hstates⟩ := exists_states_enumeration S
  refine ⟨haltingSystem (restrict (ofTM0 M) S) states (Finset.univ : Finset Γ).toList,
    fun m => encode (liftCfg (restrictedInput S hdef (f m))), ?_⟩
  intro hcomp
  refine hund ?_
  have hkey : ∀ m : ℕ,
      (StringRewriting.mk
          (haltingSystem (restrict (ofTM0 M) S) states (Finset.univ : Finset Γ).toList)
          (encode (liftCfg (restrictedInput S hdef (f m)))) =
        StringRewriting.mk
          (haltingSystem (restrict (ofTM0 M) S) states (Finset.univ : Finset Γ).toList)
          finalWord) ↔ (TM0.eval M (f m)).Dom := by
    intro m
    rw [haltingSystem_mk_eq_finalWord_iff (restrict (ofTM0 M) S) hstates
      (fun a => by simp) (restrictedInput S hdef (f m))]
    exact restricted_halts_iff M hdef hclosed (f m)
  have : (fun m : ℕ =>
      StringRewriting.mk
        (haltingSystem (restrict (ofTM0 M) S) states (Finset.univ : Finset Γ).toList)
        (encode (liftCfg (restrictedInput S hdef (f m)))) =
      StringRewriting.mk
        (haltingSystem (restrict (ofTM0 M) S) states (Finset.univ : Finset Γ).toList)
        finalWord) = fun m : ℕ => (TM0.eval M (f m)).Dom :=
    funext fun m => propext (hkey m)
  exact this ▸ hcomp

end PostMachine
end StringRewriting
end GroupApproximation
