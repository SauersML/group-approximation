import GroupApproximation.Manuscript.SimpleKazhdanSofic.LevelShiftDeltaWordProblem
import GroupApproximation.Computability.OracleTruthTable
import Mathlib.Computability.Primrec.List
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline` (a): the word problem of `Δ` is Turing reducible to that of `Γ`

`simple_kazhdan_sofic_group.tex`, `lem:halfline`, tex l.606–608:

> (a) Every finitely generated LEF group Γ is a subgroup of [Δ,Δ] for an infinite finitely generated LEF group Δ
> whose word problem is Turing reducible to that of Γ.

and the reduction of tex l.647–652 ("From a word in the β^{±1} and h_γ^{±1} one computes the exponent sum ℓ of β, the
levels where f changes, ... and the values of f there as words in E").

This module is the Turing reduction used by the endpoint of (a) (`HalflineA/Embedding`).

## Proof route

* `LevelShiftDeltaWordProblem.wordProblemOracle_levelGen_eq`: the word problem of `Δ`, in the generators
  `levelGen s = (β, h_{s i})`, is `decideCode` applied to the answers of the word problem of `Γ` in `s`.
* The decision reads the answers only at the finitely many codes `codes w` of the value words. So it is a truth-table
  reduction. `halflineQueries` lists these codes. `halflineDecide` combines the answers by a primitive recursive fold
  (`allOnes`), and both are primitive recursive (`primrec_halflineQueries`, `primrec_halflineDecide`).
* `decideCode_eq_halflineDecide`: the two decisions agree.
* `OracleTruthTable.turingReducible_of_truthTable` gives `turingReducible_wordProblemOracle_levelGen`, with no
  computability hypothesis on `Γ`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HalflineA

open LevelShiftDelta LevelShiftDeltaWordProblem Encodable

/-- Whether every entry of a list of answers is `1`, as a primitive recursive fold. -/
def allOnes (A : List ℕ) : Bool :=
  A.foldr (fun a b => decide (a = 1) && b) true

theorem allOnes_eq_true_iff (A : List ℕ) : allOnes A = true ↔ ∀ a ∈ A, a = 1 := by
  induction A with
  | nil => simp [allOnes]
  | cons a A ih =>
    rw [show allOnes (a :: A) = (decide (a = 1) && allOnes A) from rfl, Bool.and_eq_true, decide_eq_true_eq, ih,
      List.forall_mem_cons]

theorem primrec_allOnes : Primrec allOnes := by
  have hh : Primrec₂ fun (_ : List ℕ) (q : ℕ × Bool) => decide (q.1 = 1) && q.2 :=
    (Primrec.and.comp (PrimrecPred.decide (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const true) hh).of_eq fun _ => rfl

theorem allOk_eq_allOnes (o : ℕ → ℕ) (L : List ℕ) : allOk o L = allOnes (L.map o) :=
  Bool.eq_iff_iff.2 (by rw [allOk_iff, allOnes_eq_true_iff, List.forall_mem_map])

variable (ι : Type*) [Primcodable ι]

/-- **The queries**: the codes of the value words of `f` at the levels where it changes (tex l.647–650). -/
def halflineQueries (n : ℕ) : List ℕ :=
  Option.casesOn (decode n : Option (List (Option ι × Bool))) [] codes

/-- **The decision** from the answers: `ℓ = 0` and every value is trivial in `Γ` (tex l.650–651). -/
def halflineDecide (n : ℕ) (A : List ℕ) : ℕ :=
  cond (Option.casesOn (decode n : Option (List (Option ι × Bool))) false
    fun w => decide ((shiftPair w).1 = (shiftPair w).2) && allOnes A) 1 0

theorem primrec_halflineQueries : Primrec (halflineQueries ι) :=
  (Primrec.option_casesOn (Primrec.decode (α := List (Option ι × Bool))) (Primrec.const ([] : List ℕ))
    (primrec_codes.comp Primrec.snd).to₂).of_eq fun _ => rfl

theorem primrec_halflineDecide : Primrec₂ (halflineDecide ι) := by
  have h1 : Primrec fun p : ℕ × List ℕ => (decode p.1 : Option (List (Option ι × Bool))) :=
    Primrec.decode.comp Primrec.fst
  have hg : Primrec₂ fun (p : ℕ × List ℕ) (w : List (Option ι × Bool)) =>
      decide ((shiftPair w).1 = (shiftPair w).2) && allOnes p.2 :=
    (Primrec.and.comp
      (PrimrecPred.decide (Primrec.eq.comp (Primrec.fst.comp (primrec_shiftPair.comp Primrec.snd))
        (Primrec.snd.comp (primrec_shiftPair.comp Primrec.snd))))
      (primrec_allOnes.comp (Primrec.snd.comp Primrec.fst))).to₂
  exact (Primrec.cond (Primrec.option_casesOn h1 (Primrec.const false) hg) (Primrec.const 1)
    (Primrec.const 0)).of_eq fun _ => rfl

theorem decideCode_eq_halflineDecide (o : ℕ → ℕ) (n : ℕ) :
    decideCode ι o n = halflineDecide ι n ((halflineQueries ι n).map o) := by
  unfold decideCode halflineDecide halflineQueries
  cases (decode n : Option (List (Option ι × Bool))) with
  | none => rfl
  | some w =>
    show cond (decideWord o w) 1 0 =
      cond (decide ((shiftPair w).1 = (shiftPair w).2) && allOnes ((codes w).map o)) 1 0
    rw [decideWord, allOk_eq_allOnes]

variable {ι}

/-- **The word problem of `Δ` is Turing reducible to that of `Γ`** (tex l.647–652): for any family `s : ι → Γ`, the word
problem of the generators `β` and `h_{s i}` of `Δ` is Turing reducible to the word problem of `s`. -/
theorem turingReducible_wordProblemOracle_levelGen {Γ : Type*} [Group Γ] (s : ι → Γ) :
    TuringReducible (wordProblemOracle (levelGen s)) (wordProblemOracle s) :=
  OracleTruthTable.turingReducible_of_truthTable (gt := oracleAnswer s) (fun _ => (Part.some_get _).symm)
    (primrec_halflineQueries ι) (primrec_halflineDecide ι)
    (fun n => (congrFun (wordProblemOracle_levelGen_eq s) n).trans
      (congrArg Part.some (decideCode_eq_halflineDecide ι (oracleAnswer s) n)))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.turingReducible_wordProblemOracle_levelGen

end HalflineA
end SimpleKazhdanSofic
end GroupApproximation
