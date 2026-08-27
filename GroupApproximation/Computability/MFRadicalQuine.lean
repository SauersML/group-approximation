import GroupApproximation.Computability.MFRadicalComputer
import Mathlib.Computability.RE

/-!
# Exact source streams inside the operator-MF residual

`MFRadicalComputer.codeWord` detects the domain of a partial-recursive
program.  This file turns that domain bit into an output-sensitive query: for
a program `q`, input position `i`, and proposed cell `b`, the word
`outputWord q i b` is trivial exactly when `q(i)` returns `b`.

Consequently every computable byte stream, including the source stream of an
exact quine, has a complete equality oracle inside the derived layer of the
operator-MF residual of one fixed finitely presented non-MF group.  This is
not a direct-product label: the words are faithful commutator gates mixing the
Boone controller with the nontrivial invisible mark.
-/

namespace GroupApproximation
namespace MFRadicalQuine

open MFRadicalComputer

noncomputable section

private def acceptEqual (b : ℕ) : ℕ →. ℕ := fun x =>
  cond (decide (x = b)) (Part.some 0) Part.none

private theorem acceptEqual_partrec (b : ℕ) :
    Nat.Partrec (acceptEqual b) := by
  have heq : ComputablePred fun x : ℕ => x = b :=
    PrimrecPred.computablePred
      (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const b))
  exact Partrec.nat_iff.mp
    (Partrec.cond heq.decide (Computable.const 0).partrec Partrec.none)

private def filterFunction (q : Nat.Partrec.Code) (b : ℕ) : ℕ →. ℕ :=
  fun i => (Nat.Partrec.Code.eval q i).bind (acceptEqual b)

private theorem filterFunction_partrec (q : Nat.Partrec.Code) (b : ℕ) :
    Nat.Partrec (filterFunction q b) := by
  exact (acceptEqual_partrec b).comp
    (Nat.Partrec.Code.exists_code.mpr ⟨q, rfl⟩)

/-- A partial-recursive program which accepts precisely the inputs on which
`q` returns `b`. -/
def filterCode (q : Nat.Partrec.Code) (b : ℕ) : Nat.Partrec.Code :=
  (Nat.Partrec.Code.exists_code.mp (filterFunction_partrec q b)).choose

theorem eval_filterCode (q : Nat.Partrec.Code) (b i : ℕ) :
    Nat.Partrec.Code.eval (filterCode q b) i = filterFunction q b i := by
  exact congrFun
    (Nat.Partrec.Code.exists_code.mp
      (filterFunction_partrec q b)).choose_spec i

/-- A closed program whose domain records whether `q(i)` returns `b`. -/
def outputTestCode (q : Nat.Partrec.Code) (i b : ℕ) : Nat.Partrec.Code :=
  Nat.Partrec.Code.comp (filterCode q b) (Nat.Partrec.Code.const i)

theorem eval_outputTestCode (q : Nat.Partrec.Code) (i b : ℕ) :
    Nat.Partrec.Code.eval (outputTestCode q i b) 0 =
      filterFunction q b i := by
  simp [outputTestCode, Nat.Partrec.Code.eval, eval_filterCode]

private theorem filterFunction_dom_iff (q : Nat.Partrec.Code) (i b : ℕ) :
    (filterFunction q b i).Dom ↔ b ∈ Nat.Partrec.Code.eval q i := by
  rw [Part.dom_iff_mem]
  simp only [filterFunction, Part.mem_bind_iff]
  constructor
  · rintro ⟨y, a, ha, hy⟩
    by_cases hab : a = b
    · simpa [hab] using ha
    · simp [acceptEqual, hab] at hy
  · intro hb
    exact ⟨0, b, hb, by simp [acceptEqual]⟩

/-- The MF-invisible group word asking the output-sensitive question
"does program `q` return cell `b` at position `i`?" -/
def outputWord (q : Nat.Partrec.Code) (i b : ℕ) : Carrier :=
  codeWord (outputTestCode q i b)

theorem outputWord_normMFInvisible (q : Nat.Partrec.Code) (i b : ℕ) :
    NormMFInvisible (outputWord q i b) :=
  codeWord_normMFInvisible _

theorem outputWord_mem_commutator_residual
    (q : Nat.Partrec.Code) (i b : ℕ) :
    outputWord q i b ∈ ⁅normMFResidual Carrier, (⊤ : Subgroup Carrier)⁆ :=
  codeWord_mem_commutator_residual _

/-- Exact output semantics: identity is a byte equality query, not merely a
halting bit. -/
theorem outputWord_eq_one_iff_mem
    (q : Nat.Partrec.Code) (i b : ℕ) :
    outputWord q i b = 1 ↔ b ∈ Nat.Partrec.Code.eval q i := by
  rw [outputWord, codeWord_eq_one_iff_eval_dom]
  rw [eval_outputTestCode]
  exact filterFunction_dom_iff q i b

/-- A program computes a total natural-number stream. -/
def ComputesStream (q : Nat.Partrec.Code) (source : ℕ → ℕ) : Prop :=
  ∀ i, Nat.Partrec.Code.eval q i = Part.some (source i)

/-- Every computable stream has a program code. -/
theorem exists_code_computesStream (source : ℕ → ℕ)
    (hsource : Computable source) :
    ∃ q : Nat.Partrec.Code, ComputesStream q source := by
  obtain ⟨q, hq⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp hsource.partrec)
  exact ⟨q, fun i => congrFun hq i⟩

/-- Exact reconstruction theorem.  For every cell, precisely its true value
makes the corresponding invisible word trivial. -/
theorem outputWord_eq_one_iff_cell
    {q : Nat.Partrec.Code} {source : ℕ → ℕ}
    (hq : ComputesStream q source) (i b : ℕ) :
    outputWord q i b = 1 ↔ source i = b := by
  rw [outputWord_eq_one_iff_mem, hq i, Part.mem_some_iff]
  exact eq_comm

/-- Wrong cell guesses are genuinely nonidentity invisible elements; the
encoding does not store every bit by collapsing every query word. -/
theorem outputWord_ne_one_iff_cell_ne
    {q : Nat.Partrec.Code} {source : ℕ → ℕ}
    (hq : ComputesStream q source) (i b : ℕ) :
    outputWord q i b ≠ 1 ↔ source i ≠ b :=
  not_congr (outputWord_eq_one_iff_cell hq i b)

/-- At every source position there is exactly one identity answer. -/
theorem existsUnique_outputWord_eq_one
    {q : Nat.Partrec.Code} {source : ℕ → ℕ}
    (hq : ComputesStream q source) (i : ℕ) :
    ∃! b : ℕ, outputWord q i b = 1 := by
  refine ⟨source i, (outputWord_eq_one_iff_cell hq i (source i)).mpr rfl, ?_⟩
  intro b hb
  exact ((outputWord_eq_one_iff_cell hq i b).mp hb).symm

/-- Closed source-encoding package: every computable source stream has an
exact output program and a complete family of byte-query words, all in the
derived operator-MF residual of the same fixed finitely presented non-MF
group. -/
theorem exists_invisible_source_encoding (source : ℕ → ℕ)
    (hsource : Computable source) :
    ∃ q : Nat.Partrec.Code,
      ComputesStream q source ∧
      (∀ i b, NormMFInvisible (outputWord q i b)) ∧
      (∀ i b, outputWord q i b ∈
        ⁅normMFResidual Carrier, (⊤ : Subgroup Carrier)⁆) ∧
      (∀ i b, outputWord q i b = 1 ↔ source i = b) := by
  obtain ⟨q, hq⟩ := exists_code_computesStream source hsource
  exact ⟨q, hq, outputWord_normMFInvisible q,
    outputWord_mem_commutator_residual q,
    outputWord_eq_one_iff_cell hq⟩

end

end MFRadicalQuine
end GroupApproximation
