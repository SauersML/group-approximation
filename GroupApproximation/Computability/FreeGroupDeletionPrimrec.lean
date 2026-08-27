import GroupApproximation.Computability.FreeGroupDeletion
import Mathlib.Computability.Primrec.List

/-!
# The deletion checker, in the form `Primrec` can follow

`FreeGroupDeletion` characterises freeness-triviality by a positional
certificate.  For `D2` the checker that verifies such a certificate has to be
primitive recursive.  This module supplies what that proof needs and does not
itself prove it: the two closed forms below, from which the `Primrec` facts
follow by the list API alone.

The structural definition of `deleteAt` is convenient for the two `Red`
inductions and useless for `Primrec`, which cannot see a recursion that consumes
a list and an index in lockstep.  So the definition is first re-presented in
closed form,

    deleteAt L i = if cancelsAt L i then some (L.take i ++ L.drop (i + 2)) else none

with `cancelsAt` a `Bool` test on `L[i]?` and `L[i+1]?`, and `applySteps` as a
`List.foldl`.  Both forms sit inside Mathlib's `Primrec` list API --- `list_getElem?`,
`list_take`, `list_drop`, `list_append`, `list_foldl` --- so what remains for
the checker is combinator bookkeeping over `Option` case analysis, with no
further mathematics.

That closed form is also the reason the raw-word route was recommended over
encoding free-group elements: every operation in it is a list operation, and
`FreeGroup` has no `Primcodable` instance to search over in the first place.
-/

namespace GroupApproximation
namespace Computability

variable {α : Type*} [DecidableEq α]

/-- Does a letter sit immediately before its inverse at position `i`? -/
def cancelsAt (L : List (α × Bool)) (i : ℕ) : Bool :=
  match L[i]?, L[i + 1]? with
  | some (x, b), some (y, c) => x == y && c == !b
  | _, _ => false

@[simp] theorem cancelsAt_nil (i : ℕ) : cancelsAt ([] : List (α × Bool)) i = false := by
  simp [cancelsAt]

@[simp] theorem cancelsAt_cons_succ (p : α × Bool) (t : List (α × Bool)) (i : ℕ) :
    cancelsAt (p :: t) (i + 1) = cancelsAt t i := by
  simp [cancelsAt]

/-- **The closed form.**  Same function, expressed with `take`, `drop` and a
`Bool` test, which is what the `Primrec` API can follow. -/
theorem deleteAt_eq_ite : ∀ (L : List (α × Bool)) (i : ℕ),
    deleteAt L i = if cancelsAt L i then some (L.take i ++ L.drop (i + 2)) else none
  | [], i => by cases i <;> simp [deleteAt]
  | [p], 0 => by simp [deleteAt, cancelsAt]
  | (x, b) :: (y, c) :: t, 0 => by
      simp only [deleteAt, cancelsAt, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.take_zero, List.nil_append, List.drop_succ_cons, List.drop_zero]
      by_cases h : x = y ∧ c = !b
      · obtain ⟨rfl, rfl⟩ := h
        simp
      · rw [if_neg h]
        have : ¬ (x == y && c == !b) = true := by
          simpa [Bool.and_eq_true, beq_iff_eq] using h
        simp [this]
  | p :: t, (i + 1) => by
      simp only [deleteAt, deleteAt_eq_ite t i, cancelsAt_cons_succ,
        List.take_succ_cons, List.drop_succ_cons]
      cases cancelsAt t i <;> simp

/-- Once the replay fails it stays failed. -/
theorem foldl_deleteAt_none (is : List ℕ) :
    is.foldl (fun acc i => acc.bind fun M => deleteAt M i)
        (none : Option (List (α × Bool))) = none := by
  induction is with
  | nil => rfl
  | cons i is ih => simpa using ih

/-- `applySteps` is a fold, which is the shape `Primrec.list_foldl` consumes. -/
theorem applySteps_eq_foldl : ∀ (L : List (α × Bool)) (is : List ℕ),
    applySteps L is = is.foldl (fun acc i => acc.bind fun M => deleteAt M i) (some L)
  | L, [] => by simp
  | L, (i :: is) => by
      rw [applySteps_cons, List.foldl_cons, Option.bind_some]
      cases hd : deleteAt L i with
      | none => simp [foldl_deleteAt_none]
      | some L' => simpa using applySteps_eq_foldl L' is

end Computability
end GroupApproximation
