import GroupApproximation.Computability.FreeGroupRedNil

/-!
# Deletion sequences as certificates

`FreeGroupRedNil` identifies freeness-triviality with `FreeGroup.Red L []`, a
finite sequence of deletions of adjacent inverse pairs.  For `D2` that sequence
has to be a *certificate*: a concrete list of positions that a checker can
verify without ever handling a free-group element, since `FreeGroup` has no
`Primcodable` instance at this Mathlib revision and cannot be searched over.

* `deleteAt L i` deletes the pair at position `i` when a letter is followed by
  its inverse there, and fails otherwise.  It recurses structurally on the word
  and the position, so the two directions below are inductions rather than
  `take`/`drop` bookkeeping.
* `applySteps L is` replays a list of positions.
* `mk_eq_one_iff_exists_steps` — triviality of a raw word is the existence of a
  deletion certificate, a statement about `List (α × Bool)` with no group in it.

Neither direction needs confluence or normal forms: the certificate names the
positions, so the checker replays a sequence instead of searching for one.
Soundness is `Red.Step.cons_not` and `Red.Step.cons`; completeness is that a
`Red.Step` deletes at the position its own constructor names, which is an
induction on the prefix.
-/

namespace GroupApproximation
namespace Computability

open FreeGroup

variable {α : Type*} [DecidableEq α]

/-- Delete the adjacent inverse pair at position `i`, if there is one. -/
def deleteAt : List (α × Bool) → ℕ → Option (List (α × Bool))
  | (x, b) :: (y, c) :: t, 0 => if x = y ∧ c = !b then some t else none
  | p :: t, (i + 1) => (deleteAt t i).map fun t' => p :: t'
  | _, _ => none

/-- Replay a list of deletion positions. -/
def applySteps (L : List (α × Bool)) : List ℕ → Option (List (α × Bool))
  | [] => some L
  | i :: is => (deleteAt L i).bind fun L' => applySteps L' is

@[simp] theorem applySteps_nil (L : List (α × Bool)) : applySteps L [] = some L := rfl

@[simp] theorem applySteps_cons (L : List (α × Bool)) (i : ℕ) (is : List ℕ) :
    applySteps L (i :: is) = (deleteAt L i).bind fun L' => applySteps L' is := rfl

/-- **Soundness of one deletion.**  A successful `deleteAt` is a `Red.Step`, so
no certificate can manufacture a false positive. -/
theorem red_step_of_deleteAt : ∀ (L : List (α × Bool)) (i : ℕ) (L' : List (α × Bool)),
    deleteAt L i = some L' → FreeGroup.Red.Step L L'
  | (x, b) :: (y, c) :: t, 0, L', h => by
      simp only [deleteAt] at h
      by_cases hxy : x = y ∧ c = !b
      · rw [if_pos hxy] at h
        obtain ⟨rfl, rfl⟩ := hxy
        cases h
        exact FreeGroup.Red.Step.cons_not
      · rw [if_neg hxy] at h
        exact absurd h (by simp)
  | p :: t, (i + 1), L', h => by
      simp only [deleteAt] at h
      cases hd : deleteAt t i with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some t' =>
          rw [hd] at h
          simp only [Option.map_some] at h
          cases h
          exact (red_step_of_deleteAt t i t' hd).cons
  | [], _, _, h => by simp [deleteAt] at h
  | [_], 0, _, h => by simp [deleteAt] at h

/-- **Soundness.**  A certificate reaching `[]` proves triviality. -/
theorem red_nil_of_applySteps :
    ∀ (is : List ℕ) (L : List (α × Bool)), applySteps L is = some [] → FreeGroup.Red L []
  | [], L, h => by
      rw [applySteps_nil] at h
      cases h
      exact FreeGroup.Red.refl
  | (i :: is), L, h => by
      rw [applySteps_cons] at h
      cases hd : deleteAt L i with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some L' =>
          rw [hd] at h
          simp only [Option.bind_some] at h
          exact (red_step_of_deleteAt L i L' hd).to_red.trans
            (red_nil_of_applySteps is L' h)

/-- **Completeness of one step.**  A `Red.Step` deletes at the position its own
constructor names, namely the length of the prefix it splits off. -/
theorem exists_deleteAt_of_red_step {L L' : List (α × Bool)}
    (h : FreeGroup.Red.Step L L') : ∃ i, deleteAt L i = some L' := by
  cases h with
  | @not L₁ L₂ x b =>
      refine ⟨L₁.length, ?_⟩
      induction L₁ with
      | nil => simp [deleteAt]
      | cons p t ih => simpa [deleteAt] using ih

/-- **Completeness.**  Triviality is witnessed by a list of positions. -/
theorem exists_applySteps_of_red_nil {L : List (α × Bool)} (h : FreeGroup.Red L []) :
    ∃ is : List ℕ, applySteps L is = some [] := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], rfl⟩
  | head hstep _ ih =>
      obtain ⟨is, his⟩ := ih
      obtain ⟨i, hi⟩ := exists_deleteAt_of_red_step hstep
      exact ⟨i :: is, by rw [applySteps_cons, hi, Option.bind_some, his]⟩

/-- **The certificate characterisation.** -/
theorem red_nil_iff_exists_steps {L : List (α × Bool)} :
    FreeGroup.Red L [] ↔ ∃ is : List ℕ, applySteps L is = some [] :=
  ⟨exists_applySteps_of_red_nil, fun ⟨is, h⟩ => red_nil_of_applySteps is L h⟩

/-- **The form `D2` consumes.**  A raw word is trivial in the free group exactly
when a deletion certificate exists — no free-group element is quantified over. -/
theorem mk_eq_one_iff_exists_steps {L : List (α × Bool)} :
    FreeGroup.mk L = 1 ↔ ∃ is : List ℕ, applySteps L is = some [] :=
  mk_eq_one_iff_red_nil.trans red_nil_iff_exists_steps

end Computability
end GroupApproximation
