import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Tree

/-!
# Semantics of prenex sentences

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field": a prenex formula is a
quantifier prefix `qs` (`(true, i)` is `∃ x_i`, `(false, i)` is `∀ x_i`, outermost
first) over a quantifier-free matrix in disjunctive normal form.
-/

namespace GroupApproximation.Full.NN11b

/-- Truth of the prenex formula `qs. f` at the assignment `ρ`. -/
def PHolds : List (Bool × ℕ) → List (List Atom) → (ℕ → ℝ) → Prop
  | [], f, ρ => qfHolds ρ f
  | (true, i) :: qs, f, ρ => ∃ r : ℝ, PHolds qs f (Function.update ρ i r)
  | (false, i) :: qs, f, ρ => ∀ r : ℝ, PHolds qs f (Function.update ρ i r)

theorem pHolds_nil (f : List (List Atom)) (ρ : ℕ → ℝ) : PHolds [] f ρ ↔ qfHolds ρ f :=
  Iff.rfl

theorem pHolds_ex (i : ℕ) (qs : List (Bool × ℕ)) (f : List (List Atom)) (ρ : ℕ → ℝ) :
    PHolds ((true, i) :: qs) f ρ ↔ ∃ r : ℝ, PHolds qs f (Function.update ρ i r) :=
  Iff.rfl

theorem pHolds_all (i : ℕ) (qs : List (Bool × ℕ)) (f : List (List Atom)) (ρ : ℕ → ℝ) :
    PHolds ((false, i) :: qs) f ρ ↔ ∀ r : ℝ, PHolds qs f (Function.update ρ i r) :=
  Iff.rfl

end GroupApproximation.Full.NN11b
