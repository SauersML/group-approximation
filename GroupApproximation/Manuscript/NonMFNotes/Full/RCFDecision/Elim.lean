import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.ConjElim
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Prenex

/-!
# Correctness of quantifier elimination

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".

* `qfHolds_elimEx`: `elimEx i f` is a quantifier-free formula equivalent to `∃ x_i, f`.
  A disjunctive normal form is a disjunction of conjunctions, and `∃` commutes with
  `∨`, so this reduces to `good_conjTree`.
* `qfHolds_elimAll`: `elimAll qs f` is equivalent to the prenex formula `qs. f`.
  Universal quantifiers are handled through `∀ = ¬ ∃ ¬` (`qfHolds_not`).
* `decidePrenex_iff`: `decidePrenex φ = true` exactly when `φ` holds at the zero
  assignment.
-/

namespace GroupApproximation.Full.NN11b

theorem qfHolds_iff_exists (ρ : ℕ → ℝ) (f : List (List Atom)) :
    qfHolds ρ f ↔ ∃ c ∈ f, guardHolds ρ c :=
  Iff.rfl

/-- **One existential quantifier**: `elimEx i f` is equivalent to `∃ x_i, f`. -/
theorem qfHolds_elimEx (ρ : ℕ → ℝ) (i : ℕ) (f : List (List Atom)) :
    qfHolds ρ (elimEx i f) ↔ ∃ r : ℝ, qfHolds (Function.update ρ i r) f := by
  show qfHolds ρ (f.flatMap fun c => toQF (conjTree i c)) ↔ _
  constructor
  · intro h
    obtain ⟨d, hd, hg⟩ := (qfHolds_iff_exists ρ _).1 h
    obtain ⟨c, hc, hd'⟩ := List.mem_flatMap.1 hd
    obtain ⟨r, hr⟩ :=
      (qfHolds_toQF (good_conjTree ρ i c)).1 ((qfHolds_iff_exists ρ _).2 ⟨d, hd', hg⟩)
    exact ⟨r, (qfHolds_iff_exists _ f).2 ⟨c, hc, hr⟩⟩
  · rintro ⟨r, h⟩
    obtain ⟨c, hc, hr⟩ := (qfHolds_iff_exists _ f).1 h
    obtain ⟨d, hd', hg⟩ :=
      (qfHolds_iff_exists ρ _).1 ((qfHolds_toQF (good_conjTree ρ i c)).2 ⟨r, hr⟩)
    exact (qfHolds_iff_exists ρ _).2 ⟨d, List.mem_flatMap.2 ⟨c, hc, hd'⟩, hg⟩

/-- **Quantifier elimination**: `elimAll qs f` is equivalent to the prenex formula `qs. f`. -/
theorem qfHolds_elimAll : ∀ (qs : List (Bool × ℕ)) (f : List (List Atom)) (ρ : ℕ → ℝ),
    qfHolds ρ (elimAll qs f) ↔ PHolds qs f ρ
  | [], _, _ => Iff.rfl
  | (true, i) :: qs, f, ρ => by
      show qfHolds ρ (elimEx i (elimAll qs f)) ↔ ∃ r : ℝ, PHolds qs f (Function.update ρ i r)
      rw [qfHolds_elimEx]
      exact exists_congr fun r => qfHolds_elimAll qs f (Function.update ρ i r)
  | (false, i) :: qs, f, ρ => by
      show qfHolds ρ (qfNot (elimEx i (qfNot (elimAll qs f)))) ↔
        ∀ r : ℝ, PHolds qs f (Function.update ρ i r)
      rw [qfHolds_not, qfHolds_elimEx, not_exists]
      refine forall_congr' fun r => ?_
      rw [qfHolds_not, not_not]
      exact qfHolds_elimAll qs f (Function.update ρ i r)

/-- **Decision procedure for prenex sentences**: `decidePrenex φ = true` iff `φ` holds at the
zero assignment. -/
theorem decidePrenex_iff (φ : List (Bool × ℕ) × List (List Atom)) :
    decidePrenex φ = true ↔ PHolds φ.1 φ.2 (fun _ => 0) := by
  show qfZ (elimAll φ.1 φ.2) = true ↔ _
  rw [qfZ_iff]
  exact qfHolds_elimAll φ.1 φ.2 _

end GroupApproximation.Full.NN11b
