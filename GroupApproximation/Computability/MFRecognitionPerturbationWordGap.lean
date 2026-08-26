import GroupApproximation.Computability.MFRecognitionOpenCore

/-!
# Word-evaluation perturbation bounds for MF microstates
-/

namespace GroupApproximation
namespace MFRecognitionPi02

open PresentationCodes AdianRabinWordProblem RawWord
open EffectiveMatrixCode EffectiveMatrixCodePrimrec
open EffectiveOperatorNormCode
open CodedMicrostateEncoding EffectiveMicrostateSemantics MFMicrostate
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

/-- Evaluate one signed raw letter in a tuple of unitaries. -/
def tupleLetter {c : PresentationCode} {Y : FiniteModel}
    (U : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) (p : ℕ × Bool) :
    Matrix.unitaryGroup Y ℂ :=
  if p.2 then U (letterOf c p.1) else (U (letterOf c p.1))⁻¹

/-- Evaluate a raw word in a tuple of unitaries. -/
def tupleWord {c : PresentationCode} {Y : FiniteModel}
    (U : Fin (genCount c) → Matrix.unitaryGroup Y ℂ)
    (w : List (ℕ × Bool)) : Matrix.unitaryGroup Y ℂ :=
  (w.map (tupleLetter U)).prod

theorem microstate_hom_wordOf_eq_tupleWord {c : PresentationCode}
    (M : Microstate c) (w : List (ℕ × Bool)) :
    M.hom (wordOf c w) = tupleWord M.gen w := by
  induction w with
  | nil =>
      rw [wordOf_nil, map_one]
      rfl
  | cons p w ih =>
      obtain ⟨i, s⟩ := p
      cases s
      · rw [wordOf_cons_neg, map_mul, map_inv, ih]
        simp only [tupleWord, tupleLetter, List.map_cons, List.prod_cons,
          Bool.false_eq_true, if_false]
        rw [Microstate.hom, FreeGroup.lift_apply_of]
      · rw [wordOf_cons_pos, map_mul, ih]
        simp only [tupleWord, tupleLetter, List.map_cons, List.prod_cons, if_true]
        rw [Microstate.hom, FreeGroup.lift_apply_of]

private theorem tupleLetter_gap {c : PresentationCode} {Y : FiniteModel}
    (U V : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) {η : ℝ}
    (hclose : ∀ i, ‖(U i : Matrix Y Y ℂ) - (V i : Matrix Y Y ℂ)‖ < η)
    (p : ℕ × Bool) :
    ‖(tupleLetter U p : Matrix Y Y ℂ) -
        (tupleLetter V p : Matrix Y Y ℂ)‖ < η := by
  obtain ⟨i, s⟩ := p
  cases s
  · simpa [tupleLetter] using
      (show ‖(((U (letterOf c i))⁻¹ : Matrix.unitaryGroup Y ℂ) :
          Matrix Y Y ℂ) -
          (((V (letterOf c i))⁻¹ : Matrix.unitaryGroup Y ℂ) :
            Matrix Y Y ℂ)‖ < η from by
        rw [norm_inv_sub_inv_unitary]
        exact hclose (letterOf c i))
  · simpa [tupleLetter] using hclose (letterOf c i)

/-- Telescoping bound for a finite word evaluated in two unitary tuples. -/
theorem tupleWord_gap_le {c : PresentationCode} {Y : FiniteModel}
    (U V : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) {η : ℝ}
    (hclose : ∀ i, ‖(U i : Matrix Y Y ℂ) - (V i : Matrix Y Y ℂ)‖ < η) :
    ∀ w : List (ℕ × Bool),
      ‖(tupleWord U w : Matrix Y Y ℂ) -
          (tupleWord V w : Matrix Y Y ℂ)‖ ≤ (w.length : ℝ) * η
  | [] => by simp [tupleWord]
  | p :: w => by
      have hstep := norm_mul_sub_mul_unitary_le
        (tupleLetter U p) (tupleLetter V p) (tupleWord U w) (tupleWord V w)
      have hp := (tupleLetter_gap U V hclose p).le
      have hw := tupleWord_gap_le U V hclose w
      simp only [tupleWord, List.map_cons, List.prod_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      calc
        ‖(tupleLetter U p : Matrix Y Y ℂ) *
            (tupleWord U w : Matrix Y Y ℂ) -
            (tupleLetter V p : Matrix Y Y ℂ) *
              (tupleWord V w : Matrix Y Y ℂ)‖ ≤
            ‖(tupleLetter U p : Matrix Y Y ℂ) -
              (tupleLetter V p : Matrix Y Y ℂ)‖ +
            ‖(tupleWord U w : Matrix Y Y ℂ) -
              (tupleWord V w : Matrix Y Y ℂ)‖ := hstep
        _ ≤ η + (w.length : ℝ) * η := add_le_add hp hw
        _ = ((w.length : ℝ) + 1) * η := by ring

/-- Perturbing each generator by `η` changes the word displacement from the
identity by at most `length * η`. -/
theorem abs_tupleLength_sub_le {c : PresentationCode} {Y : FiniteModel}
    (U V : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) {η : ℝ}
    (hclose : ∀ i,
      ‖(U i : Matrix Y Y ℂ) - (V i : Matrix Y Y ℂ)‖ < η)
    (w : List (ℕ × Bool)) :
    |‖(tupleWord U w : Matrix Y Y ℂ) - 1‖ -
        ‖(tupleWord V w : Matrix Y Y ℂ) - 1‖| ≤
      (w.length : ℝ) * η := by
  refine (abs_norm_sub_norm_le
    ((tupleWord U w : Matrix Y Y ℂ) - 1)
    ((tupleWord V w : Matrix Y Y ℂ) - 1)).trans ?_
  have hgap := tupleWord_gap_le U V hclose w
  simpa only [sub_sub_sub_cancel_right] using hgap

end
end MFRecognitionPi02
end GroupApproximation
