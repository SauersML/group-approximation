import GroupApproximation.Computability.MFRecognitionOpenCore

/-!
# Finite-dimensional rational perturbation for MF microstates
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
  | nil => simp [tupleWord]
  | cons p w ih =>
      obtain ⟨i, s⟩ := p
      cases s
      · rw [wordOf_cons_neg, map_mul, map_inv, ih]
        simp [tupleWord, tupleLetter, letterOf]
      · rw [wordOf_cons_pos, map_mul, ih]
        simp [tupleWord, tupleLetter, letterOf]

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

/-- A finite list of positive word margins admits one positive generator
tolerance satisfying all length-weighted bounds. -/
theorem exists_word_tolerance (L : List (List (ℕ × Bool)))
    (margin : List (ℕ × Bool) → ℝ)
    (hmargin : ∀ w ∈ L, 0 < margin w) :
    ∃ η : ℝ, 0 < η ∧
      ∀ w ∈ L, (w.length : ℝ) * η < margin w := by
  induction L with
  | nil => exact ⟨1, by norm_num, by simp⟩
  | cons a L ih =>
      obtain ⟨η, hη, hL⟩ := ih (fun w hw ↦ hmargin w (List.mem_cons_of_mem _ hw))
      let δ : ℝ := min (margin a / ((a.length : ℝ) + 1)) η / 2
      have hma : 0 < margin a := hmargin a List.mem_cons_self
      have hδ : 0 < δ := by
        dsimp [δ]
        positivity
      refine ⟨δ, hδ, ?_⟩
      intro w hw
      rcases List.mem_cons.1 hw with hwa | hw
      · subst w
        have hle : δ < margin a / ((a.length : ℝ) + 1) := by
          dsimp [δ]
          have hmin : 0 < min (margin a / ((a.length : ℝ) + 1)) η := by
            positivity
          have hhalf : min (margin a / ((a.length : ℝ) + 1)) η / 2 <
              min (margin a / ((a.length : ℝ) + 1)) η := by linarith
          exact hhalf.trans_le (min_le_left _ _)
        have hlen : (a.length : ℝ) < (a.length : ℝ) + 1 := by linarith
        calc
          (a.length : ℝ) * δ ≤ ((a.length : ℝ) + 1) * δ :=
            mul_le_mul_of_nonneg_right hlen.le hδ.le
          _ < ((a.length : ℝ) + 1) *
              (margin a / ((a.length : ℝ) + 1)) :=
            mul_lt_mul_of_pos_left hle (by positivity)
          _ = margin a := by field_simp
      · have hδη : δ ≤ η := by
          dsimp [δ]
          have hmin := min_le_right (margin a / ((a.length : ℝ) + 1)) η
          nlinarith
        exact (mul_le_mul_of_nonneg_left hδη (by positivity)).trans_lt (hL w hw)

/-- Every strict-open microstate packet has a witness consisting of exactly
unitary Gaussian-rational matrix codes. -/
theorem exists_coded_openPasses {c : PresentationCode}
    {W : List (List (ℕ × Bool))} {k : ℕ} (M : Microstate c)
    (hM : PassesOpen c W k M) :
    ∃ d : ℕ, ∃ gens : List MatrixCode,
      ∃ hunitary : GeneratorsUnitary c d gens,
        PassesOpen c W k (toMicrostate c d gens hunitary) := by
  classical
  have hcard : Fintype.card M.model ≠ 0 := Nat.ne_of_gt M.card_pos
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hcard
  have hdim : Fintype.card M.model = dim d := by simpa [dim] using hd
  let e : M.model ≃ Fin (dim d) :=
    (Fintype.equivFin M.model).trans (finCongr hdim)
  let N : Microstate c := M.reindex (naturalFiniteModel (dim d)) e
  have hNlen (w : List (ℕ × Bool)) : N.len w = M.len w := by
    exact Microstate.reindex_len M (naturalFiniteModel (dim d)) e w
  have hNrel : ∀ r ∈ c.2, N.len r < 1 / ((k : ℝ) + 1) := by
    intro r hr
    rw [hNlen]
    exact hM.1 r hr
  have hNsep : ∀ w ∈ W, 1 / 3 < N.len w := by
    intro w hw
    rw [hNlen]
    exact hM.2 w hw
  obtain ⟨ηr, hηr, hrelMargin⟩ := exists_word_tolerance c.2
    (fun r ↦ 1 / ((k : ℝ) + 1) - N.len r) (by
      intro r hr
      have := hNrel r hr
      linarith)
  obtain ⟨ηw, hηw, hwordMargin⟩ := exists_word_tolerance W
    (fun w ↦ N.len w - 1 / 3) (by
      intro w hw
      have := hNsep w hw
      linarith)
  let η : ℝ := min ηr ηw / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηr_le : η ≤ ηr := by
    dsimp [η]
    have := min_le_left ηr ηw
    nlinarith
  have hηw_le : η ≤ ηw := by
    dsimp [η]
    have := min_le_right ηr ηw
    nlinarith
  have hcodes : ∀ i : Fin (genCount c), ∃ C : MatrixCode,
      isUnitary d C ∧
        ‖(N.gen i : Matrix (Fin (dim d)) (Fin (dim d)) ℂ) -
          toMatrix d C‖ < η := by
    intro i
    exact RationalMatrixEncoding.exists_unitary_matrixCode_close d
      (N.gen i).2 hη
  choose code hcodeUnit hcodeClose using hcodes
  let gens : List MatrixCode := List.ofFn code
  have hgenerator (i : Fin (genCount c)) : generator d gens i = code i := by
    simp [generator, gens, List.getD_eq_getElem?_getD, i.isLt]
  have hunitary : GeneratorsUnitary c d gens := by
    intro i
    rw [hgenerator]
    exact hcodeUnit i
  let C : Microstate c := toMicrostate c d gens hunitary
  have hclose : ∀ i,
      ‖(N.gen i : Matrix (Fin (dim d)) (Fin (dim d)) ℂ) -
        (C.gen i : Matrix (Fin (dim d)) (Fin (dim d)) ℂ)‖ < η := by
    intro i
    simpa [C, toMicrostate, hgenerator i] using hcodeClose i
  have hgap (w : List (ℕ × Bool)) :
      |N.len w - C.len w| ≤ (w.length : ℝ) * η := by
    rw [Microstate.len_def, Microstate.len_def,
      microstate_hom_wordOf_eq_tupleWord,
      microstate_hom_wordOf_eq_tupleWord]
    exact abs_tupleLength_sub_le N.gen C.gen hclose w
  refine ⟨d, gens, hunitary, ?_, ?_⟩
  · intro r hr
    have hmarginη : (r.length : ℝ) * η <
        1 / ((k : ℝ) + 1) - N.len r :=
      (mul_le_mul_of_nonneg_left hηr_le (by positivity)).trans_lt
        (hrelMargin r hr)
    have habs := hgap r
    have hside : C.len r - N.len r ≤ (r.length : ℝ) * η :=
      (le_abs_self _).trans habs
    linarith
  · intro w hw
    have hmarginη : (w.length : ℝ) * η < N.len w - 1 / 3 :=
      (mul_le_mul_of_nonneg_left hηw_le (by positivity)).trans_lt
        (hwordMargin w hw)
    have habs := hgap w
    have hside : N.len w - C.len w ≤ (w.length : ℝ) * η :=
      (le_abs_self _).trans habs
    linarith

end
end MFRecognitionPi02
end GroupApproximation
