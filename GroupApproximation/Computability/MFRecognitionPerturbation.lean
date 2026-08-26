import GroupApproximation.Computability.MFRecognitionPerturbationWordGap
import GroupApproximation.Computability.MicrostateGeneratorEncoding

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
  obtain ⟨gens, hunitary, hcodeClose⟩ :=
    MicrostateGeneratorEncoding.exists_generatorCodes_close M d e hη
  let C : Microstate c := toMicrostate c d gens hunitary
  let U : Fin (genCount c) → Matrix.unitaryGroup (Fin (dim d)) ℂ :=
    fun i => unitaryReindexEquiv e (M.gen i)
  let V : Fin (genCount c) → Matrix.unitaryGroup (Fin (dim d)) ℂ :=
    fun i => C.gen i
  have hclose : ∀ i,
      ‖(U i : Matrix (Fin (dim d)) (Fin (dim d)) ℂ) -
        (V i : Matrix (Fin (dim d)) (Fin (dim d)) ℂ)‖ < η := by
    intro i
    simpa [U, V, C, EffectiveMicrostateSemantics.toMicrostate] using hcodeClose i
  have hNgen : N.gen = U := by rfl
  have hCgen : C.gen = V := by rfl
  have hgap (w : List (ℕ × Bool)) :
      |N.len w - C.len w| ≤ (w.length : ℝ) * η := by
    rw [microstate_len_eq_tupleWord C w, hCgen]
    apply abs_microstate_len_tupleWord_sub_le
    intro i
    rw [hNgen]
    exact hclose i
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
