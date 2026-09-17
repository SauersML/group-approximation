import GroupApproximation.Computability.MicrostateNaturalize
import GroupApproximation.Computability.MFRecognitionOpenCore

/-!
# `thm:mf-radical-arithmetic`: the literal predicate `D(P,v,n,d)`

Manuscript `non_mf_group_notes.tex`, `thm:mf-radical-arithmetic`, proof:

> "Let `D(P,v,n,d)` assert the existence of `d`-dimensional generator unitaries
> with relator defect at most `2^{-n-10}` and `‖v(U)-1‖ ≥ 1/2`."

This file defines `D(P,v,n,d)` exactly as printed (`LiteralD`): the generator
unitaries live in `U(d) = Matrix.unitaryGroup (Fin d) ℂ`, the norm is the
operator norm, every relator `r` of `P` satisfies `‖r(U) - 1‖ ≤ 2^{-n-10}`,
and `‖v(U) - 1‖ ≥ 1/2`.  It then proves the elementary estimates the proof
uses about these constants:

* `literalDefectBound_eq`, `literalDefectBound_pos`, `literalDefectBound_antitone`,
  `literalD_mono`: the defect scale `2^{-n-10}` is positive and decreasing in `n`;
* `literalD_dim_pos`: `D(P,v,n,d)` forces `d > 0`;
* `literalDefectBound_lt`: `2^{-k-10} < 1/(k+1)`;
* `literalMicrostate_len`, `literalD_of_microstate`: the bridge between `d`-dimensional
  generator unitaries and the repository's microstates.
-/

namespace GroupApproximation.Full.NN02b

open PresentationCodes AdianRabinWordProblem MFMicrostate
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## The constants -/

/-- The printed defect scale `2^{-n-10}` of `D(P,v,n,d)`. -/
def literalDefectBound (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℤ) - 10)

theorem literalDefectBound_eq (n : ℕ) :
    literalDefectBound n = ((2 : ℝ) ^ (n + 10))⁻¹ := by
  rw [literalDefectBound, show -(n : ℤ) - 10 = -((n + 10 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast]

theorem literalDefectBound_pos (n : ℕ) : 0 < literalDefectBound n := by
  rw [literalDefectBound_eq]
  positivity

/-- The defect scale decreases with the level. -/
theorem literalDefectBound_antitone {m n : ℕ} (hmn : m ≤ n) :
    literalDefectBound n ≤ literalDefectBound m := by
  rw [literalDefectBound_eq, literalDefectBound_eq]
  apply inv_anti₀
  · positivity
  · exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- `2^{-k-10} < 1/(k+1)`: the printed scale is finer than the open test
`1/(k+1)` of `MFRecognitionPi02.PassesOpen`. -/
theorem literalDefectBound_lt (k : ℕ) :
    literalDefectBound k < 1 / ((k : ℝ) + 1) := by
  have hnat : k + 1 < 2 ^ (k + 10) :=
    lt_of_lt_of_le (@Nat.lt_two_pow_self (k + 1))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hreal : ((k + 1 : ℕ) : ℝ) < ((2 ^ (k + 10) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hreal
  rw [literalDefectBound_eq, one_div]
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2 hreal

/-! ## The predicate -/

/-- The value `w(U)` of a raw word at `d`-dimensional generator unitaries. -/
def literalWordValue (c : PresentationCode) {d : ℕ}
    (U : Fin (genCount c) → Matrix.unitaryGroup (Fin d) ℂ) (w : List (ℕ × Bool)) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  FreeGroup.lift U (wordOf c w)

/-- **`D(P,v,n,d)`, as printed** (`non_mf_group_notes.tex`,
proof of `thm:mf-radical-arithmetic`): there are `d`-dimensional generator
unitaries `U` with relator defect at most `2^{-n-10}` and `‖v(U) - 1‖ ≥ 1/2`
(operator norm). -/
def LiteralD (c : PresentationCode) (v : List (ℕ × Bool)) (n d : ℕ) : Prop :=
  ∃ U : Fin (genCount c) → Matrix.unitaryGroup (Fin d) ℂ,
    (∀ r ∈ c.2,
      ‖((literalWordValue c U r : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) - 1‖
        ≤ literalDefectBound n) ∧
    1 / 2 ≤
      ‖((literalWordValue c U v : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) - 1‖

/-- `D(P,v,n,d)` is monotone downward in the level `n`. -/
theorem literalD_mono {c : PresentationCode} {v : List (ℕ × Bool)} {m n d : ℕ}
    (hmn : m ≤ n) (h : LiteralD c v n d) : LiteralD c v m d := by
  obtain ⟨U, hrel, hv⟩ := h
  exact ⟨U, fun r hr => (hrel r hr).trans (literalDefectBound_antitone hmn), hv⟩

/-- `D(P,v,n,d)` can only hold in positive dimension: on `Fin 0` every matrix
is zero, so `‖v(U) - 1‖ = 0 < 1/2`. -/
theorem literalD_dim_pos {c : PresentationCode} {v : List (ℕ × Bool)} {n d : ℕ}
    (h : LiteralD c v n d) : 0 < d := by
  obtain ⟨U, _, hv⟩ := h
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · exfalso
    subst hd0
    have h0 : ((literalWordValue c U v : Matrix.unitaryGroup (Fin 0) ℂ) :
        Matrix (Fin 0) (Fin 0) ℂ) - 1 = 0 :=
      Matrix.ext fun i _ => Fin.elim0 i
    rw [h0, norm_zero] at hv
    norm_num at hv
  · exact hd

/-! ## Bridge to microstates -/

/-- The microstate on the literal natural basis `Fin d` carried by
`d`-dimensional generator unitaries. -/
def literalMicrostate (c : PresentationCode) {d : ℕ} (hd : 0 < d)
    (U : Fin (genCount c) → Matrix.unitaryGroup (Fin d) ℂ) : Microstate c where
  model := naturalFiniteModel d
  card_pos := Fintype.card_pos_iff.2 ⟨(⟨0, hd⟩ : Fin d)⟩
  gen := U

theorem literalMicrostate_len (c : PresentationCode) {d : ℕ} (hd : 0 < d)
    (U : Fin (genCount c) → Matrix.unitaryGroup (Fin d) ℂ) (w : List (ℕ × Bool)) :
    (literalMicrostate c hd U).len w =
      ‖((literalWordValue c U w : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) - 1‖ :=
  rfl

/-- A microstate on any finite model with defects at most `2^{-n-10}` and
`v`-displacement at least `1/2` witnesses `D(P,v,n,d)` in its own dimension. -/
theorem literalD_of_microstate {c : PresentationCode} {v : List (ℕ × Bool)} {n : ℕ}
    (M : Microstate c) (hrel : ∀ r ∈ c.2, M.len r ≤ literalDefectBound n)
    (hv : 1 / 2 ≤ M.len v) : LiteralD c v n (Fintype.card M.model) := by
  refine ⟨M.naturalize.gen, fun r hr => ?_, ?_⟩
  · have h : M.naturalize.len r ≤ literalDefectBound n := by
      rw [Microstate.naturalize_len]
      exact hrel r hr
    exact h
  · have h : 1 / 2 ≤ M.naturalize.len v := by
      rw [Microstate.naturalize_len]
      exact hv
    exact h

end

end GroupApproximation.Full.NN02b
