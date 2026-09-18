import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.Holds

/-!
# `Φ(P, n, c)` over the model `Fin (certDim c)`

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, proof sentence `4b85128c696d`
("there are `U_1, …, U_k ∈ U(d)` with `‖r_i(U) - 1‖ ≤ 2^{-n}` … and
`‖w(U) - 1‖ ≥ 1/4` for every word `w` labelled `S`"), printed sentence
`9eae4d68673a`.  A microstate of dimension `d` is transported to the model
`Fin d` along an equivalence; the operator norm is invariant under this
reindexing (`norm_submatrix_equiv`).  Hence `PhiSpec P n c` is the matrix condition
`MatCond` on tuples of `d × d` unitaries (`phiSpec_iff_matCond`).
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.PresentationCodes GroupApproximation.MFMicrostate Matrix

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

/-- The matrix condition of `prop:mf-upper-bound` on `d × d` unitaries. -/
def MatCond (P : PresentationCode) (n d : ℕ) (S : List (List (ℕ × Bool))) : Prop :=
  1 ≤ d ∧ ∃ U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ,
    (∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
      (∀ r ∈ P.2, ‖encWordMat P U r - 1‖ ≤ (1 / 2 : ℝ) ^ n) ∧
        ∀ w ∈ S, (1 / 4 : ℝ) ≤ ‖encWordMat P U w - 1‖

theorem norm_submatrix_equiv_le {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z]
    [DecidableEq Z] (X : Matrix Y Y ℂ) (e : Y ≃ Z) :
    ‖X.submatrix e.symm e.symm‖ ≤ ‖X‖ := by
  refine (Manuscript.MFRecognition.Certificates.l2_opNorm_le_iff_quadraticForm_nonneg _
    (norm_nonneg X)).2 fun v => ?_
  have h1 := (Manuscript.MFRecognition.Certificates.l2_opNorm_le_iff_quadraticForm_nonneg X
    (norm_nonneg X)).1 le_rfl (v ∘ e)
  have hv : X.submatrix e.symm e.symm *ᵥ v = (X *ᵥ (v ∘ e)) ∘ e.symm := by
    rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]
  have hs1 : ∑ i : Z, Complex.normSq (((X *ᵥ (v ∘ e)) ∘ e.symm) i)
      = ∑ j : Y, Complex.normSq ((X *ᵥ (v ∘ e)) j) :=
    Equiv.sum_comp e.symm (fun j => Complex.normSq ((X *ᵥ (v ∘ e)) j))
  have hs2 : ∑ i : Z, Complex.normSq (v i) = ∑ j : Y, Complex.normSq ((v ∘ e) j) :=
    (Equiv.sum_comp e (fun i => Complex.normSq (v i))).symm
  rw [hv, hs1, hs2]
  exact h1

/-- The L2 operator norm is invariant under reindexing along an equivalence. -/
theorem norm_submatrix_equiv {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z]
    [DecidableEq Z] (X : Matrix Y Y ℂ) (e : Y ≃ Z) :
    ‖X.submatrix e.symm e.symm‖ = ‖X‖ := by
  refine le_antisymm (norm_submatrix_equiv_le X e) ?_
  have h := norm_submatrix_equiv_le (X.submatrix e.symm e.symm) e.symm
  rw [Matrix.submatrix_submatrix, Equiv.symm_symm, Equiv.symm_comp_self,
    Matrix.submatrix_id_id] at h
  exact h

/-- The unitaries of a microstate, reindexed to `Fin d`. -/
def subU {P : PresentationCode} (M : Microstate P) {d : ℕ} (e : M.model ≃ Fin d) :
    Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ :=
  fun g => (M.gen g : Matrix M.model M.model ℂ).submatrix e.symm e.symm

theorem subU_mem_unitaryGroup {P : PresentationCode} (M : Microstate P) {d : ℕ}
    (e : M.model ≃ Fin d) (g : Fin (genCount P)) :
    subU M e g ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  show (M.gen g : Matrix M.model M.model ℂ).submatrix e.symm e.symm
    ∈ Matrix.unitaryGroup (Fin d) ℂ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff.1 (M.gen g).2, Matrix.submatrix_one_equiv]

theorem encWordMat_subU {P : PresentationCode} (M : Microstate P) {d : ℕ}
    (e : M.model ≃ Fin d) :
    ∀ w : List (ℕ × Bool), encWordMat P (subU M e) w =
      (Manuscript.MFRecognition.Certificates.wordEval M w).submatrix e.symm e.symm
  | [] => by
      show (1 : Matrix (Fin d) (Fin d) ℂ) = (1 : Matrix M.model M.model ℂ).submatrix e.symm e.symm
      exact (Matrix.submatrix_one_equiv e.symm).symm
  | (i, true) :: rest => by
      show (M.gen (letterOf P i) : Matrix M.model M.model ℂ).submatrix e.symm e.symm *
          encWordMat P (subU M e) rest
        = ((M.gen (letterOf P i) : Matrix M.model M.model ℂ) *
          Manuscript.MFRecognition.Certificates.wordEval M rest).submatrix e.symm e.symm
      rw [encWordMat_subU M e rest, Matrix.submatrix_mul_equiv]
  | (i, false) :: rest => by
      show ((M.gen (letterOf P i) : Matrix M.model M.model ℂ).submatrix e.symm e.symm)ᴴ *
          encWordMat P (subU M e) rest
        = ((M.gen (letterOf P i) : Matrix M.model M.model ℂ)ᴴ *
          Manuscript.MFRecognition.Certificates.wordEval M rest).submatrix e.symm e.symm
      rw [encWordMat_subU M e rest, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

theorem norm_encWordMat_subU {P : PresentationCode} (M : Microstate P) {d : ℕ}
    (e : M.model ≃ Fin d) (w : List (ℕ × Bool)) :
    ‖encWordMat P (subU M e) w - 1‖ = M.len w := by
  have hsub : (Manuscript.MFRecognition.Certificates.wordEval M w - 1).submatrix e.symm e.symm
      = (Manuscript.MFRecognition.Certificates.wordEval M w).submatrix e.symm e.symm -
        (1 : Matrix M.model M.model ℂ).submatrix e.symm e.symm := rfl
  rw [encWordMat_subU M e w, ← Matrix.submatrix_one_equiv e.symm, ← hsub, norm_submatrix_equiv,
    Manuscript.MFRecognition.Certificates.norm_wordEval_sub_one]

/-- The microstate on `Fin d` given by a tuple of unitaries. -/
def matMicrostate (P : PresentationCode) (d : ℕ) (h1 : 1 ≤ d)
    (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ) : Microstate P where
  model := ⟨Fin d, inferInstance, inferInstance⟩
  card_pos := by
    show 0 < Fintype.card (Fin d)
    rw [Fintype.card_fin]
    exact h1
  gen g := ⟨U g, hU g⟩

theorem wordEval_matMicrostate (P : PresentationCode) (d : ℕ) (h1 : 1 ≤ d)
    (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ w : List (ℕ × Bool),
      Manuscript.MFRecognition.Certificates.wordEval (matMicrostate P d h1 U hU) w =
        encWordMat P U w
  | [] => rfl
  | (i, true) :: rest => by
      rw [Manuscript.MFRecognition.Certificates.wordEval, wordEval_matMicrostate P d h1 U hU rest]
      rfl
  | (i, false) :: rest => by
      rw [Manuscript.MFRecognition.Certificates.wordEval, wordEval_matMicrostate P d h1 U hU rest]
      rfl

theorem len_matMicrostate (P : PresentationCode) (d : ℕ) (h1 : 1 ≤ d)
    (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ) (w : List (ℕ × Bool)) :
    (matMicrostate P d h1 U hU).len w = ‖encWordMat P U w - 1‖ := by
  rw [← Manuscript.MFRecognition.Certificates.norm_wordEval_sub_one]
  exact congrArg (fun X => ‖X - 1‖) (wordEval_matMicrostate P d h1 U hU w)

/-- `prop:mf-upper-bound`: `PhiSpec P n c` is the matrix condition over `Fin (certDim c)`. -/
theorem phiSpec_iff_matCond (P : PresentationCode) (n : ℕ)
    (c : Manuscript.MFRecognition.Certificates.PrintedCertificate) :
    Manuscript.MFRecognition.Certificates.PhiSpec P n c ↔
      MatCond P n (Manuscript.MFRecognition.Certificates.certDim c)
        (Manuscript.MFRecognition.Certificates.sWords P n c) := by
  constructor
  · rintro ⟨M, hcard, hr, hw⟩
    have h1 : 1 ≤ Manuscript.MFRecognition.Certificates.certDim c := by
      rw [← hcard]
      exact M.card_pos
    let e : M.model ≃ Fin (Manuscript.MFRecognition.Certificates.certDim c) :=
      Fintype.equivFinOfCardEq hcard
    refine ⟨h1, subU M e, subU_mem_unitaryGroup M e, fun r hr' => ?_, fun w hw' => ?_⟩
    · rw [norm_encWordMat_subU M e r]
      exact hr r hr'
    · rw [norm_encWordMat_subU M e w]
      exact hw w hw'
  · rintro ⟨h1, U, hU, hr, hw⟩
    refine ⟨matMicrostate P _ h1 U hU, ?_, fun r hr' => ?_, fun w hw' => ?_⟩
    · show Fintype.card (Fin (Manuscript.MFRecognition.Certificates.certDim c)) = _
      exact Fintype.card_fin _
    · rw [len_matMicrostate]
      exact hr r hr'
    · rw [len_matMicrostate]
      exact hw w hw'

end

end GroupApproximation.Full.NN11b
