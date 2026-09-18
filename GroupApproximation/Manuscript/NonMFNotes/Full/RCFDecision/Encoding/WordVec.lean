import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.CPoly
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.Vars
import GroupApproximation.Computability.PresentationCodes
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Words acting on vectors, symbolically

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`
("`Φ(P,n,c)` is a first-order sentence over the reals"), feeding
`thm:mf-arithmetic`.  The entries of the unitaries `U_g` are the variables of tag
`0` (`encGEntry`).  A word `w` acts on a vector of complex polynomials letter by
letter (`encWordVec`), with `x_j^{-1} ↦ U_j^*`; evaluating the result at an
assignment is applying the evaluated word matrix `encWordMat` to the evaluated
vector (`encEvalVec_wordVec`).
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.PresentationCodes Matrix

open scoped Matrix

/-- Reading back an entry of a mapped range. -/
theorem encGetD_map_range {α : Type} (F : ℕ → α) (x : α) {d r : ℕ} (h : r < d) :
    ((List.range d).map F).getD r x = F r := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h,
    Option.map_some, Option.getD_some]

/-- The entry `(r, s)` of the `g`-th unitary, as a complex polynomial. -/
def encGEntry (g r s : ℕ) : MvP × MvP := (mvVar (encIdx 0 g r s 0), mvVar (encIdx 0 g r s 1))

/-- The entry `(r, s)` of the matrix of the letter `a`: `U_g` or `U_g^*`. -/
def encLetterEntry (P : PresentationCode) (a : ℕ × Bool) (r s : ℕ) : MvP × MvP :=
  bif a.2 then encGEntry (a.1 % genCount P) r s else cpConj (encGEntry (a.1 % genCount P) s r)

/-- The letter `a` applied to a vector of complex polynomials of dimension `d`. -/
def encApplyLetter (P : PresentationCode) (d : ℕ) (a : ℕ × Bool) (v : List (MvP × MvP)) :
    List (MvP × MvP) :=
  (List.range d).map fun x =>
    cpSumRange d fun s => cpMul (encLetterEntry P a x s) (v.getD s cpZero)

/-- The word `w` applied to a vector of complex polynomials of dimension `d`. -/
def encWordVec (P : PresentationCode) (d : ℕ) (w : List (ℕ × Bool)) (v : List (MvP × MvP)) :
    List (MvP × MvP) :=
  w.foldr (encApplyLetter P d) v

/-- The vector whose coordinate `r` is the variable pair `encIdx tag t r 0 _`. -/
def encVecOf (tag t d : ℕ) : List (MvP × MvP) :=
  (List.range d).map fun r => (mvVar (encIdx tag t r 0 0), mvVar (encIdx tag t r 0 1))

noncomputable section

/-- The evaluation of a vector of complex polynomials. -/
def encEvalVec (ρ : ℕ → ℝ) (d : ℕ) (l : List (MvP × MvP)) : Fin d → ℂ :=
  fun r => cpEval ρ (l.getD r cpZero)

/-- The evaluated unitaries. -/
def encUmat (P : PresentationCode) (ρ : ℕ → ℝ) (d : ℕ) (g : Fin (genCount P)) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun r s => cpEval ρ (encGEntry (g : ℕ) r s)

/-- The matrix of a letter: `U_j` for `x_j`, `U_j^*` for `x_j^{-1}`. -/
def encLetterMat (P : PresentationCode) {d : ℕ} (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ)
    (a : ℕ × Bool) : Matrix (Fin d) (Fin d) ℂ :=
  bif a.2 then U (letterOf P a.1) else (U (letterOf P a.1))ᴴ

/-- The matrix of a word. -/
def encWordMat (P : PresentationCode) {d : ℕ} (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ) :
    List (ℕ × Bool) → Matrix (Fin d) (Fin d) ℂ
  | [] => 1
  | a :: w => encLetterMat P U a * encWordMat P U w

theorem encEvalVec_vecOf (ρ : ℕ → ℝ) (tag t d : ℕ) (r : Fin d) :
    encEvalVec ρ d (encVecOf tag t d) r = ⟨ρ (encIdx tag t r 0 0), ρ (encIdx tag t r 0 1)⟩ := by
  show cpEval ρ (((List.range d).map fun x =>
      (mvVar (encIdx tag t x 0 0), mvVar (encIdx tag t x 0 1))).getD r cpZero) = _
  rw [encGetD_map_range _ _ r.isLt]
  exact Complex.ext (mvEval_var ρ _) (mvEval_var ρ _)

theorem cpEval_letterEntry (P : PresentationCode) (ρ : ℕ → ℝ) (d : ℕ) (a : ℕ × Bool)
    (r s : Fin d) :
    cpEval ρ (encLetterEntry P a r s) = encLetterMat P (encUmat P ρ d) a r s := by
  obtain ⟨i, b⟩ := a
  cases b
  · exact (cpEval_conj ρ (encGEntry (i % genCount P) s r)).trans
      (Matrix.conjTranspose_apply (encUmat P ρ d (letterOf P i)) r s).symm
  · rfl

theorem encEvalVec_applyLetter (P : PresentationCode) (ρ : ℕ → ℝ) (d : ℕ) (a : ℕ × Bool)
    (v : List (MvP × MvP)) :
    encEvalVec ρ d (encApplyLetter P d a v) =
      encLetterMat P (encUmat P ρ d) a *ᵥ encEvalVec ρ d v := by
  funext r
  show cpEval ρ (((List.range d).map fun x =>
      cpSumRange d fun s => cpMul (encLetterEntry P a x s) (v.getD s cpZero)).getD r cpZero)
    = ∑ s : Fin d, encLetterMat P (encUmat P ρ d) a r s * encEvalVec ρ d v s
  rw [encGetD_map_range _ _ r.isLt, cpEval_sumRange]
  refine Finset.sum_congr rfl fun s _ => ?_
  show cpEval ρ (cpMul (encLetterEntry P a r s) (v.getD s cpZero))
    = encLetterMat P (encUmat P ρ d) a r s * cpEval ρ (v.getD s cpZero)
  rw [cpEval_mul, cpEval_letterEntry]

theorem encEvalVec_wordVec (P : PresentationCode) (ρ : ℕ → ℝ) (d : ℕ) (v : List (MvP × MvP)) :
    ∀ w : List (ℕ × Bool),
      encEvalVec ρ d (encWordVec P d w v) = encWordMat P (encUmat P ρ d) w *ᵥ encEvalVec ρ d v
  | [] => (Matrix.one_mulVec (encEvalVec ρ d v)).symm
  | a :: w => by
      show encEvalVec ρ d (encApplyLetter P d a (encWordVec P d w v))
        = (encLetterMat P (encUmat P ρ d) a * encWordMat P (encUmat P ρ d) w) *ᵥ encEvalVec ρ d v
      rw [encEvalVec_applyLetter, encEvalVec_wordVec P ρ d v w, Matrix.mulVec_mulVec]

end

end GroupApproximation.Full.NN11b
