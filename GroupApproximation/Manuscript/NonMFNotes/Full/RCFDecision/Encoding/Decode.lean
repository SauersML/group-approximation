import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.FinModel

/-!
# Reading unitaries and vectors off an assignment

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`:
"the variables are the real and imaginary parts of the entries".  Under the
assignment produced by the quantifier prefix of `encFormula`, the evaluated
unitaries and unit vectors only see the existential block and the test vectors
only see the universal block (`encCond_override`).  Conversely, any tuple of
matrices and vectors is the evaluation of an assignment (`encUmat_decode`,
`encEvalVec_decode`).
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.PresentationCodes Matrix

open scoped Matrix

noncomputable section

theorem encGetD_eq {α : Type} (l : List α) (x : α) {i : ℕ} (h : i < l.length) :
    l.getD i x = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem encGetD_mem {α : Type} (l : List α) (t : Fin l.length) (x : α) : l.getD t x ∈ l := by
  rw [encGetD_eq l x t.isLt]
  exact List.getElem_mem t.isLt

theorem encUmat_apply (P : PresentationCode) (ρ : ℕ → ℝ) (d : ℕ) (g : Fin (genCount P))
    (r s : Fin d) :
    encUmat P ρ d g r s = ⟨ρ (encIdx 0 g r s 0), ρ (encIdx 0 g r s 1)⟩ := by
  show cpEval ρ (encGEntry g r s) = _
  exact Complex.ext (mvEval_var ρ (encIdx 0 g r s 0)) (mvEval_var ρ (encIdx 0 g r s 1))

theorem encUmat_congr (P : PresentationCode) {ρ ρ' : ℕ → ℝ} (d : ℕ)
    (h : ∀ g < genCount P, ∀ r < d, ∀ s < d, ∀ p < 2, ρ (encIdx 0 g r s p) = ρ' (encIdx 0 g r s p)) :
    encUmat P ρ d = encUmat P ρ' d :=
  funext fun g => Matrix.ext fun r s => by
    rw [encUmat_apply, encUmat_apply]
    exact congrArg₂ Complex.mk (h g g.isLt r r.isLt s s.isLt 0 Nat.zero_lt_two)
      (h g g.isLt r r.isLt s s.isLt 1 Nat.one_lt_two)

theorem encEvalVec_congr {ρ ρ' : ℕ → ℝ} (tag t d : ℕ)
    (h : ∀ r < d, ∀ p < 2, ρ (encIdx tag t r 0 p) = ρ' (encIdx tag t r 0 p)) :
    encEvalVec ρ d (encVecOf tag t d) = encEvalVec ρ' d (encVecOf tag t d) :=
  funext fun r => by
    rw [encEvalVec_vecOf, encEvalVec_vecOf]
    exact congrArg₂ Complex.mk (h r r.isLt 0 Nat.zero_lt_two) (h r r.isLt 1 Nat.one_lt_two)

theorem encUmat_override (P : PresentationCode) (d : ℕ) (S : List (List (ℕ × Bool)))
    (σ τ ρ : ℕ → ℝ) :
    encUmat P (encOverride (encAllVars P d) τ (encOverride (encExVars P d S) σ ρ)) d =
      encUmat P σ d :=
  encUmat_congr P d fun _ hg _ hr _ hs _ hp =>
    (encOverride_of_not_mem τ (encOverride (encExVars P d S) σ ρ)
      (encIdx_not_mem_encBlock (tag := 0) (tag' := 2) (by decide))).trans
      (encOverride_of_mem σ ρ (List.mem_append_left _ (encIdx_mem_encBlock hg hr hs hp)))

theorem encVec1_override (P : PresentationCode) (d : ℕ) (S : List (List (ℕ × Bool)))
    (σ τ ρ : ℕ → ℝ) (t : Fin S.length) :
    encEvalVec (encOverride (encAllVars P d) τ (encOverride (encExVars P d S) σ ρ)) d
      (encVecOf 1 t d) = encEvalVec σ d (encVecOf 1 t d) :=
  encEvalVec_congr 1 t d fun _ hr _ hp =>
    (encOverride_of_not_mem τ (encOverride (encExVars P d S) σ ρ)
      (encIdx_not_mem_encBlock (tag := 1) (tag' := 2) (by decide))).trans
      (encOverride_of_mem σ ρ
        (List.mem_append_right _ (encIdx_mem_encBlock t.isLt hr Nat.zero_lt_one hp)))

theorem encVec2_override (P : PresentationCode) (d : ℕ) (S : List (List (ℕ × Bool)))
    (σ τ ρ : ℕ → ℝ) (t : Fin P.2.length) :
    encEvalVec (encOverride (encAllVars P d) τ (encOverride (encExVars P d S) σ ρ)) d
      (encVecOf 2 t d) = encEvalVec τ d (encVecOf 2 t d) :=
  encEvalVec_congr 2 t d fun _ hr _ hp =>
    encOverride_of_mem τ _ (encIdx_mem_encBlock t.isLt hr Nat.zero_lt_one hp)

/-- The matrix of the sentence at the assignment given by the prefix: the unitaries
and unit vectors come from `σ`, the test vectors from `τ`. -/
theorem encCond_override (P : PresentationCode) (n d : ℕ) (S : List (List (ℕ × Bool)))
    (σ τ ρ : ℕ → ℝ) :
    EncCond P n d S (encOverride (encAllVars P d) τ (encOverride (encExVars P d S) σ ρ)) ↔
      ((∀ g : Fin (genCount P), encUmat P σ d g ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
        ∀ t : Fin S.length, ∑ r : Fin d, Complex.normSq (encEvalVec σ d (encVecOf 1 t d) r) = 1) ∧
      ((1 ≤ d ∧
        ∀ t : Fin S.length, (1 / 4 : ℝ) ^ 2 ≤ ∑ r : Fin d, Complex.normSq
          (((encWordMat P (encUmat P σ d) (S.getD t []) - 1) *ᵥ
            encEvalVec σ d (encVecOf 1 t d)) r)) ∧
        ∀ t : Fin P.2.length,
          0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * ∑ r : Fin d, Complex.normSq (encEvalVec τ d (encVecOf 2 t d) r)
            - ∑ r : Fin d, Complex.normSq (((encWordMat P (encUmat P σ d) (P.2.getD t []) - 1) *ᵥ
              encEvalVec τ d (encVecOf 2 t d)) r)) := by
  simp only [EncCond, encUmat_override, encVec1_override, encVec2_override]

/-- The entries of a matrix tuple, padded by `0`. -/
def encFam0 (P : PresentationCode) (d : ℕ) (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ)
    (a b c : ℕ) : ℂ :=
  if ha : a < genCount P then if hb : b < d then if hc : c < d then
    U ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ else 0 else 0 else 0

theorem encFam0_apply (P : PresentationCode) (d : ℕ)
    (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ) (g : Fin (genCount P)) (r s : Fin d) :
    encFam0 P d U g r s = U g r s := by
  show (if ha : (g : ℕ) < genCount P then if hb : (r : ℕ) < d then if hc : (s : ℕ) < d then
    U ⟨g, ha⟩ ⟨r, hb⟩ ⟨s, hc⟩ else 0 else 0 else 0) = U g r s
  rw [dif_pos g.isLt, dif_pos r.isLt, dif_pos s.isLt]

/-- The coordinates of a vector tuple, padded by `0`. -/
def encFamV (d m : ℕ) (V : Fin m → Fin d → ℂ) (a b : ℕ) : ℂ :=
  if ha : a < m then if hb : b < d then V ⟨a, ha⟩ ⟨b, hb⟩ else 0 else 0

theorem encFamV_apply (d m : ℕ) (V : Fin m → Fin d → ℂ) (t : Fin m) (r : Fin d) :
    encFamV d m V t r = V t r := by
  show (if ha : (t : ℕ) < m then if hb : (r : ℕ) < d then V ⟨t, ha⟩ ⟨r, hb⟩ else 0 else 0)
    = V t r
  rw [dif_pos t.isLt, dif_pos r.isLt]

theorem encUmat_decode (P : PresentationCode) (d : ℕ) (G : ℕ → ℕ → ℕ → ℕ → ℂ)
    (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ)
    (hG : ∀ (g : Fin (genCount P)) (r s : Fin d), G 0 g r s = U g r s) :
    encUmat P (encDecode G) d = U :=
  funext fun g => Matrix.ext fun r s =>
    (encUmat_apply P (encDecode G) d g r s).trans (Complex.ext
      ((encDecode_encIdx G 0 g r s 0).trans ((encPart_zero _).trans (congrArg Complex.re (hG g r s))))
      ((encDecode_encIdx G 0 g r s 1).trans ((encPart_one _).trans (congrArg Complex.im (hG g r s)))))

theorem encEvalVec_decode (G : ℕ → ℕ → ℕ → ℕ → ℂ) (tag t d : ℕ) (v : Fin d → ℂ)
    (hG : ∀ r : Fin d, G tag t r 0 = v r) :
    encEvalVec (encDecode G) d (encVecOf tag t d) = v :=
  funext fun r =>
    (encEvalVec_vecOf (encDecode G) tag t d r).trans (Complex.ext
      ((encDecode_encIdx G tag t r 0 0).trans ((encPart_zero _).trans (congrArg Complex.re (hG r))))
      ((encDecode_encIdx G tag t r 0 1).trans ((encPart_one _).trans (congrArg Complex.im (hG r)))))

end

end GroupApproximation.Full.NN11b
