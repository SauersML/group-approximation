import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.Decode
import Mathlib.Tactic.Choose

/-!
# Correctness of the encoding `encodePrenex`

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`
("`Φ(P,n,c)` is a first-order sentence over the reals"), feeding `thm:mf-arithmetic`.
The prenex sentence `encodePrenex ((P, n), c)` holds over `ℝ` iff `PhiSpec P n c`
(`encodePrenex_spec`).  The existential block carries the unitaries `U_g` and the
unit vectors witnessing `‖S_t(U) - 1‖ ≥ 1/4`
(`le_l2_opNorm_iff_exists_unit_vector`); the universal block carries the test vectors
of the quadratic forms expressing `‖R_t(U) - 1‖ ≤ 2^{-n}`
(`l2_opNorm_le_iff_quadraticForm_nonneg`).
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.PresentationCodes Matrix

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

/-- The coordinates of a single vector, padded by `0`, at every tag and index. -/
def encFamT (d : ℕ) (v : Fin d → ℂ) (_tag _a b _c : ℕ) : ℂ :=
  if hb : b < d then v ⟨b, hb⟩ else 0

theorem encFamT_apply (d : ℕ) (v : Fin d → ℂ) (tag t : ℕ) (r : Fin d) :
    encFamT d v tag t r 0 = v r :=
  dif_pos r.isLt

/-- The existential data: entries of the unitaries at tag `0`, coordinates of the unit
vectors at every other tag. -/
def encFamEx (P : PresentationCode) (d : ℕ) (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ)
    (m : ℕ) (V : Fin m → Fin d → ℂ) (tag a b c : ℕ) : ℂ :=
  if tag = 0 then encFam0 P d U a b c else encFamV d m V a b

theorem encFamEx_zero (P : PresentationCode) (d : ℕ)
    (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ) (m : ℕ) (V : Fin m → Fin d → ℂ)
    (a b c : ℕ) : encFamEx P d U m V 0 a b c = encFam0 P d U a b c := by
  rw [encFamEx, if_pos rfl]

theorem encFamEx_one (P : PresentationCode) (d : ℕ)
    (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ) (m : ℕ) (V : Fin m → Fin d → ℂ)
    (a b c : ℕ) : encFamEx P d U m V 1 a b c = encFamV d m V a b := by
  rw [encFamEx, if_neg Nat.one_ne_zero]

/-- A quadratic form that is nonnegative at every assignment of the universal block
gives the upper bound on the operator norm. -/
theorem encUpper_norm_le (P : PresentationCode) (n d : ℕ)
    (U : Fin (genCount P) → Matrix (Fin d) (Fin d) ℂ) (w : List (ℕ × Bool)) (t : ℕ)
    (h : ∀ τ : ℕ → ℝ,
      0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * ∑ r : Fin d, Complex.normSq (encEvalVec τ d (encVecOf 2 t d) r)
        - ∑ r : Fin d, Complex.normSq (((encWordMat P U w - 1) *ᵥ
          encEvalVec τ d (encVecOf 2 t d)) r)) :
    ‖encWordMat P U w - 1‖ ≤ (1 / 2 : ℝ) ^ n := by
  refine (Manuscript.MFRecognition.Certificates.l2_opNorm_le_iff_quadraticForm_nonneg _
    (pow_nonneg (by norm_num) n)).2 fun v => ?_
  have hv := h (encDecode (encFamT d v))
  rw [encEvalVec_decode (encFamT d v) 2 t d v (encFamT_apply d v 2 t)] at hv
  exact hv

/-- `prop:mf-upper-bound`: the `∃ ∀` closure of the matrix of `encFormula P n d S` is
the matrix condition `MatCond P n d S`. -/
theorem exAll_encCond_iff_matCond (P : PresentationCode) (n d : ℕ)
    (S : List (List (ℕ × Bool))) :
    (∃ σ : ℕ → ℝ, ∀ τ : ℕ → ℝ, EncCond P n d S
      (encOverride (encAllVars P d) τ (encOverride (encExVars P d S) σ (fun _ => 0)))) ↔
      MatCond P n d S := by
  constructor
  · rintro ⟨σ, h⟩
    have hC := fun τ => (encCond_override P n d S σ τ (fun _ => 0)).1 (h τ)
    have h0 := hC (fun _ => 0)
    have h1 : 1 ≤ d := h0.2.1.1
    have hne : Nonempty (Fin d) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one h1⟩⟩
    refine ⟨h1, encUmat P σ d, h0.1.1, fun r hr => ?_, fun w hw => ?_⟩
    · obtain ⟨i, hi, hr'⟩ := List.mem_iff_getElem.1 hr
      rw [← hr', ← encGetD_eq P.2 [] hi]
      exact encUpper_norm_le P n d (encUmat P σ d) (P.2.getD i []) i
        fun τ => (hC τ).2.2 ⟨i, hi⟩
    · obtain ⟨i, hi, hw'⟩ := List.mem_iff_getElem.1 hw
      rw [← hw', ← encGetD_eq S [] hi]
      exact (Manuscript.MFRecognition.Certificates.le_l2_opNorm_iff_exists_unit_vector hne _
        (by norm_num)).2 ⟨encEvalVec σ d (encVecOf 1 i d), h0.1.2 ⟨i, hi⟩, h0.2.1.2 ⟨i, hi⟩⟩
  · rintro ⟨h1, U, hU, hr, hw⟩
    have hne : Nonempty (Fin d) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one h1⟩⟩
    have hv : ∀ t : Fin S.length, ∃ v : Fin d → ℂ, (∑ r : Fin d, Complex.normSq (v r)) = 1 ∧
        (1 / 4 : ℝ) ^ 2 ≤ ∑ r : Fin d, Complex.normSq
          (((encWordMat P U (S.getD t []) - 1) *ᵥ v) r) := fun t =>
      (Manuscript.MFRecognition.Certificates.le_l2_opNorm_iff_exists_unit_vector hne _
        (by norm_num)).1 (hw _ (encGetD_mem S t []))
    choose V hV1 hV2 using hv
    have hGU : encUmat P (encDecode (encFamEx P d U S.length V)) d = U :=
      encUmat_decode P d (encFamEx P d U S.length V) U fun g r s =>
        (encFamEx_zero P d U S.length V g r s).trans (encFam0_apply P d U g r s)
    have hGV : ∀ t : Fin S.length,
        encEvalVec (encDecode (encFamEx P d U S.length V)) d (encVecOf 1 t d) = V t := fun t =>
      encEvalVec_decode (encFamEx P d U S.length V) 1 t d (V t) fun r =>
        (encFamEx_one P d U S.length V t r 0).trans (encFamV_apply d S.length V t r)
    refine ⟨encDecode (encFamEx P d U S.length V), fun τ =>
      (encCond_override P n d S (encDecode (encFamEx P d U S.length V)) τ (fun _ => 0)).2 ?_⟩
    rw [hGU]
    refine ⟨⟨hU, fun t => ?_⟩, ⟨h1, fun t => ?_⟩, fun t => ?_⟩
    · rw [hGV t]
      exact hV1 t
    · rw [hGV t]
      exact hV2 t
    · exact (Manuscript.MFRecognition.Certificates.l2_opNorm_le_iff_quadraticForm_nonneg _
        (pow_nonneg (by norm_num) n)).1 (hr _ (encGetD_mem P.2 t []))
        (encEvalVec τ d (encVecOf 2 t d))

/-- The prenex sentence `encFormula P n d S` holds over the reals iff `MatCond P n d S`. -/
theorem pHolds_encFormula_iff (P : PresentationCode) (n d : ℕ) (S : List (List (ℕ × Bool))) :
    PHolds (encFormula P n d S).1 (encFormula P n d S).2 (fun _ => 0) ↔ MatCond P n d S := by
  have h1 := pHolds_encExAll (encExVars P d S) (encAllVars P d) (encFormula P n d S).2
    (fun _ => 0)
  have h2 : (∃ σ : ℕ → ℝ, ∀ τ : ℕ → ℝ, qfHolds
        (encOverride (encAllVars P d) τ (encOverride (encExVars P d S) σ (fun _ => 0)))
        (encFormula P n d S).2) ↔
      ∃ σ : ℕ → ℝ, ∀ τ : ℕ → ℝ, EncCond P n d S
        (encOverride (encAllVars P d) τ (encOverride (encExVars P d S) σ (fun _ => 0))) :=
    exists_congr fun σ => forall_congr' fun τ => qfHolds_encFormula P n d S
      (encOverride (encAllVars P d) τ (encOverride (encExVars P d S) σ (fun _ => 0)))
  exact h1.trans (h2.trans (exAll_encCond_iff_matCond P n d S))

/-- `prop:mf-upper-bound`, printed sentence `9eae4d68673a`: the prenex sentence
`encodePrenex ((P, n), c)` holds over the reals iff `Φ(P, n, c)`, i.e. `PhiSpec P n c`. -/
theorem encodePrenex_spec (P : PresentationCode) (n : ℕ)
    (c : Manuscript.MFRecognition.Certificates.PrintedCertificate) :
    PHolds (encodePrenex ((P, n), c)).1 (encodePrenex ((P, n), c)).2 (fun _ => 0) ↔
      Manuscript.MFRecognition.Certificates.PhiSpec P n c :=
  (pHolds_encFormula_iff P n (Manuscript.MFRecognition.Certificates.certDim c)
    (Manuscript.MFRecognition.Certificates.sWords P n c)).trans (phiSpec_iff_matCond P n c).symm

end

end GroupApproximation.Full.NN11b
