import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.Encoding
import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralCertificate.Predicate
import GroupApproximation.Sofic.KazhdanCornerModel
import GroupApproximation.Manuscript.MFRecognition.PrintedTarskiCertificateSyntax

/-!
# Solutions of the polynomial system witness the literal predicate (lane NN02c)

Manuscript: `thm:mf-radical-arithmetic` (non_mf_group_notes.tex), sentence
"This is decidable over the real closed field" (Tarski 1951, Seidenberg 1954).

A solution `ζ` of the matrix conditions `Solution ζ z` attached to `z = ((c, v), n, d)`
gives generator unitaries `U i = blk ζ d 0 i` witnessing `NN02b.LiteralD c v n d`:

* the word blocks `(1, encode u)` are the values `u(U)` (`blk_one_eq_literalWordValue`);
* `M = 2^(n+10) (W_r - 1)` with `1 = Mᴴ M + Bᴴ B` gives `‖W_r - 1‖ ≤ 2^(-n-10)`
  (`norm_le_one_of_gram`, `norm_sub_one_le_of_scaled`);
* a unit vector `x` with `4 ‖(W_v - 1) x‖² ≥ 1` gives `‖W_v - 1‖ ≥ 1/2` (`half_le_norm`).
-/

namespace GroupApproximation.Full.NN02c

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ### Norm estimates -/

theorem star_dotProduct_self_eq {d : ℕ} (x : Fin d → ℂ) :
    star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact Complex.normSq_eq_conj_mul_self.symm

theorem star_dotProduct_gram {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((Aᴴ * A) *ᵥ x) = ((∑ i, Complex.normSq ((A *ᵥ x) i) : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star,
    star_dotProduct_self_eq]

/-- `1 = Mᴴ M + Bᴴ B` forces `‖M‖ ≤ 1`. -/
theorem norm_le_one_of_gram {d : ℕ} (M B : Matrix (Fin d) (Fin d) ℂ)
    (h : 1 = Mᴴ * M + Bᴴ * B) : ‖M‖ ≤ 1 := by
  refine GroupApproximation.KazhdanCornerMatrices.l2_opNorm_le_of_sum_normSq_general M
    zero_le_one fun x => ?_
  have hc : ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) =
      ((∑ i, Complex.normSq ((M *ᵥ x) i) + ∑ i, Complex.normSq ((B *ᵥ x) i) : ℝ) : ℂ) := by
    rw [← star_dotProduct_self_eq x, Complex.ofReal_add, ← star_dotProduct_gram M x,
      ← star_dotProduct_gram B x, ← dotProduct_add, ← Matrix.add_mulVec, ← h, Matrix.one_mulVec]
  have hr := Complex.ofReal_injective hc
  have hB : 0 ≤ ∑ i, Complex.normSq ((B *ᵥ x) i) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  rw [one_pow, one_mul]
  linarith

/-- `M = 2^(n+10) (W - 1)` and `1 = Mᴴ M + Bᴴ B` give `‖W - 1‖ ≤ 2^(-n-10)`. -/
theorem norm_sub_one_le_of_scaled {d : ℕ} (n : ℕ) (W M B : Matrix (Fin d) (Fin d) ℂ)
    (hM : M = ((scale n : ℕ) : ℂ) • (W - 1)) (hG : 1 = Mᴴ * M + Bᴴ * B) :
    ‖W - 1‖ ≤ NN02b.literalDefectBound n := by
  have hS : ((scale n : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by rw [scale_eq]; exact pow_ne_zero _ two_ne_zero)
  have hW : W - 1 = ((scale n : ℕ) : ℂ)⁻¹ • M := by
    rw [hM, smul_smul, inv_mul_cancel₀ hS, one_smul]
  have hnorm := norm_le_one_of_gram M B hG
  calc ‖W - 1‖ = ‖((scale n : ℕ) : ℂ)⁻¹ • M‖ := by rw [hW]
    _ ≤ ‖((scale n : ℕ) : ℂ)⁻¹‖ * ‖M‖ := norm_smul_le _ _
    _ ≤ ‖((scale n : ℕ) : ℂ)⁻¹‖ * 1 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = NN02b.literalDefectBound n := by
      rw [mul_one, norm_inv, Complex.norm_natCast, scale_eq, NN02b.literalDefectBound_eq]
      norm_num

/-- A unit vector `x` with `0 ≤ re (4 ⟪X x, X x⟫ - 1)` gives `1/2 ≤ ‖X‖`. -/
theorem half_le_norm {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d → ℂ)
    (hx : star x ⬝ᵥ x = 1) (hy : y = X *ᵥ x)
    (hnn : 0 ≤ (((4 : ℕ) : ℂ) * (star y ⬝ᵥ y) - 1).re) : 1 / 2 ≤ ‖X‖ := by
  have hne : Nonempty (Fin d) := by
    rcases d with _ | _
    · exfalso
      rw [dotProduct, Finset.univ_eq_empty, Finset.sum_empty] at hx
      exact zero_ne_one hx
    · exact ⟨0⟩
  refine (GroupApproximation.Manuscript.MFRecognition.Certificates.le_l2_opNorm_iff_exists_unit_vector
    hne X (by norm_num)).mpr ⟨x, ?_, ?_⟩
  · rw [star_dotProduct_self_eq] at hx
    exact Complex.ofReal_injective (hx.trans Complex.ofReal_one.symm)
  · rw [hy, star_dotProduct_self_eq, Complex.sub_re, Complex.one_re, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, Complex.ofReal_re] at hnn
    have h4 : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
    have h44 : ((4 : ℕ) : ℝ) = 4 := by norm_num
    rw [h44] at hnn
    rw [h4]
    linarith

/-! ### Word values -/

/-- Matrix form of one letter step of the word value. -/
theorem coe_literalWordValue_cons (c : PresentationCodes.PresentationCode) {d : ℕ}
    (U : Fin (PresentationCodes.genCount c) → Matrix.unitaryGroup (Fin d) ℂ)
    (a : ℕ × Bool) (u : List (ℕ × Bool)) :
    ((NN02b.literalWordValue c U (a :: u) : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) =
      (bif a.2 then (U (PresentationCodes.letterOf c a.1) : Matrix (Fin d) (Fin d) ℂ)
        else (U (PresentationCodes.letterOf c a.1) : Matrix (Fin d) (Fin d) ℂ)ᴴ) *
        ((NN02b.literalWordValue c U u : Matrix.unitaryGroup (Fin d) ℂ) :
          Matrix (Fin d) (Fin d) ℂ) := by
  rcases a with ⟨_, _ | _⟩ <;> rfl

theorem coe_literalWordValue_nil (c : PresentationCodes.PresentationCode) {d : ℕ}
    (U : Fin (PresentationCodes.genCount c) → Matrix.unitaryGroup (Fin d) ℂ) :
    ((NN02b.literalWordValue c U [] : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) = 1 := rfl

/-- Under `WordCond`, block `(1, encode u)` is the value `u(U)` of the word at the
generator blocks. -/
theorem blk_one_eq_literalWordValue (ζ : ℕ → ℂ) (c : PresentationCodes.PresentationCode)
    {d : ℕ} (U : Fin (PresentationCodes.genCount c) → Matrix.unitaryGroup (Fin d) ℂ)
    (hU : ∀ i : Fin (PresentationCodes.genCount c),
      (U i : Matrix (Fin d) (Fin d) ℂ) = blk ζ d 0 i)
    (u : List (ℕ × Bool)) (hw : WordCond ζ (c.1 + 1) d u) :
    blk ζ d 1 (Encodable.encode u) =
      ((NN02b.literalWordValue c U u : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) := by
  induction u with
  | nil =>
    have h : blk ζ d 1 (Encodable.encode ([] : List (ℕ × Bool))) = 1 := hw
    rw [h, coe_literalWordValue_nil]
  | cons a u ih =>
    have h : blk ζ d 1 (Encodable.encode (a :: u)) =
        letterMat ζ (c.1 + 1) d a * blk ζ d 1 (Encodable.encode u) ∧
          WordCond ζ (c.1 + 1) d u := hw
    have hl : letterMat ζ (c.1 + 1) d a =
        bif a.2 then (U (PresentationCodes.letterOf c a.1) : Matrix (Fin d) (Fin d) ℂ)
          else (U (PresentationCodes.letterOf c a.1) : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
      rw [hU]
      rfl
    rw [h.1, ih h.2, coe_literalWordValue_cons, hl]

/-! ### Solutions witness `LiteralD` -/

/-- **A solution of the system witnesses `D(P,v,n,d)`** (`thm:mf-radical-arithmetic`). -/
theorem literalD_of_solution (ζ : ℕ → ℂ)
    (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ) (h : Solution ζ z) :
    NN02b.LiteralD z.1.1 z.1.2 z.2.1 z.2.2 := by
  obtain ⟨⟨hU, hR, hV⟩, hnn⟩ := h
  let U : Fin (PresentationCodes.genCount z.1.1) → Matrix.unitaryGroup (Fin z.2.2) ℂ :=
    fun i => ⟨blk ζ z.2.2 0 i, Matrix.mem_unitaryGroup_iff'.mpr (hU (i : ℕ) i.2)⟩
  have hUb : ∀ i : Fin (PresentationCodes.genCount z.1.1),
      (U i : Matrix (Fin z.2.2) (Fin z.2.2) ℂ) = blk ζ z.2.2 0 i := fun _ => rfl
  refine ⟨U, fun r hr => ?_, ?_⟩
  · obtain ⟨hw, hM, hG⟩ := hR r hr
    rw [← blk_one_eq_literalWordValue ζ z.1.1 U hUb r hw]
    exact norm_sub_one_le_of_scaled z.2.1 _ _ _ hM hG
  · obtain ⟨hw, hx, hy⟩ := hV
    rw [← blk_one_eq_literalWordValue ζ z.1.1 U hUb z.1.2 hw]
    exact half_le_norm _ _ _ hx hy hnn

/-- Solvability of the complex system implies `D(P,v,n,d)`. -/
theorem literalD_of_holds_encodeC
    (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ)
    (h : CSystem.Holds (encodeC z)) : NN02b.LiteralD z.1.1 z.1.2 z.2.1 z.2.2 := by
  obtain ⟨ζ, hζ⟩ := (holds_encodeC_iff z).mp h
  exact literalD_of_solution ζ z hζ

end

end GroupApproximation.Full.NN02c
