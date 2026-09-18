import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.UHFBlockAmp
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.UHFInterface
import GroupApproximation.Analysis.OperatorNormCertificate

/-!
# The universal UHF algebra `Q`: the block average `M_{n!} → M_{m!}`

Lane `TWWSch3d5a` (work order `WO-TWWSchafhauser-3d-5`, part (a)).

For `m ≤ n`, `d = n!/m!` and the isometries `W_r` of `UHFBlockAmp.lean`, the
block average `x ↦ d⁻¹ ∑_r W_r⋆ x W_r` is the normalized partial trace
`M_{m!} ⊗ M_d → M_{m!}`.  It is a left inverse of the amplification
`a ↦ a ⊗ 1_d`, it is a bimodule map over the amplified copy of `M_{m!}`, it
carries the normalized trace of `M_{n!}` to that of `M_{m!}`, it does not
increase entries beyond the operator norm, and it is completely positive:
every form `∑ w̄_i Φ(c_i⋆ c_j) w_j` equals `d⁻¹ ∑_r ‖∑_i c_i W_r w_i‖²`.
These are the finite-level facts behind the conditional expectations
`Q → M_{m!}`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Two elementary identities about vectors -/

/-- A sesquilinear form written through `dotProduct`. -/
theorem uhf_form_eq_dotProduct {Y : Type*} [Fintype Y] (u : Y → ℂ) (M : Matrix Y Y ℂ)
    (v : Y → ℂ) :
    ∑ x, ∑ y, (starRingEnd ℂ) (u x) * M x y * v y = star u ⬝ᵥ (M *ᵥ v) := by
  show _ = ∑ x, star u x * ∑ y, M x y * v y
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [starRingEnd_apply, mul_assoc]

/-- `⟨u, P⋆Q v⟩ = ⟨P u, Q v⟩`. -/
theorem uhf_dotProduct_conjTranspose_mul {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]
    (P : Matrix κ α ℂ) (Q : Matrix κ β ℂ) (u : α → ℂ) (v : β → ℂ) :
    star u ⬝ᵥ ((Pᴴ * Q) *ᵥ v) = star (P *ᵥ u) ⬝ᵥ (Q *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec v Pᴴ Q, Matrix.dotProduct_mulVec (star u) Pᴴ (Q *ᵥ v),
    ← Matrix.star_mulVec P u]

/-- `⟨v, v⟩` is a nonnegative real number. -/
theorem uhf_star_dotProduct_self {α : Type*} [Fintype α] (v : α → ℂ) :
    (star v ⬝ᵥ v).im = 0 ∧ 0 ≤ (star v ⬝ᵥ v).re := by
  constructor
  · show (∑ i, star (v i) * v i).im = 0
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  · show 0 ≤ (∑ i, star (v i) * v i).re
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_self_nonneg (v i).re, mul_self_nonneg (v i).im]

variable {m n : ℕ} (h : m ≤ n)

theorem uhfBlockDim_cast_ne_zero : (uhfBlockDim m n : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (uhfBlockDim_pos h).ne'

/-! ## The block average -/

/-- **The block average** `x ↦ d⁻¹ ∑_r W_r⋆ x W_r`, the normalized partial trace
`M_{m!} ⊗ M_d → M_{m!}`. -/
def uhfAvg (x : Matrix (Fin n.factorial) (Fin n.factorial) ℂ) :
    Matrix (Fin m.factorial) (Fin m.factorial) ℂ :=
  (uhfBlockDim m n : ℂ)⁻¹ • ∑ r, (uhfBlockIso h r)ᴴ * x * uhfBlockIso h r

theorem uhfAvg_def (x : Matrix (Fin n.factorial) (Fin n.factorial) ℂ) :
    uhfAvg h x = (uhfBlockDim m n : ℂ)⁻¹ • ∑ r, (uhfBlockIso h r)ᴴ * x * uhfBlockIso h r :=
  rfl

/-- The entries of the block average. -/
theorem uhfAvg_apply (x : Matrix (Fin n.factorial) (Fin n.factorial) ℂ)
    (p q : Fin m.factorial) :
    uhfAvg h x p q =
      (uhfBlockDim m n : ℂ)⁻¹ * ∑ r, x (uhfBlockIndex h p r) (uhfBlockIndex h q r) := by
  rw [uhfAvg_def, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [mul_uhfBlockIso_apply, uhfBlockIso_conjTranspose_mul_apply]

theorem uhfAvg_add (x y : Matrix (Fin n.factorial) (Fin n.factorial) ℂ) :
    uhfAvg h (x + y) = uhfAvg h x + uhfAvg h y := by
  have hterm : ∀ r, (uhfBlockIso h r)ᴴ * (x + y) * uhfBlockIso h r =
      (uhfBlockIso h r)ᴴ * x * uhfBlockIso h r + (uhfBlockIso h r)ᴴ * y * uhfBlockIso h r :=
    fun r ↦ by rw [Matrix.mul_add, Matrix.add_mul]
  rw [uhfAvg_def h (x + y), uhfAvg_def h x, uhfAvg_def h y]
  simp only [hterm]
  rw [Finset.sum_add_distrib, smul_add]

theorem uhfAvg_smul (c : ℂ) (x : Matrix (Fin n.factorial) (Fin n.factorial) ℂ) :
    uhfAvg h (c • x) = c • uhfAvg h x := by
  have hterm : ∀ r, (uhfBlockIso h r)ᴴ * (c • x) * uhfBlockIso h r =
      c • ((uhfBlockIso h r)ᴴ * x * uhfBlockIso h r) :=
    fun r ↦ by rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [uhfAvg_def h (c • x), uhfAvg_def h x]
  simp only [hterm]
  rw [← Finset.smul_sum, smul_comm ((uhfBlockDim m n : ℂ)⁻¹) c]

/-- The block average as a linear map. -/
def uhfAvgLin : Matrix (Fin n.factorial) (Fin n.factorial) ℂ →ₗ[ℂ]
    Matrix (Fin m.factorial) (Fin m.factorial) ℂ where
  toFun := uhfAvg h
  map_add' := uhfAvg_add h
  map_smul' := uhfAvg_smul h

theorem uhfAvgLin_apply (x : Matrix (Fin n.factorial) (Fin n.factorial) ℂ) :
    uhfAvgLin h x = uhfAvg h x :=
  rfl

/-- **The block average is a left inverse of the amplification.** -/
theorem uhfAvg_amp (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) :
    uhfAvg h (uhfAmp h a) = a := by
  have hterm : ∀ r, (uhfBlockIso h r)ᴴ * uhfAmp h a * uhfBlockIso h r = a := fun r ↦ by
    rw [uhfBlockIso_conjTranspose_mul_amp, Matrix.mul_assoc, uhfBlockIso_conjTranspose_mul_iso,
      if_pos rfl, Matrix.mul_one]
  rw [uhfAvg_def]
  simp only [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ (uhfBlockDim_cast_ne_zero h), one_smul]

/-- Along a tower `k ≤ m ≤ n`, averaging down to `m` an element amplified from `k`
returns its amplification to `m`. -/
theorem uhfAvg_amp_of_le {k : ℕ} (hkm : k ≤ m)
    (b : Matrix (Fin k.factorial) (Fin k.factorial) ℂ) :
    uhfAvg h (uhfAmp (Nat.le_trans hkm h) b) = uhfAmp hkm b := by
  rw [← uhfAmp_uhfAmp hkm h b, uhfAvg_amp]

/-- **The bimodule property** over the amplified copy of `M_{m!}`. -/
theorem uhfAvg_amp_mul_mul_amp (a b : Matrix (Fin m.factorial) (Fin m.factorial) ℂ)
    (x : Matrix (Fin n.factorial) (Fin n.factorial) ℂ) :
    uhfAvg h (uhfAmp h a * x * uhfAmp h b) = a * uhfAvg h x * b := by
  have hterm : ∀ r, (uhfBlockIso h r)ᴴ * (uhfAmp h a * x * uhfAmp h b) * uhfBlockIso h r =
      a * ((uhfBlockIso h r)ᴴ * x * uhfBlockIso h r) * b := fun r ↦ by
    simp only [Matrix.mul_assoc]
    rw [uhfAmp_mul_iso h b r,
      uhfBlockIso_conjTranspose_mul_amp_assoc h a r (x * (uhfBlockIso h r * b))]
  rw [uhfAvg_def h (uhfAmp h a * x * uhfAmp h b), uhfAvg_def h x]
  simp only [hterm]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]

/-- The block average multiplies the trace by `d⁻¹`. -/
theorem uhfAvg_trace (x : Matrix (Fin n.factorial) (Fin n.factorial) ℂ) :
    Matrix.trace (uhfAvg h x) = (uhfBlockDim m n : ℂ)⁻¹ * Matrix.trace x := by
  rw [uhfAvg_def, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  congr 1
  calc ∑ r, Matrix.trace ((uhfBlockIso h r)ᴴ * x * uhfBlockIso h r)
      = ∑ r, Matrix.trace (uhfBlockIso h r * (uhfBlockIso h r)ᴴ * x) :=
        Finset.sum_congr rfl fun r _ ↦ by
          rw [Matrix.trace_mul_comm ((uhfBlockIso h r)ᴴ * x) (uhfBlockIso h r),
            Matrix.mul_assoc]
    _ = Matrix.trace (∑ r, uhfBlockIso h r * (uhfBlockIso h r)ᴴ * x) :=
        (Matrix.trace_sum Finset.univ fun r ↦ uhfBlockIso h r * (uhfBlockIso h r)ᴴ * x).symm
    _ = Matrix.trace x := by
        rw [← Matrix.sum_mul Finset.univ (fun r ↦ uhfBlockIso h r * (uhfBlockIso h r)ᴴ) x,
          sum_uhfBlockIso_mul_conjTranspose, Matrix.one_mul]

/-- **The block average preserves the normalized trace.** -/
theorem normTrace_uhfAvg (x : Matrix (Fin n.factorial) (Fin n.factorial) ℂ) :
    normTrace (uhfLevel m) (uhfAvg h x) = normTrace (uhfLevel n) x := by
  rw [normTrace, normTrace, card_uhfLevel, card_uhfLevel, uhfAvg_trace,
    ← factorial_mul_uhfBlockDim h, Nat.cast_mul]
  ring

/-- Each entry of the block average is bounded by the operator norm. -/
theorem norm_uhfAvg_apply_le (x : Matrix (Fin n.factorial) (Fin n.factorial) ℂ)
    (p q : Fin m.factorial) : ‖uhfAvg h x p q‖ ≤ ‖x‖ := by
  have hd : (0 : ℝ) < uhfBlockDim m n := Nat.cast_pos.2 (uhfBlockDim_pos h)
  rw [uhfAvg_apply, norm_mul, norm_inv, Complex.norm_natCast]
  calc (uhfBlockDim m n : ℝ)⁻¹ * ‖∑ r, x (uhfBlockIndex h p r) (uhfBlockIndex h q r)‖
      ≤ (uhfBlockDim m n : ℝ)⁻¹ * ∑ _r : Fin (uhfBlockDim m n), ‖x‖ :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ ↦
          OperatorNormCertificate.norm_entry_le_opNorm x _ _)) (inv_nonneg.2 hd.le)
    _ = ‖x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hd.ne', one_mul]

end

end GroupApproximation.Full.TWWSchafhauser
