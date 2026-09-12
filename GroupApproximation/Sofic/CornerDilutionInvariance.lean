import GroupApproximation.Sofic.NormTraceGap

/-!
# The relative rank of the averaging corner is unconstrained

`sec:limits` explains what an operator-norm obstruction must produce, and then
records what it need *not* produce:

> The relative rank of that substructure is unconstrained: padding leaves the
> averaging corner `q_n M_{d_n}(ℂ) q_n` untouched while `d_n` grows, so
> `r_n/d_n` may tend to zero while the argument uses the corner's own
> normalized trace.

`Sofic.NormTraceGap` already builds the padding — `padModel`, `padMatrix`, and
`l2_opNorm_cornerPad`, which is the statement that the corner block carries the
full operator norm.  What that file does not say is the sentence above: that
the corner is *unchanged* by padding while its relative rank goes to zero.
Both halves are proved here.

`cornerProj Y m` is the projection `q` onto the original block of the padded
model.  Three facts, in the order the sentence uses them:

* `cornerProj_compress` — `q (padMatrix A) q` is `A` again, in the corner:
  padding leaves `q M q` untouched.  With `l2_opNorm_cornerPad` and
  `padMatrix_sub` this gives `norm_padMatrix_sub`, so every operator-norm
  quantity of the model survives padding exactly.
* `normTrace_cornerProj` — the relative rank `r/d` is the ambient normalized
  trace of `q`, and equals `r/(r+m)`.
* `relativeRank_lt_of_lt` and `tendsto_relativeRank` — that ratio can be pushed
  below any bound, and tends to zero along the padding.

Meanwhile `normTrace_corner_eq` records the other half of the sentence: the
trace the argument actually uses on the corner divides by the corner's own
rank, so it is one of the quantities padding does not move.

Nothing in the development depends on this file.  It exists because the
sentence is an assertion about what the method does *not* require, and such an
assertion is discharged by exhibiting the freedom it claims.
-/

namespace GroupApproximation
namespace CornerDilutionInvariance

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## The corner projection -/

/-- The projection onto the unpadded block of a padded model. -/
def cornerProj (Y : FiniteModel) (m : ℕ) :
    Matrix (padModel Y m) (padModel Y m) ℂ :=
  Matrix.fromBlocks 1 0 0 0

theorem cornerProj_conjTranspose (Y : FiniteModel) (m : ℕ) :
    (cornerProj Y m)ᴴ = cornerProj Y m := by
  unfold cornerProj
  rw [Matrix.fromBlocks_conjTranspose]
  congr 1 <;> simp

theorem cornerProj_mul_self (Y : FiniteModel) (m : ℕ) :
    cornerProj Y m * cornerProj Y m = cornerProj Y m := by
  unfold cornerProj
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;> simp

/-- **Padding leaves the corner untouched.**  Compressing a padded matrix to
the corner returns the original matrix, sitting in the corner. -/
theorem cornerProj_compress (Y : FiniteModel) (m : ℕ) (A : Matrix Y Y ℂ) :
    cornerProj Y m * padMatrix Y m A * cornerProj Y m
      = Matrix.fromBlocks A 0 0 0 := by
  unfold cornerProj padMatrix
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

/-- **Every operator-norm quantity survives padding exactly.**  This is
`l2_opNorm_cornerPad` in the form the sentence uses it. -/
theorem norm_padMatrix_sub (Y : FiniteModel) (m : ℕ) (A B : Matrix Y Y ℂ) :
    ‖padMatrix Y m A - padMatrix Y m B‖ = ‖A - B‖ := by
  rw [padMatrix_sub, l2_opNorm_cornerPad]

/-! ## The relative rank -/

/-- The trace of a corner-supported matrix is the trace of its block. -/
theorem trace_fromBlocks_corner (Y : FiniteModel) (m : ℕ) (A : Matrix Y Y ℂ) :
    Matrix.trace (Matrix.fromBlocks A 0 0 0 :
        Matrix (padModel Y m) (padModel Y m) ℂ) = Matrix.trace A := by
  classical
  have hsum :
      (∑ p : Y ⊕ Fin m, (Matrix.fromBlocks A 0 0 0 :
          Matrix (padModel Y m) (padModel Y m) ℂ) p p)
        = (∑ i : Y, A i i) + ∑ _j : Fin m, (0 : ℂ) :=
    Fintype.sum_sum_type _
  show (∑ p : Y ⊕ Fin m, (Matrix.fromBlocks A 0 0 0 :
      Matrix (padModel Y m) (padModel Y m) ℂ) p p) = Matrix.trace A
  rw [hsum, Finset.sum_const_zero, add_zero]
  rfl

/-- The rank of the corner projection is the size of the corner. -/
theorem trace_cornerProj (Y : FiniteModel) (m : ℕ) :
    Matrix.trace (cornerProj Y m) = (Fintype.card Y : ℂ) :=
  (trace_fromBlocks_corner Y m 1).trans Matrix.trace_one

/-- **The relative rank `r/d` is the ambient normalized trace of the corner
projection**, and padding by `m` fresh points makes it `r/(r+m)`. -/
theorem normTrace_cornerProj (Y : FiniteModel) (m : ℕ) :
    normTrace (padModel Y m) (cornerProj Y m)
      = (Fintype.card Y : ℂ) / ((Fintype.card Y : ℂ) + (m : ℂ)) := by
  unfold normTrace
  rw [trace_cornerProj, card_padModel, Nat.cast_add]

/-- **The corner is normalized on its own range.**  The trace the argument uses
on the corner divides by the corner's own size, so padding does not move it. -/
theorem normTrace_corner_eq (Y : FiniteModel) (m : ℕ) (A : Matrix Y Y ℂ) :
    normTrace Y A
      = Matrix.trace (cornerProj Y m * padMatrix Y m A * cornerProj Y m)
          / (Fintype.card Y : ℂ) := by
  rw [cornerProj_compress, trace_fromBlocks_corner]
  rfl

/-- Padding past `r/ε` fresh points puts the relative rank below `ε`. -/
theorem relativeRank_lt_of_lt (Y : FiniteModel) {ε : ℝ} (hε : 0 < ε) {m : ℕ}
    (hm : (Fintype.card Y : ℝ) / ε < (m : ℝ)) :
    (Fintype.card Y : ℝ) / (Fintype.card (padModel Y m) : ℝ) < ε := by
  have hc : (0 : ℝ) ≤ (Fintype.card Y : ℝ) := Nat.cast_nonneg _
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hmul : (Fintype.card Y : ℝ) < (m : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hm
    exact hm
  have hd : ((Fintype.card (padModel Y m) : ℕ) : ℝ)
      = (Fintype.card Y : ℝ) + (m : ℝ) := by
    rw [card_padModel, Nat.cast_add]
  rw [hd]
  rcases eq_or_lt_of_le hc with hc0 | hc0
  · rw [← hc0, zero_div]
    exact hε
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_pos hε hc0]

/-- **"`r_n/d_n` may tend to zero."**  Along the padding, the relative rank of
the corner converges to zero — while, by `cornerProj_compress` and
`norm_padMatrix_sub`, the corner and every operator-norm quantity are fixed. -/
theorem tendsto_relativeRank (Y : FiniteModel) :
    Filter.Tendsto
      (fun m : ℕ ↦
        (Fintype.card Y : ℝ) / (Fintype.card (padModel Y m) : ℝ))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((Fintype.card Y : ℝ) / ε)
  refine ⟨N, fun m hm ↦ ?_⟩
  have hmR : (Fintype.card Y : ℝ) / ε < (m : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast hm)
  have hnn : (0 : ℝ) ≤
      (Fintype.card Y : ℝ) / (Fintype.card (padModel Y m) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  exact relativeRank_lt_of_lt Y hε hmR

/-- **The dilution statement, assembled.**  For every bound there is a padding
under which the corner and all of its operator-norm data are unchanged and the
relative rank is below the bound. -/
theorem exists_padding_relativeRank_lt (Y : FiniteModel) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ,
      (Fintype.card Y : ℝ) / (Fintype.card (padModel Y m) : ℝ) < ε ∧
      (∀ A : Matrix Y Y ℂ,
        cornerProj Y m * padMatrix Y m A * cornerProj Y m
          = Matrix.fromBlocks A 0 0 0) ∧
      (∀ A B : Matrix Y Y ℂ,
        ‖padMatrix Y m A - padMatrix Y m B‖ = ‖A - B‖) := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((Fintype.card Y : ℝ) / ε)
  exact ⟨m, relativeRank_lt_of_lt Y hε hm, cornerProj_compress Y m,
    norm_padMatrix_sub Y m⟩

end CornerDilutionInvariance
end GroupApproximation
