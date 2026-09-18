import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.PowersStormerAlgebra
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.PowersStormerUnitary
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.CloseSqrt
import GroupApproximation.Sofic.LeavittTraceFloor
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-26, part 6: `ContractionSqrtCommutatorStatement` holds

Let `y` be a contraction and `T ≥ 0` with `T² = h` and `tr h = 1`.

1. Doubling: `Yd = [[0, y], [yᴴ, 0]]` is Hermitian with `1 − Yd² = diag(1 − yyᴴ, 1 − yᴴy) ≥ 0`.
   Put `T' = diag(T, T)`, so `T'² = diag(h, h)`.
2. Dilation (part 2): take `D` Hermitian, commuting with `Yd`, with `D² = 1 − Yd²`. Then
   `U = Yd + iD` is unitary.
3. Powers--Størmer (part 3): `‖UT' − T'U‖₂² ≤ re tr((UT'² − T'²U) G)` for some unitary `G`.
4. `‖yT − Ty‖₂²` is at most `‖[Yd, T']‖₂²`, the `(1,2)` block, which is at most `‖[U, T']‖₂²`.
5. The right side is at most `|tr([Yd, T'²] G)| + |tr(D T'² G)| + |tr(T'² D G)|`.
   The first term is at most `2η`, by the commutator hypothesis on the two off-diagonal
   blocks of `G`. By Cauchy--Schwarz, the squares of the others are at most
   `tr(T'²) tr(D² T'²) ≤ 2 · 2η`.

So `‖yT − Ty‖₂² ≤ 2η + 4√η`, and `η = min(ε/4, ε²/64)` gives the bound `ε`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **The quantitative Powers--Størmer bound for one contraction.** The two Cauchy--Schwarz
terms `a` and `b` have squares at most `4η`. -/
theorem powersStormer_contraction_bound {y h T : Matrix m m ℂ} {η : ℝ}
    (hQ : (1 - yᴴ * y).PosSemidef) (hP : (1 - y * yᴴ).PosSemidef) (hT : T.PosSemidef)
    (hTh : T * T = h) (htr : trace h = 1)
    (hcomm : ∀ x : Matrix m m ℂ, ‖trace ((h * y - y * h) * x)‖ ≤ η * ‖x‖)
    (h1 : ‖trace (h * (1 - yᴴ * y))‖ ≤ η) (h2 : ‖trace (h * (1 - y * yᴴ))‖ ≤ η) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a ^ 2 ≤ 4 * η ∧ b ^ 2 ≤ 4 * η ∧
      (trace ((y * T - T * y)ᴴ * (y * T - T * y))).re ≤ 2 * η + (a + b) := by
  have hη0 : 0 ≤ η := (norm_nonneg _).trans h1
  have hh : hᴴ = h := by rw [← hTh, conjTranspose_mul, hT.isHermitian.eq]
  obtain ⟨Yd, hYd⟩ : ∃ Yd : Matrix (m ⊕ m) (m ⊕ m) ℂ, Yd = fromBlocks 0 y yᴴ 0 :=
    ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T' : Matrix (m ⊕ m) (m ⊕ m) ℂ, T' = fromBlocks T 0 0 T :=
    ⟨_, rfl⟩
  have hTpsd : T'.PosSemidef := by
    rw [hT']
    exact powersStormer_posSemidef_fromBlocks hT hT
  have hTs : T'ᴴ = T' := hTpsd.isHermitian.eq
  have hYs : Ydᴴ = Yd := by rw [hYd, powersStormer_doubling_conjTranspose]
  have hYY : (1 - Yd * Yd).PosSemidef := by
    rw [hYd, powersStormer_one_sub_doubling_sq]
    exact powersStormer_posSemidef_fromBlocks hP hQ
  have hsq : T' * T' = fromBlocks h 0 0 h := by
    rw [hT']
    exact powersStormer_diag_mul_diag hTh
  obtain ⟨D, hDs, hc, hDD⟩ := powersStormer_exists_dilation hYs hYY
  obtain ⟨hU1, hU2⟩ := powersStormer_unitary_of_dilation hYs hDs hc hDD
  obtain ⟨G, hG1, hG2, hPS⟩ := powersStormer_unitary_commutator hU1 hU2 hTpsd rfl
  -- Step 4: the `(1,2)` block and the imaginary part.
  have hK : toBlocks₁₂ (Yd * T' - T' * Yd) = y * T - T * y := by
    rw [hYd, hT', powersStormer_doubling_commutator, toBlocks_fromBlocks₁₂]
  have hL := powersStormer_re_trace_gram_toBlocks₁₂_le (Yd * T' - T' * Yd)
  rw [hK] at hL
  have hM := powersStormer_re_trace_gram_commutator_le hYs hDs hTs
  -- Step 5: split the Powers--Størmer right side.
  have hRHS := powersStormer_re_trace_commutator_mul_le Yd D (T' * T') G
  have hG21 : ‖toBlocks₂₁ G‖ ≤ 1 :=
    powersStormer_norm_toBlocks₂₁_le (powersStormer_norm_le_one_of_conjTranspose_mul_self hG1)
  have hG12 : ‖toBlocks₁₂ G‖ ≤ 1 :=
    powersStormer_norm_toBlocks₁₂_le (powersStormer_norm_le_one_of_conjTranspose_mul_self hG1)
  have hfirst : ‖trace ((Yd * (T' * T') - T' * T' * Yd) * G)‖ ≤ 2 * η := by
    rw [hsq, hYd, powersStormer_doubling_commutator, powersStormer_trace_offdiag_mul]
    have e1 : trace ((y * h - h * y) * toBlocks₂₁ G)
        = -trace ((h * y - y * h) * toBlocks₂₁ G) := by
      rw [← trace_neg, ← neg_mul, neg_sub]
    have e2 : trace ((yᴴ * h - h * yᴴ) * toBlocks₁₂ G)
        = star (trace ((h * y - y * h) * (toBlocks₁₂ G)ᴴ)) := by
      rw [← powersStormer_trace_conjTranspose_mul, conjTranspose_sub, conjTranspose_mul,
        conjTranspose_mul, hh]
    rw [e1, e2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_star]
    have b1 := hcomm (toBlocks₂₁ G)
    have b2 := hcomm (toBlocks₁₂ G)ᴴ
    rw [l2_opNorm_conjTranspose] at b2
    have c1 := mul_le_of_le_one_right hη0 hG21
    have c2 := mul_le_of_le_one_right hη0 hG12
    linarith
  -- Step 5, continued: the two Cauchy--Schwarz terms.
  obtain ⟨cs1, cs2⟩ := powersStormer_norm_trace_sq_pair hTs hDs hG1 hG2
  have htr' : (trace (T' * T')).re = 2 := by
    rw [hsq, powersStormer_trace_fromBlocks, htr]
    norm_num
  have hDDh : (trace (D * D * (T' * T'))).re ≤ 2 * η := by
    rw [hDD, hYd, powersStormer_one_sub_doubling_sq, hsq, powersStormer_trace_diag_mul_diag,
      trace_mul_comm (1 - y * yᴴ) h, trace_mul_comm (1 - yᴴ * y) h, Complex.add_re]
    linarith [Complex.re_le_norm (trace (h * (1 - y * yᴴ))),
      Complex.re_le_norm (trace (h * (1 - yᴴ * y)))]
  rw [htr'] at cs1 cs2
  refine ⟨‖trace (D * (T' * T') * G)‖, ‖trace (T' * T' * D * G)‖, norm_nonneg _,
    norm_nonneg _, by linarith, by linarith, ?_⟩
  linarith

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_contraction_bound

/-- If `0 ≤ c` and `c² ≤ 4η` with `η ≤ ε²/64`, then `c ≤ ε/4`. -/
theorem powersStormer_le_of_sq_le {ε η c : ℝ} (hε : 0 < ε) (hη : η ≤ ε ^ 2 / 64)
    (hc : 0 ≤ c) (hc2 : c ^ 2 ≤ 4 * η) : c ≤ ε / 4 := by
  by_contra hlt
  have hlt' : ε / 4 < c := not_le.mp hlt
  have h3 : 0 < (c - ε / 4) * (c + ε / 4) := mul_pos (by linarith) (by linarith)
  nlinarith [hc]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_le_of_sq_le

/-- **`ContractionSqrtCommutatorStatement` holds**, with `η = min(ε/4, ε²/64)`. -/
theorem powersStormer_contractionSqrtCommutator : ContractionSqrtCommutatorStatement := by
  intro ε hε
  refine ⟨min (ε / 4) (ε ^ 2 / 64),
    lt_min (div_pos hε (by norm_num)) (div_pos (pow_pos hε 2) (by norm_num)), ?_⟩
  intro Y y h T hy hT hTh htr hcomm h1 h2
  rw [Matrix.star_eq_conjTranspose] at h1 h2
  have hQ : (1 - yᴴ * y).PosSemidef :=
    one_sub_conjTranspose_mul_posSemidef_of_l2_opNorm_le_one Y y hy
  have hP : (1 - y * yᴴ).PosSemidef := by
    have h0 := one_sub_conjTranspose_mul_posSemidef_of_l2_opNorm_le_one Y yᴴ
      ((l2_opNorm_conjTranspose y).trans_le hy)
    rwa [conjTranspose_conjTranspose] at h0
  obtain ⟨a, b, ha, hb, ha2, hb2, hbound⟩ :=
    powersStormer_contraction_bound hQ hP hT hTh htr hcomm h1 h2
  have hη1 : min (ε / 4) (ε ^ 2 / 64) ≤ ε / 4 := min_le_left _ _
  have hη2 : min (ε / 4) (ε ^ 2 / 64) ≤ ε ^ 2 / 64 := min_le_right _ _
  have hA := powersStormer_le_of_sq_le hε hη2 ha ha2
  have hB := powersStormer_le_of_sq_le hε hη2 hb hb2
  linarith

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_contractionSqrtCommutator

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
