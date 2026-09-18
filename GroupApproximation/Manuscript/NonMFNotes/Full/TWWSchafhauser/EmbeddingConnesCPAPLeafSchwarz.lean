import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosCPBasics
import GroupApproximation.Analysis.CStarCPStarTarget
import Mathlib.Analysis.CStarAlgebra.Module.Constructions

/-!
# Connes' trick, CPAP leaf: the Choi--Schwarz inequality for ucp maps

Lane TWWSch3b1A (work order WO-3b1-A).  This file is the first leaf of
`isMatrixLeftBimoduleCPAP_of_isNuclearCStarAlgebra`, which feeds the Tikuisis--White--Winter
input `\cite{TWW}` of `non_mf_group_notes.tex`.  That input is the quasidiagonality of nuclear
C⋆-algebras, used in the proof of `thm:fixed-radical-membership`.
Sources: M.-D. Choi, *A Schwarz inequality for positive linear maps on C⋆-algebras* (1974), and
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Prop 2.2.6 and the proof
of Thm 6.2.7.

For a unital completely positive `φ`, positivity of the `3 × 3` amplification at the row
`(1, x, y)` gives two columns `z`, `w` with Gram entries
`⟨z, w⟩ = φ(x⋆y) - φ(x)⋆φ(y)`, `⟨z, z⟩ = φ(x⋆x) - φ(x)⋆φ(x)` and `⟨w, w⟩ = φ(y⋆y) - φ(y)⋆φ(y)`.
The Hilbert-module Cauchy--Schwarz inequality then gives the norm bound
`norm_map_star_mul_sub_le`.
`norm_schwarzDefect_comp_le` compares the Schwarz defects of `ψ` and `ψ ∘ ρ`.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

universe u v w

section ColPair

variable {C : Type v} [CStarAlgebra C] {ι : Type} [Fintype ι]

/-- The `C`-valued pairing `∑ₖ uₖ⋆ vₖ` of two columns (Choi 1974). -/
def cpapColPair (u v : ι → C) : C := ∑ k, star (u k) * v k

theorem cpapColPair_shift_left (u a v : ι → C) (c : C) :
    cpapColPair (fun k ↦ u k - a k * c) v = cpapColPair u v - star c * cpapColPair a v := by
  simp only [cpapColPair]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [star_sub, star_mul, sub_mul, mul_assoc]

theorem cpapColPair_shift_right (u v a : ι → C) (c : C) :
    cpapColPair u (fun k ↦ v k - a k * c) = cpapColPair u v - cpapColPair u a * c := by
  simp only [cpapColPair]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_sub, mul_assoc]

/-- **Cauchy--Schwarz for the column pairing**, from the Hilbert C⋆-module inequality
`CStarModule.norm_inner_le` on `C⋆ᵐᵒᵈ(C, ι → C)` (Brown--Ozawa, proof of Prop 2.2.6). -/
theorem norm_cpapColPair_le (u v : ι → C) :
    ‖cpapColPair u v‖ ≤ √‖cpapColPair u u‖ * √‖cpapColPair v v‖ := by
  letI : PartialOrder C := CStarAlgebra.spectralOrder C
  letI : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  have hinner : ∀ w z : ι → C,
      inner C ((_root_.WithCStarModule.equiv C (ι → C)).symm fun k ↦ star (w k))
        ((_root_.WithCStarModule.equiv C (ι → C)).symm fun k ↦ star (z k)) =
        cpapColPair z w := by
    intro w z
    simp only [cpapColPair, _root_.WithCStarModule.pi_inner,
      _root_.WithCStarModule.equiv_symm_pi_apply, _root_.WithCStarModule.inner_def, star_star]
  have hnorm : ∀ w : ι → C,
      ‖(_root_.WithCStarModule.equiv C (ι → C)).symm fun k ↦ star (w k)‖ =
        √‖cpapColPair w w‖ := by
    intro w
    rw [_root_.CStarModule.norm_eq_sqrt_norm_inner_self (A := C)
      ((_root_.WithCStarModule.equiv C (ι → C)).symm fun k ↦ star (w k)), hinner]
  have h := _root_.CStarModule.norm_inner_le (A := C) (_root_.WithCStarModule C (ι → C))
    (x := (_root_.WithCStarModule.equiv C (ι → C)).symm fun k ↦ star (v k))
    (y := (_root_.WithCStarModule.equiv C (ι → C)).symm fun k ↦ star (u k))
  rw [hinner, hnorm, hnorm] at h
  exact h.trans_eq (mul_comm _ _)

end ColPair

section Gram

variable {B : Type u} {C : Type v} [CStarAlgebra B] [CStarAlgebra C]

/-- The `3 × 3` matrix whose first row is `r` and whose other rows vanish. -/
def cpapRowMatrix (r : Fin 3 → B) : CStarMatrix (Fin 3) (Fin 3) B :=
  CStarMatrix.ofMatrix fun i j ↦ if i = 0 then r j else 0

theorem cpapRowMatrix_apply (r : Fin 3 → B) (i j : Fin 3) :
    cpapRowMatrix r i j = if i = 0 then r j else 0 := rfl

theorem cpapRowMatrix_star_mul_self_apply (r : Fin 3 → B) (i j : Fin 3) :
    (star (cpapRowMatrix r) * cpapRowMatrix r) i j = star (r i) * r j := by
  have h0 : ∀ k : Fin 3, cpapRowMatrix r 0 k = r k := fun k ↦ by
    rw [cpapRowMatrix_apply, if_pos rfl]
  have h1 : ∀ k : Fin 3, cpapRowMatrix r 1 k = 0 := fun k ↦ by
    rw [cpapRowMatrix_apply, if_neg (show (1 : Fin 3) ≠ 0 by decide)]
  have h2 : ∀ k : Fin 3, cpapRowMatrix r 2 k = 0 := fun k ↦ by
    rw [cpapRowMatrix_apply, if_neg (show (2 : Fin 3) ≠ 0 by decide)]
  have hs : ∀ k l : Fin 3, (star (cpapRowMatrix r)) k l = star (cpapRowMatrix r l k) :=
    fun _ _ ↦ CStarMatrix.star_apply
  calc (star (cpapRowMatrix r) * cpapRowMatrix r) i j
      = ∑ k : Fin 3, (star (cpapRowMatrix r)) i k * cpapRowMatrix r k j := CStarMatrix.mul_apply
    _ = (star (cpapRowMatrix r)) i 0 * cpapRowMatrix r 0 j
          + (star (cpapRowMatrix r)) i 1 * cpapRowMatrix r 1 j
          + (star (cpapRowMatrix r)) i 2 * cpapRowMatrix r 2 j := Fin.sum_univ_three _
    _ = star (r i) * r j := by simp only [hs, h0, h1, h2, star_zero, zero_mul, add_zero]

/-- **The Gram columns of a completely positive map** at a row `r`: positivity of
`[φ(rᵢ⋆ rⱼ)]` (Choi 1974). -/
theorem exists_cpapGram_of_isCompletelyPositive {φ : B →ₗ[ℂ] C}
    (hφ : CStarExactness.IsCompletelyPositive φ) (r : Fin 3 → B) :
    ∃ P : CStarMatrix (Fin 3) (Fin 3) C, ∀ i j : Fin 3,
      cpapColPair (fun k ↦ P k i) (fun k ↦ P k j) = φ (star (r i) * r j) := by
  obtain ⟨P, hP⟩ := hφ 3 (star (cpapRowMatrix r) * cpapRowMatrix r) ⟨cpapRowMatrix r, rfl⟩
  have hstarP : ∀ i k : Fin 3, (star P) i k = star (P k i) := fun _ _ ↦ CStarMatrix.star_apply
  refine ⟨P, fun i j ↦ ?_⟩
  symm
  calc φ (star (r i) * r j) = φ ((star (cpapRowMatrix r) * cpapRowMatrix r) i j) := by
        rw [cpapRowMatrix_star_mul_self_apply]
    _ = ((star (cpapRowMatrix r) * cpapRowMatrix r).map ⇑φ) i j := rfl
    _ = (star P * P) i j := congrArg (fun T : CStarMatrix (Fin 3) (Fin 3) C ↦ T i j) hP
    _ = ∑ k : Fin 3, (star P) i k * P k j := CStarMatrix.mul_apply
    _ = ∑ k : Fin 3, star (P k i) * P k j := Finset.sum_congr rfl fun k _ ↦ by rw [hstarP]
    _ = cpapColPair (fun k ↦ P k i) (fun k ↦ P k j) := rfl

/-- **The Schwarz columns** (Choi 1974): for a unital completely positive `φ`, the Schwarz
defects `φ(x⋆y) - φ(x)⋆φ(y)` are the Gram entries of two columns. -/
theorem exists_cpapSchwarz_columns {φ : B →ₗ[ℂ] C}
    (hφ : CStarExactness.IsCompletelyPositive φ) (h1 : φ 1 = 1) (x y : B) :
    ∃ z w : Fin 3 → C,
      cpapColPair z w = φ (star x * y) - star (φ x) * φ y ∧
      cpapColPair z z = φ (star x * x) - star (φ x) * φ x ∧
      cpapColPair w w = φ (star y * y) - star (φ y) * φ y := by
  obtain ⟨P, hG⟩ := exists_cpapGram_of_isCompletelyPositive hφ ![1, x, y]
  have hr0 : (![1, x, y] : Fin 3 → B) 0 = 1 := rfl
  have hr1 : (![1, x, y] : Fin 3 → B) 1 = x := rfl
  have hr2 : (![1, x, y] : Fin 3 → B) 2 = y := rfl
  have h00 : cpapColPair (fun k ↦ P k 0) (fun k ↦ P k 0) = 1 := by
    rw [hG 0 0, hr0, star_one, one_mul, h1]
  have h01 : cpapColPair (fun k ↦ P k 0) (fun k ↦ P k 1) = φ x := by
    rw [hG 0 1, hr0, hr1, star_one, one_mul]
  have h02 : cpapColPair (fun k ↦ P k 0) (fun k ↦ P k 2) = φ y := by
    rw [hG 0 2, hr0, hr2, star_one, one_mul]
  have h10 : cpapColPair (fun k ↦ P k 1) (fun k ↦ P k 0) = star (φ x) := by
    rw [hG 1 0, hr1, hr0, mul_one, GroupApproximation.OrderZero.map_star_of_cp hφ]
  have h20 : cpapColPair (fun k ↦ P k 2) (fun k ↦ P k 0) = star (φ y) := by
    rw [hG 2 0, hr2, hr0, mul_one, GroupApproximation.OrderZero.map_star_of_cp hφ]
  have h11 : cpapColPair (fun k ↦ P k 1) (fun k ↦ P k 1) = φ (star x * x) := by
    rw [hG 1 1, hr1]
  have h12 : cpapColPair (fun k ↦ P k 1) (fun k ↦ P k 2) = φ (star x * y) := by
    rw [hG 1 2, hr1, hr2]
  have h22 : cpapColPair (fun k ↦ P k 2) (fun k ↦ P k 2) = φ (star y * y) := by
    rw [hG 2 2, hr2]
  refine ⟨fun k ↦ P k 1 - P k 0 * φ x, fun k ↦ P k 2 - P k 0 * φ y, ?_, ?_, ?_⟩
  · rw [cpapColPair_shift_left, cpapColPair_shift_right, cpapColPair_shift_right,
      h12, h10, h02, h00, one_mul, sub_self, mul_zero, sub_zero]
  · rw [cpapColPair_shift_left, cpapColPair_shift_right, cpapColPair_shift_right,
      h11, h10, h01, h00, one_mul, sub_self, mul_zero, sub_zero]
  · rw [cpapColPair_shift_left, cpapColPair_shift_right, cpapColPair_shift_right,
      h22, h20, h02, h00, one_mul, sub_self, mul_zero, sub_zero]

/-- **The Choi--Schwarz inequality** for a unital completely positive map (Choi 1974;
Brown--Ozawa, proof of Thm 6.2.7):
`‖φ(x⋆y) - φ(x)⋆φ(y)‖ ≤ ‖φ(x⋆x) - φ(x)⋆φ(x)‖^{1/2} ‖φ(y⋆y) - φ(y)⋆φ(y)‖^{1/2}`. -/
theorem norm_map_star_mul_sub_le {φ : B →ₗ[ℂ] C}
    (hφ : CStarExactness.IsCompletelyPositive φ) (h1 : φ 1 = 1) (x y : B) :
    ‖φ (star x * y) - star (φ x) * φ y‖ ≤
      √‖φ (star x * x) - star (φ x) * φ x‖ * √‖φ (star y * y) - star (φ y) * φ y‖ := by
  obtain ⟨z, w, hzw, hzz, hww⟩ := exists_cpapSchwarz_columns hφ h1 x y
  rw [← hzw, ← hzz, ← hww]
  exact norm_cpapColPair_le z w

/-- The Schwarz defect of a contraction is at most `(2‖y‖)²`. -/
theorem sqrt_norm_schwarzDefect_le {φ : B →ₗ[ℂ] C} (hc : ∀ b, ‖φ b‖ ≤ ‖b‖) (y : B) :
    √‖φ (star y * y) - star (φ y) * φ y‖ ≤ 2 * ‖y‖ := by
  have h1 : ‖φ (star y * y)‖ ≤ ‖y‖ * ‖y‖ := (hc _).trans CStarRing.norm_star_mul_self.le
  have h2 : ‖star (φ y) * φ y‖ ≤ ‖y‖ * ‖y‖ := by
    rw [CStarRing.norm_star_mul_self]
    exact mul_le_mul (hc y) (hc y) (norm_nonneg _) (norm_nonneg _)
  have h3 : ‖φ (star y * y) - star (φ y) * φ y‖ ≤ (2 * ‖y‖) ^ 2 := by
    have h4 := (norm_sub_le (φ (star y * y)) (star (φ y) * φ y)).trans (add_le_add h1 h2)
    nlinarith [h4, mul_nonneg (norm_nonneg y) (norm_nonneg y)]
  calc √‖φ (star y * y) - star (φ y) * φ y‖ ≤ √((2 * ‖y‖) ^ 2) := Real.sqrt_le_sqrt h3
    _ = 2 * ‖y‖ := Real.sqrt_sq (by positivity)

/-- **Schwarz defects under composition** (Brown--Ozawa, proof of Thm 6.2.7): for unital
completely positive `ρ` and `ψ`, the defect of `ψ` at `ρ b` is dominated by that of `ψ ∘ ρ`
at `b`, since `ψ(ρ(bb⋆)) - ψ(ρ b)ψ(ρ b)⋆` is that defect plus the positive element
`ψ(ρ(bb⋆) - ρ(b)ρ(b)⋆)`. -/
theorem norm_schwarzDefect_comp_le {D : Type w} [CStarAlgebra D] {ρ : B →ₗ[ℂ] C}
    {ψ : C →ₗ[ℂ] D} (hρ : CStarExactness.IsCompletelyPositive ρ) (hρ1 : ρ 1 = 1)
    (hψ : CStarExactness.IsCompletelyPositive ψ) (hψ1 : ψ 1 = 1) (b : B) :
    ‖ψ (ρ b * star (ρ b)) - ψ (ρ b) * star (ψ (ρ b))‖ ≤
      ‖ψ (ρ (b * star b)) - ψ (ρ b) * star (ψ (ρ b))‖ := by
  letI : PartialOrder D := CStarAlgebra.spectralOrder D
  letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  have hρs : ρ (star b) = star (ρ b) := GroupApproximation.OrderZero.map_star_of_cp hρ b
  have hψs : ψ (star (ρ b)) = star (ψ (ρ b)) :=
    GroupApproximation.OrderZero.map_star_of_cp hψ (ρ b)
  obtain ⟨z, _, _, hzz, _⟩ := exists_cpapSchwarz_columns hρ hρ1 (star b) (star b)
  obtain ⟨w, _, _, hww, _⟩ :=
    exists_cpapSchwarz_columns hψ hψ1 (star (ρ b)) (star (ρ b))
  rw [star_star, hρs, star_star] at hzz
  rw [star_star, hψs, star_star] at hww
  have hE : 0 ≤ ψ (cpapColPair z z) := by
    unfold cpapColPair
    rw [map_sum]
    refine Finset.sum_nonneg fun k _ ↦ ?_
    obtain ⟨p, hp⟩ := exists_map_star_mul_self_eq hψ (z k)
    rw [hp]
    exact star_mul_self_nonneg p
  have hW : 0 ≤ cpapColPair w w := by
    unfold cpapColPair
    exact Finset.sum_nonneg fun k _ ↦ star_mul_self_nonneg (w k)
  have hsplit : ψ (ρ (b * star b)) - ψ (ρ b) * star (ψ (ρ b)) =
      ψ (cpapColPair z z) + cpapColPair w w := by
    rw [hzz, hww, map_sub]
    abel
  rw [← hww, hsplit]
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le hW (le_add_of_nonneg_left hE)

end Gram

end

end TWWSchafhauser
end Full
end GroupApproximation
