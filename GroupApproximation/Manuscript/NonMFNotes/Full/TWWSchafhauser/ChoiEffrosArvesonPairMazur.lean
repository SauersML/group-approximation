import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosArvesonPairSelection
import GroupApproximation.Analysis.VoiculescuAlmostOrthogonal

/-!
# Arveson pairs, step 2b: the quasicentral convex combination

Lane TWWSchafhauser-3a1, work order WO-TWWSchafhauser-3a-1.  In Arveson's
proof, Mazur's theorem turns the approximate unit of `J = ker π` into a
quasicentral one.  Here the convex combination is written out explicitly: the
average

`h = N⁻¹ ∑_{i < N} s i`

of the greedy selection of `ChoiEffrosArvesonPairSelection`.  Every clause
that holds for each member passes to the average.  That covers membership in
`J`, self-adjointness, `‖1 - h‖ ≤ 1` and absorption.  The commutator
`[h, y] = N⁻¹ ∑ᵢ [s i, y]` is a sum of almost orthogonal defects, so
`ShulmanFill.norm_sum_le_of_almostOrthogonal` bounds it by `√(M²/N + δ)`.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open Filter

noncomputable section

universe v w

variable {B : Type v} {C : Type w} [CStarAlgebra B] [CStarAlgebra C]

/-- A member of the approximate unit has norm at most `2`. -/
theorem arvesonPair_norm_le_two [Nontrivial B] {s : B} (hs : ‖1 - s‖ ≤ 1) : ‖s‖ ≤ 2 := by
  calc ‖s‖ = ‖1 - (1 - s)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖(1 : B)‖ + ‖1 - s‖ := norm_sub_le _ _
    _ ≤ 2 := by
        rw [norm_one]
        linarith

/-- The commutator with a member of the approximate unit is at most `4 ‖y‖`. -/
theorem arvesonPair_norm_commutator_le [Nontrivial B] {s : B} (hs : ‖1 - s‖ ≤ 1)
    (y : B) : ‖s * y - y * s‖ ≤ 4 * ‖y‖ := by
  have h2 := arvesonPair_norm_le_two hs
  have hy := norm_nonneg y
  calc ‖s * y - y * s‖ ≤ ‖s * y‖ + ‖y * s‖ := norm_sub_le _ _
    _ ≤ ‖s‖ * ‖y‖ + ‖y‖ * ‖s‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 4 * ‖y‖ := by nlinarith

/-- **The quasicentral average.**  Some element of `ker π` commutes with every
`y ∈ Y` to within `ε`, satisfies `‖1 - h‖ ≤ 1`, and absorbs every `x ∈ X` to
within `‖π x‖ + η`. -/
theorem arvesonPair_exists_average [Nontrivial B] (π : B →⋆ₐ[ℂ] C)
    (Y X : Finset B) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ h : B, h ∈ arvesonKernel π ∧ IsSelfAdjoint h ∧ ‖1 - h‖ ≤ 1 ∧
      (∀ y ∈ Y, ‖h * y - y * h‖ ≤ ε) ∧ ∀ x ∈ X, ‖x - h * x‖ ≤ ‖π x‖ + η := by
  -- a single bound for all the defects
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 4 * ∑ z ∈ Y, ‖z‖ := ⟨_, rfl⟩
  -- how many members to average
  obtain ⟨N, hN0, hNbig⟩ : ∃ N : ℕ, 0 < N ∧ 2 * M ^ 2 / ε ^ 2 ≤ (N : ℝ) := by
    refine ⟨⌈2 * M ^ 2 / ε ^ 2⌉₊ + 1, Nat.succ_pos _, ?_⟩
    have h := Nat.le_ceil (2 * M ^ 2 / ε ^ 2)
    push_cast
    linarith
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt hNR
  have hNCne : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hN0.ne'
  have hnormc : ‖((N : ℂ))⁻¹‖ = ((N : ℝ))⁻¹ := by simp
  -- how small the cross terms must be
  obtain ⟨δ, hδpos, hsize⟩ : ∃ δ : ℝ, 0 < δ ∧
      (N : ℝ) * M ^ 2 + (N : ℝ) ^ 2 * δ ≤ ((N : ℝ) * ε) ^ 2 := by
    have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
    refine ⟨ε ^ 2 / 2, div_pos hε2 (by norm_num), ?_⟩
    rw [div_le_iff₀ hε2] at hNbig
    nlinarith [mul_le_mul_of_nonneg_left hNbig hNR.le]
  -- the selection
  obtain ⟨s, hs, hscross⟩ := arvesonPair_exists_selection π Y X hδpos hη N
  obtain ⟨h, hhdef⟩ : ∃ h : B, h = (N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, s i := ⟨_, rfl⟩
  -- membership in the kernel
  have hmem : h ∈ arvesonKernel π := by
    rw [hhdef, Algebra.smul_def]
    exact (arvesonKernel π).mul_mem_left _
      ((arvesonKernel π).sum_mem fun i _ ↦ (hs i).1)
  -- self-adjointness
  have hsa : IsSelfAdjoint h := by
    have hstarc : star ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by rw [star_inv₀, star_natCast]
    show star h = h
    rw [hhdef, star_smul, hstarc, star_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ (hs i).2.1.star_eq
  -- whatever every member absorbs, the average absorbs
  have habs : ∀ (T : B) (d : ℝ), (∀ i, ‖T - s i * T‖ ≤ d) → ‖T - h * T‖ ≤ d := by
    intro T d hT
    have hexp : (N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, (T - s i * T) = T - h * T := by
      rw [hhdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        ← Finset.sum_mul, smul_sub, ← smul_mul_assoc, ← Nat.cast_smul_eq_nsmul (R := ℂ),
        smul_smul, inv_mul_cancel₀ hNCne, one_smul]
    have hsum : ‖∑ i ∈ Finset.range N, (T - s i * T)‖ ≤ (N : ℝ) * d := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i ∈ Finset.range N, ‖T - s i * T‖
          ≤ ∑ _i ∈ Finset.range N, d := Finset.sum_le_sum fun i _ ↦ hT i
        _ = (N : ℝ) * d := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← hexp, norm_smul, hnormc]
    calc ((N : ℝ))⁻¹ * ‖∑ i ∈ Finset.range N, (T - s i * T)‖
        ≤ ((N : ℝ))⁻¹ * ((N : ℝ) * d) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = d := by rw [← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
  -- the contraction clause
  have hone : ‖1 - h‖ ≤ 1 := by
    have h1 := habs 1 1 fun i ↦ by
      rw [mul_one]
      exact (hs i).2.2.1
    rw [mul_one] at h1
    exact h1
  -- the commutator clause
  have hcomm : ∀ y ∈ Y, ‖h * y - y * h‖ ≤ ε := by
    intro y hy
    have hyS : ‖y‖ ≤ ∑ z ∈ Y, ‖z‖ := Finset.single_le_sum (fun z _ ↦ norm_nonneg z) hy
    have hexp : h * y - y * h = (N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, (s i * y - y * s i) := by
      rw [hhdef, smul_mul_assoc, mul_smul_comm, ← smul_sub, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
    have hAO : ‖∑ i ∈ Finset.range N, (s i * y - y * s i)‖ ≤ (N : ℝ) * ε := by
      refine ShulmanFill.norm_sum_le_of_almostOrthogonal (fun i ↦ s i * y - y * s i) N M δ ε
        hδpos.le hε.le ?_ ?_ hsize
      · intro i _
        show ‖s i * y - y * s i‖ ≤ M
        exact (arvesonPair_norm_commutator_le (hs i).2.2.1 y).trans (by linarith)
      · intro i hi j hj hij
        show ‖(s i * y - y * s i) * star (s j * y - y * s j)‖ ≤ δ
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact hscross i j hlt hj y hy
        · have h2 := hscross j i hgt hi y hy
          rw [← norm_star, star_mul, star_star]
          exact h2
    rw [hexp, norm_smul, hnormc]
    calc ((N : ℝ))⁻¹ * ‖∑ i ∈ Finset.range N, (s i * y - y * s i)‖
        ≤ ((N : ℝ))⁻¹ * ((N : ℝ) * ε) := mul_le_mul_of_nonneg_left hAO (by positivity)
      _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
  exact ⟨h, hmem, hsa, hone, hcomm, fun x hx ↦ habs x _ fun i ↦ (hs i).2.2.2 x hx⟩

end

end TWWSchafhauser
end Full
end GroupApproximation
