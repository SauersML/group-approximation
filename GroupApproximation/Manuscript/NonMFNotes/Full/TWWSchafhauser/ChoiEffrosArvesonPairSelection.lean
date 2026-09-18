import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosArvesonPairQuotient

/-!
# Arveson pairs, step 2a: quasicentral selection

Lane TWWSchafhauser-3a1, work order WO-TWWSchafhauser-3a-1.  The textbook
proof makes an approximate unit of `J = ker π` quasicentral by a weak limit
and Mazur's theorem.  This file uses a norm-only substitute that needs no dual
space and no separability.

Put `D(h) = h y - y h`.  When `h ∈ J`, the defect `D(h)` lies in `J`.  For a
self-adjoint `e` the product with a later defect is a difference of two
absorption errors:

`D(h) ⋆(D(e)) = (D(h) y⋆ e - D(h) y⋆) - (D(h) e - D(h)) y⋆`,

and both errors tend to `0` along the approximate unit, because `D(h)` and
`D(h) y⋆` lie in `J` (`arvesonPair_eventually_cross`).  Choosing one element at
a time along the filter (`arvesonPair_exists_selection`) gives a finite sequence
of good members of the unit whose defects are pairwise almost orthogonal.  The
average of that sequence is taken in `ChoiEffrosArvesonPairMazur`.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open Filter

noncomputable section

universe v w

variable {B : Type v} {C : Type w} [CStarAlgebra B] [CStarAlgebra C]

/-- The defect identity behind almost orthogonality, for self-adjoint `e`. -/
theorem arvesonDefect_mul_star (D y e : B) (he : IsSelfAdjoint e) :
    D * star (e * y - y * e)
      = (D * star y * e - D * star y) - (D * e - D) * star y := by
  rw [star_sub, star_mul, star_mul, he.star_eq]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- **Cross terms vanish along the unit**: for a fixed `D ∈ ker π`, eventually
`‖D ⋆(e y - y e)‖ ≤ δ`. -/
theorem arvesonPair_eventually_cross [Nontrivial B] (π : B →⋆ₐ[ℂ] C) (y D : B)
    (hD : D ∈ arvesonKernel π) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ e in (arvesonUnit π).filter, ‖D * star (e * y - y * e)‖ ≤ δ := by
  have hDs : D * star y ∈ arvesonKernel π := (arvesonKernel π).mul_mem_right (star y) hD
  have hlim : Tendsto (fun e ↦ ‖D * star y - D * star y * e‖ + ‖D - D * e‖ * ‖y‖)
      (arvesonUnit π).filter (nhds 0) := by
    have h := ((arvesonUnit π).tendsto_mul_right _ hDs).add
      (((arvesonUnit π).tendsto_mul_right _ hD).mul_const ‖y‖)
    rw [zero_mul, add_zero] at h
    exact h
  filter_upwards [(arvesonUnit π).eventually_isSelfAdjoint,
    hlim.eventually_le_const hδ] with e hesa hsmall
  have h1 : ‖D * star y * e - D * star y‖ = ‖D * star y - D * star y * e‖ :=
    norm_sub_rev _ _
  have h2 : ‖(D * e - D) * star y‖ ≤ ‖D - D * e‖ * ‖y‖ := by
    calc ‖(D * e - D) * star y‖ ≤ ‖D * e - D‖ * ‖star y‖ := norm_mul_le _ _
      _ = ‖D - D * e‖ * ‖y‖ := by rw [norm_star, norm_sub_rev]
  rw [arvesonDefect_mul_star D y e hesa]
  calc ‖(D * star y * e - D * star y) - (D * e - D) * star y‖
      ≤ ‖D * star y * e - D * star y‖ + ‖(D * e - D) * star y‖ := norm_sub_le _ _
    _ ≤ ‖D * star y - D * star y * e‖ + ‖D - D * e‖ * ‖y‖ := by
        rw [h1]
        exact add_le_add le_rfl h2
    _ ≤ δ := hsmall

/-- The defect of a member of the kernel lies in the kernel. -/
theorem arvesonDefect_mem (π : B →⋆ₐ[ℂ] C) (y h : B)
    (hh : h ∈ arvesonKernel π) : h * y - y * h ∈ arvesonKernel π :=
  (arvesonKernel π).sub_mem ((arvesonKernel π).mul_mem_right y hh)
    ((arvesonKernel π).mul_mem_left y hh)

/-- The properties a single selected member must have. -/
theorem arvesonPair_eventually_good [Nontrivial B] (π : B →⋆ₐ[ℂ] C) (X : Finset B)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ e in (arvesonUnit π).filter, e ∈ arvesonKernel π ∧ IsSelfAdjoint e ∧
      ‖1 - e‖ ≤ 1 ∧ ∀ x ∈ X, ‖x - e * x‖ ≤ ‖π x‖ + η :=
  (arvesonUnit π).eventually_mem.and ((arvesonUnit π).eventually_isSelfAdjoint.and
    ((arvesonUnit π).eventually_norm_one_sub.and
      (arvesonPair_eventually_absorb_finset π X hη)))

/-- **Greedy selection.**  For every `N` there is a sequence of good members of
the approximate unit whose defects against every `y ∈ Y` are pairwise almost
orthogonal below index `N`. -/
theorem arvesonPair_exists_selection [Nontrivial B] (π : B →⋆ₐ[ℂ] C)
    (Y X : Finset B) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (N : ℕ) :
    ∃ s : ℕ → B, (∀ i, s i ∈ arvesonKernel π ∧ IsSelfAdjoint (s i) ∧
        ‖1 - s i‖ ≤ 1 ∧ ∀ x ∈ X, ‖x - s i * x‖ ≤ ‖π x‖ + η) ∧
      ∀ i j, i < j → j < N → ∀ y ∈ Y,
        ‖(s i * y - y * s i) * star (s j * y - y * s j)‖ ≤ δ := by
  haveI := (arvesonUnit π).neBot
  induction N with
  | zero =>
    obtain ⟨e, he⟩ := (arvesonPair_eventually_good π X hη).exists
    exact ⟨fun _ ↦ e, fun _ ↦ he, fun _ j _ hj ↦ absurd hj (Nat.not_lt_zero j)⟩
  | succ N ih =>
    obtain ⟨s, hs, hscross⟩ := ih
    have hcross : ∀ᶠ e in (arvesonUnit π).filter, ∀ i ∈ Finset.range N, ∀ y ∈ Y,
        ‖(s i * y - y * s i) * star (e * y - y * e)‖ ≤ δ := by
      rw [Filter.eventually_all_finset]
      intro i _
      rw [Filter.eventually_all_finset]
      intro y _
      exact arvesonPair_eventually_cross π y _
        (arvesonDefect_mem π y (s i) (hs i).1) hδ
    obtain ⟨e, he, hecross⟩ := ((arvesonPair_eventually_good π X hη).and hcross).exists
    refine ⟨fun i ↦ if i < N then s i else e, fun i ↦ ?_, ?_⟩
    · by_cases hi : i < N
      · simp only [if_pos hi]
        exact hs i
      · simp only [if_neg hi]
        exact he
    · intro i j hij hj y hy
      by_cases hjN : j < N
      · have hiN : i < N := lt_trans hij hjN
        simp only [if_pos hiN, if_pos hjN]
        exact hscross i j hij hjN y hy
      · have hiN : i < N := by omega
        simp only [if_pos hiN, if_neg hjN]
        exact hecross i (Finset.mem_range.2 hiN) y hy

end

end TWWSchafhauser
end Full
end GroupApproximation
