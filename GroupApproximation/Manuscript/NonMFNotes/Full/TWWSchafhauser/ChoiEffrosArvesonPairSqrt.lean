import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosArvesonPairMazur
import GroupApproximation.Analysis.VoiculescuSqrtCommutator
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Arveson pairs, step 3: the square-root calculus

Lane TWWSchafhauser-3a1, work order WO-TWWSchafhauser-3a-1.  This file proves
`exists_arvesonPair`.  Take the quasicentral average `h ∈ ker π` of
`ChoiEffrosArvesonPairMazur` and put

`f = 1 - h`,  `g = √(1 - f²)`.

Then `f` is a self-adjoint contraction with `π f = 1`, so `0 ≤ f² ≤ 1` and
`g` is defined.  By construction `f² + g² = 1`, and `π g` is self-adjoint with
square `0`, so it is `0`.  Commutators with `y ∈ Y` pass from `h` to `f` with
the same norm, from `f` to `1 - f²` at twice the norm, and from `1 - f²` to its
square root through a uniform modulus.  Finally `‖f² x‖ ≤ ‖f x‖ = ‖x - h x‖`,
which is the absorption bound.

The order on `B` is `CStarAlgebra.spectralOrder`, registered locally, since a
general C⋆-algebra carries no order instance.  `arvesonPair_sqrt_modulus`
comes from `ShulmanFill.tendsto_norm_commutator_sqrt` by contradiction, the
same argument as in `VoiculescuSqrtModulus`, run in a general C⋆-algebra.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open Filter PolarLiftingGeneralCStar

noncomputable section

universe v w

/-- **The uniform square-root modulus** in a C⋆-algebra.  Among elements of
norm at most `M`, a small enough commutator with a positive `a` forces a small
commutator with `√a`. -/
theorem arvesonPair_sqrt_modulus {B : Type v} [CStarAlgebra B] [Nontrivial B]
    [PartialOrder B] [StarOrderedRing B] (M ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : B, 0 ≤ a → ‖a‖ ≤ M → ‖b‖ ≤ M →
      ‖a * b - b * a‖ < δ → ‖CFC.sqrt a * b - b * CFC.sqrt a‖ < ε := by
  by_contra hcon
  push Not at hcon
  choose A Bs hA0 hAM hBM hcomm hbad using fun n : ℕ ↦
    hcon (1 / ((n : ℝ) + 1)) (by positivity)
  let a : BoundedCStarSequence (fun _ : ℕ ↦ B) :=
    ⟨A, memℓp_infty ⟨M, by rintro _ ⟨n, rfl⟩; exact hAM n⟩⟩
  let b : BoundedCStarSequence (fun _ : ℕ ↦ B) :=
    ⟨Bs, memℓp_infty ⟨M, by rintro _ ⟨n, rfl⟩; exact hBM n⟩⟩
  have hcoeA : ∀ n, a n = A n := fun _ ↦ rfl
  have hcoeB : ∀ n, b n = Bs n := fun _ ↦ rfl
  have hnull : Tendsto (fun n ↦ ‖a n * b n - b n * a n‖) atTop (nhds 0) := by
    simp only [hcoeA, hcoeB]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hcomm n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hsq := ShulmanFill.tendsto_norm_commutator_sqrt (fun _ : ℕ ↦ B) atTop a b
    (fun n ↦ by rw [hcoeA]; exact hA0 n) hnull
  simp only [hcoeA, hcoeB] at hsq
  exact absurd (ge_of_tendsto' hsq hbad) (not_le.mpr hε)

/-- **Arveson pairs** (Arveson 1977, §1; Davidson I.9.16).  For a unital
⋆-homomorphism `π` of C⋆-algebras and finite sets `Y`, `X`, there are
self-adjoint contractions `f`, `g` with `f² + g² = 1`, `π f = 1`, `π g = 0`,
almost commuting with `Y` and with `‖f² x‖ ≤ ‖π x‖ + ε` on `X`. -/
theorem exists_arvesonPair {B : Type v} {C : Type w} [CStarAlgebra B] [CStarAlgebra C]
    (π : B →⋆ₐ[ℂ] C) (Y X : Finset B) (ε : ℝ) (hε : 0 < ε) :
    ∃ f g : B, IsSelfAdjoint f ∧ IsSelfAdjoint g ∧ ‖f‖ ≤ 1 ∧ ‖g‖ ≤ 1 ∧
      f * f + g * g = 1 ∧ π f = 1 ∧ π g = 0 ∧
      (∀ y ∈ Y, ‖f * y - y * f‖ ≤ ε ∧ ‖g * y - y * g‖ ≤ ε) ∧
      ∀ x ∈ X, ‖f * f * x‖ ≤ ‖π x‖ + ε := by
  rcases subsingleton_or_nontrivial B with hsub | hnt
  · haveI := hsub
    refine ⟨0, 0, IsSelfAdjoint.zero B, IsSelfAdjoint.zero B, ?_, ?_,
      Subsingleton.elim _ _, ?_, map_zero π, ?_, ?_⟩
    · rw [norm_zero]
      exact zero_le_one
    · rw [norm_zero]
      exact zero_le_one
    · rw [Subsingleton.elim (0 : B) 1, map_one]
    · intro y _
      rw [Subsingleton.elim ((0 : B) * y - y * 0) 0, norm_zero]
      exact ⟨hε.le, hε.le⟩
    · intro x _
      rw [Subsingleton.elim ((0 : B) * 0 * x) 0, norm_zero]
      linarith [norm_nonneg (π x)]
  · haveI := hnt
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ z ∈ Y, ‖z‖ := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := by
      rw [hSdef]
      exact Finset.sum_nonneg fun z _ ↦ norm_nonneg z
    obtain ⟨δ₀, hδ₀, hmod⟩ := arvesonPair_sqrt_modulus (B := B) (S + 2) ε hε
    obtain ⟨δ, hδ, hδε, hδδ₀⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 4 * δ ≤ δ₀ :=
      ⟨min ε (δ₀ / 4), lt_min hε (div_pos hδ₀ (by norm_num)), min_le_left _ _,
        by linarith [min_le_right ε (δ₀ / 4)]⟩
    obtain ⟨h, hmem, hsa, hone, hcomm, habs⟩ := arvesonPair_exists_average π Y X hδ hε
    -- `f = 1 - h`
    obtain ⟨f, hfdef⟩ : ∃ f : B, f = 1 - h := ⟨_, rfl⟩
    have hfsa : IsSelfAdjoint f := by
      rw [hfdef]
      exact (IsSelfAdjoint.one B).sub hsa
    have hfn : ‖f‖ ≤ 1 := by
      rw [hfdef]
      exact hone
    have hff0 : 0 ≤ f * f := by
      have h0 := star_mul_self_nonneg f
      rw [hfsa.star_eq] at h0
      exact h0
    have hffn : ‖f * f‖ ≤ 1 :=
      (norm_mul_le _ _).trans (mul_le_one₀ hfn (norm_nonneg _) hfn)
    have hff1 : f * f ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg (f * f) hff0).1 hffn
    -- `a = 1 - f²` and `g = √a`
    obtain ⟨a, hadef⟩ : ∃ a : B, a = 1 - f * f := ⟨_, rfl⟩
    have ha0 : 0 ≤ a := by
      rw [hadef]
      exact sub_nonneg.2 hff1
    have han : ‖a‖ ≤ 1 := by
      refine (CStarAlgebra.norm_le_one_iff_of_nonneg a ha0).2 ?_
      rw [hadef]
      exact sub_le_self 1 hff0
    obtain ⟨g, hgdef⟩ : ∃ g : B, g = CFC.sqrt a := ⟨_, rfl⟩
    have hgg : g * g = a := by
      rw [hgdef]
      exact CFC.sqrt_mul_sqrt_self a ha0
    have hg0 : 0 ≤ g := by
      rw [hgdef]
      exact CFC.sqrt_nonneg a
    have hgsa : IsSelfAdjoint g := IsSelfAdjoint.of_nonneg hg0
    have hsum : f * f + g * g = 1 := by
      rw [hgg, hadef]
      abel
    have hgn : ‖g‖ ≤ 1 := by
      have h1 : ‖g‖ * ‖g‖ ≤ 1 := by
        rw [← CStarRing.norm_star_mul_self, hgsa.star_eq, hgg]
        exact han
      nlinarith [norm_nonneg g]
    -- the images under `π`
    have hπf : π f = 1 := by
      rw [hfdef, map_sub, map_one, (mem_arvesonKernel_iff π h).1 hmem, sub_zero]
    have hπg : π g = 0 := by
      have hsq : π g * π g = 0 := by
        rw [← map_mul π g g, hgg, hadef, map_sub, map_one, map_mul, hπf, mul_one, sub_self]
      have hgsa' : IsSelfAdjoint (π g) := hgsa.map π
      have hn : ‖π g‖ * ‖π g‖ = 0 := by
        rw [← CStarRing.norm_star_mul_self, hgsa'.star_eq, hsq, norm_zero]
      exact norm_eq_zero.1 (mul_self_eq_zero.1 hn)
    -- commutators
    have hfcomm : ∀ y ∈ Y, ‖f * y - y * f‖ ≤ δ := by
      intro y hy
      have hexp : f * y - y * f = -(h * y - y * h) := by
        rw [hfdef]
        simp only [sub_mul, mul_sub, one_mul, mul_one]
        abel
      rw [hexp, norm_neg]
      exact hcomm y hy
    have hacomm : ∀ y ∈ Y, ‖a * y - y * a‖ < δ₀ := by
      intro y hy
      have hexp : a * y - y * a = -(f * (f * y - y * f) + (f * y - y * f) * f) := by
        rw [hadef]
        simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
        abel
      have hfy := hfcomm y hy
      rw [hexp, norm_neg]
      calc ‖f * (f * y - y * f) + (f * y - y * f) * f‖
          ≤ ‖f * (f * y - y * f)‖ + ‖(f * y - y * f) * f‖ := norm_add_le _ _
        _ ≤ ‖f‖ * ‖f * y - y * f‖ + ‖f * y - y * f‖ * ‖f‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 1 * δ + δ * 1 :=
            add_le_add (mul_le_mul hfn hfy (norm_nonneg _) zero_le_one)
              (mul_le_mul hfy hfn (norm_nonneg _) hδ.le)
        _ < δ₀ := by linarith
    have hgcomm : ∀ y ∈ Y, ‖g * y - y * g‖ ≤ ε := by
      intro y hy
      have hyS : ‖y‖ ≤ S := by
        rw [hSdef]
        exact Finset.single_le_sum (fun z _ ↦ norm_nonneg z) hy
      rw [hgdef]
      exact (hmod a y ha0 (by linarith) (by linarith) (hacomm y hy)).le
    -- absorption
    have hfx : ∀ x ∈ X, ‖f * f * x‖ ≤ ‖π x‖ + ε := by
      intro x hx
      have hex : f * x = x - h * x := by
        rw [hfdef, sub_mul, one_mul]
      calc ‖f * f * x‖ = ‖f * (f * x)‖ := by rw [mul_assoc]
        _ ≤ ‖f‖ * ‖f * x‖ := norm_mul_le _ _
        _ ≤ ‖f * x‖ := mul_le_of_le_one_left (norm_nonneg _) hfn
        _ = ‖x - h * x‖ := by rw [hex]
        _ ≤ ‖π x‖ + ε := habs x hx
    exact ⟨f, g, hfsa, hgsa, hfn, hgn, hsum, hπf, hπg,
      fun y hy ↦ ⟨(hfcomm y hy).trans hδε, hgcomm y hy⟩, hfx⟩

end

end TWWSchafhauser
end Full
end GroupApproximation
