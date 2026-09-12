import GroupApproximation.Analysis.PowersAveragingFromPartition
import GroupApproximation.Analysis.PowersAveragingUniqueTrace
import GroupApproximation.Analysis.MaximalGroupCStarTrace

/-!
# Powers' averaging estimate from the Powers property

This module closes component (C) of `Analysis/PowersAveraging` **modulo pure
combinatorics**: the analytic hypothesis `PowersAveragingEstimate G` follows
from the *Powers property* of the group, a statement about partitions and
translates with no analysis in it.

## The Powers property

`PowersProperty G`: for every finite `F ⊆ G` avoiding `1` and every `n > 0`
there are a partition `G = C ⊔ D` and elements `g₁, …, gₙ` with

* `f C ∩ C = ∅` for every `f ∈ F`, and
* the translates `gᵢ D` pairwise disjoint.

This is Powers' condition verbatim.  It is what a free group of rank at least
two satisfies, by counting reduced words, and it is the only thing still missing
from a proof of Powers' theorem in this repository.

## The chain

1. `Analysis/GroupHilbertSubsetProjection` builds the coordinate projections
   `P_S` of `ℓ²(G)` and proves `λ(g) P_S λ(g)⋆ = P_{gS}`.
2. `Analysis/OrthogonalProjectionSumEstimate` gives `‖∑ᵢ Aᵢ Qᵢ‖ ≤ √n max ‖Aᵢ‖`
   for pairwise orthogonal `Qᵢ`.
3. `Analysis/PowersAveragingFromPartition` combines them:
   `P_C a P_C = 0` and disjoint translates give `‖avg(a)‖ ≤ 2‖a‖/√n`.
4. Here: `f C ∩ C = ∅` on the support of a finite combination of translations
   gives `P_C a P_C = 0`, the density of those combinations
   (`exists_translationSum_approx`) carries the estimate to every element, and
   averaging is a contraction, which is what lets the approximation through.

The identity coefficient is what the trace hypothesis is for.  An approximant
`b = ∑ᵢ cᵢ λ(γᵢ)` need not be supported off `1`; zeroing the coefficients at
`γᵢ = 1` leaves `b₀` with `b = b₀ + κ·1`, the canonical trace of `b₀` vanishes,
so `κ = τ(b)`, and `|τ(b)| = |τ(b - a)| ≤ ‖b - a‖` is small because `τ(a) = 0`.
Deleting the identity term therefore costs nothing.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace ReducedGroupCStarTrace

open GroupApproximation.GroupVonNeumann
open scoped Pointwise

universe u

noncomputable section

variable (G : Type u) [Group G]

/-! ## The Powers property -/

/-- **Powers' property.**  For every finite `F ⊆ G \ {1}` and every `n > 0`
there are a partition `G = C ⊔ D` with `f C ∩ C = ∅` for all `f ∈ F`, and
`n` elements whose translates of `D` are pairwise disjoint. -/
def PowersProperty : Prop :=
  ∀ F : Finset G, (1 : G) ∉ F → ∀ n : ℕ, 0 < n →
    ∃ (C D : Set G) (g : Fin n → G),
      Disjoint C D ∧ C ∪ D = Set.univ ∧
        (∀ f ∈ F, Disjoint (f • C) C) ∧
          (∀ i j, i ≠ j → Disjoint (g i • D) (g j • D))

/-! ## Elementary facts about the reduced algebra -/

/-- The inclusion of the reduced algebra into `B(ℓ²G)`. -/
def reducedInclusion :
    ReducedGroupCStar G →⋆ₐ[ℂ] (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  (reducedGroupCStarSubalgebra G).subtype

theorem reducedInclusion_apply (x : ReducedGroupCStar G) :
    reducedInclusion G x = (x : GroupHilbert G →L[ℂ] GroupHilbert G) := rfl

theorem norm_reducedLeftRegular_le_one (g : G) :
    ‖reducedLeftRegular G g‖ ≤ 1 := by
  have h : ‖(reducedLeftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G)‖ ≤ 1 :=
    norm_leftRegularOperator_le_one G g
  rwa [norm_coe_reducedGroupCStar] at h

theorem norm_one_le_one : ‖(1 : ReducedGroupCStar G)‖ ≤ 1 := by
  have h : ‖star (1 : ReducedGroupCStar G) * 1‖
      = ‖(1 : ReducedGroupCStar G)‖ * ‖(1 : ReducedGroupCStar G)‖ :=
    CStarRing.norm_star_mul_self
  rw [star_one, one_mul] at h
  nlinarith [norm_nonneg (1 : ReducedGroupCStar G)]

/-! ## Averaging is a contraction -/

theorem norm_conj_reducedLeftRegular_le (x : ReducedGroupCStar G) (g : G) :
    ‖reducedLeftRegular G g * x * star (reducedLeftRegular G g)‖ ≤ ‖x‖ := by
  have h1 : ‖reducedLeftRegular G g * x * star (reducedLeftRegular G g)‖
      ≤ ‖reducedLeftRegular G g * x‖ * ‖star (reducedLeftRegular G g)‖ :=
    norm_mul_le _ _
  have h2 : ‖reducedLeftRegular G g * x‖ ≤ ‖reducedLeftRegular G g‖ * ‖x‖ :=
    norm_mul_le _ _
  have h3 : ‖star (reducedLeftRegular G g)‖ ≤ 1 := by
    rw [norm_star]
    exact norm_reducedLeftRegular_le_one G g
  nlinarith [norm_nonneg x, norm_nonneg (reducedLeftRegular G g),
    norm_nonneg (reducedLeftRegular G g * x),
    norm_reducedLeftRegular_le_one G g, h1, h2, h3]

/-- **Averaging does not increase the norm.** -/
theorem norm_reducedAverage_le (x : ReducedGroupCStar G) {n : ℕ} (hn : 0 < n)
    (g : Fin n → G) :
    ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * x * star (reducedLeftRegular G (g i))‖
      ≤ ‖x‖ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsum : ‖∑ i : Fin n,
      reducedLeftRegular G (g i) * x * star (reducedLeftRegular G (g i))‖
      ≤ (n : ℝ) * ‖x‖ := by
    calc ‖∑ i : Fin n,
        reducedLeftRegular G (g i) * x * star (reducedLeftRegular G (g i))‖
        ≤ ∑ i : Fin n,
            ‖reducedLeftRegular G (g i) * x * star (reducedLeftRegular G (g i))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, ‖x‖ :=
          Finset.sum_le_sum fun i _ ↦ norm_conj_reducedLeftRegular_le G x (g i)
      _ = (n : ℝ) * ‖x‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc (n : ℝ)⁻¹ * ‖∑ i : Fin n,
        reducedLeftRegular G (g i) * x * star (reducedLeftRegular G (g i))‖
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ‖x‖) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hnpos))
    _ = ‖x‖ := by field_simp

/-! ## The canonical trace of a translation -/

/-- `τ(λ(g)) = 1` if `g = 1` and `0` otherwise. -/
theorem canonicalCoefficientAtOne_reducedLeftRegular (g : G) :
    canonicalCoefficientAtOne G (reducedLeftRegular G g)
      = if g = 1 then 1 else 0 := by
  classical
  by_cases hg : g = 1
  · rw [if_pos hg, hg, reducedLeftRegular_one]
    exact (canonicalFaithfulTracialState G).map_one
  · rw [if_neg hg, canonicalCoefficientAtOne_reducedLeftRegular_of_ne_one G hg]

/-! ## The projection hypothesis from the combinatorics -/

/-- **`f C ∩ C = ∅` on the support gives `P_C a P_C = 0`.**

A vanishing coefficient is allowed in place of the disjointness, which is what
lets the identity term of an approximant be zeroed rather than excluded. -/
theorem subsetProjection_conj_translationSum_eq_zero {C : Set G} {m : ℕ}
    (c : Fin m → ℂ) (γ : Fin m → G)
    (h : ∀ i, c i = 0 ∨ Disjoint (γ i • C) C) :
    subsetProjection G C *
        (∑ i : Fin m, c i • leftRegularOperator G (γ i)) *
        subsetProjection G C = 0 := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rcases h i with hc | hd
  · rw [hc, zero_smul, mul_zero, zero_mul]
  · rw [mul_smul_comm, smul_mul_assoc,
      subsetProjection_conj_eq_zero_of_disjoint G hd, smul_zero]

/-- The coercion of a finite combination of reduced translations. -/
theorem coe_translationSum {m : ℕ} (c : Fin m → ℂ) (γ : Fin m → G) :
    ((∑ i : Fin m, c i • reducedLeftRegular G (γ i) : ReducedGroupCStar G) :
        GroupHilbert G →L[ℂ] GroupHilbert G)
      = ∑ i : Fin m, c i • leftRegularOperator G (γ i) := by
  have h := map_sum (reducedInclusion G)
    (fun i ↦ c i • reducedLeftRegular G (γ i)) Finset.univ
  rw [reducedInclusion_apply] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [map_smul, reducedInclusion_apply]

/-! ## The estimate -/

set_option maxHeartbeats 1000000 in
/-- **Powers' averaging estimate follows from the Powers property.**

This is component (C) of `Analysis/PowersAveraging`, reduced to combinatorics.
Everything analytic is discharged. -/
theorem powersAveragingEstimate_of_powersProperty (h : PowersProperty G) :
    PowersAveragingEstimate G := by
  classical
  intro a hτa ε hε
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  have hδne : δ ≠ 0 := ne_of_gt hδ
  -- Approximate `a` by a finite combination of translations.
  obtain ⟨m, c, γ, happrox⟩ := exists_translationSum_approx G a.2 hδ
  set b : ReducedGroupCStar G := ∑ i : Fin m, c i • reducedLeftRegular G (γ i) with hbdef
  have hbcoe : (b : GroupHilbert G →L[ℂ] GroupHilbert G)
      = ∑ i : Fin m, c i • leftRegularOperator G (γ i) := by
    rw [hbdef]
    exact coe_translationSum G c γ
  have hab : ‖a - b‖ < δ := by
    have hsub : ((a - b : ReducedGroupCStar G) :
        GroupHilbert G →L[ℂ] GroupHilbert G)
        = (a : GroupHilbert G →L[ℂ] GroupHilbert G)
          - ∑ i : Fin m, c i • leftRegularOperator G (γ i) := by
      have hmap := map_sub (reducedInclusion G) a b
      rw [reducedInclusion_apply, reducedInclusion_apply, reducedInclusion_apply,
        hbcoe] at hmap
      exact hmap
    have hnorm := happrox
    rw [← hsub, norm_coe_reducedGroupCStar] at hnorm
    exact hnorm
  -- Zero the coefficients at the identity.
  set c' : Fin m → ℂ := fun i ↦ if γ i = 1 then 0 else c i with hc'
  set b₀ : ReducedGroupCStar G := ∑ i : Fin m, c' i • reducedLeftRegular G (γ i)
    with hb₀
  set κ : ℂ := ∑ i : Fin m, (if γ i = 1 then c i else 0) with hκdef
  have hsplit : b = b₀ + κ • 1 := by
    rw [hbdef, hb₀, hκdef, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hγ : γ i = 1
    · rw [hc']
      simp [hγ]
    · simp [hc', hγ]
  -- The identity coefficient is the trace of `b`, hence small.
  have hτb₀ : canonicalFaithfulTracialState G b₀ = 0 := by
    have hlin : canonicalCoefficientAtOne G b₀
        = ∑ i : Fin m, c' i * canonicalCoefficientAtOne G (reducedLeftRegular G (γ i)) := by
      rw [hb₀, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
    show canonicalCoefficientAtOne G b₀ = 0
    rw [hlin]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [canonicalCoefficientAtOne_reducedLeftRegular]
    by_cases hγ : γ i = 1
    · rw [hc']
      simp [hγ]
    · simp [hγ]
  have hτb : canonicalFaithfulTracialState G b = κ := by
    have hlin : canonicalCoefficientAtOne G b
        = ∑ i : Fin m, c i * canonicalCoefficientAtOne G (reducedLeftRegular G (γ i)) := by
      rw [hbdef, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
    show canonicalCoefficientAtOne G b = κ
    rw [hlin, hκdef]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [canonicalCoefficientAtOne_reducedLeftRegular]
    by_cases hγ : γ i = 1 <;> simp [hγ]
  have hκsmall : ‖κ‖ < δ := by
    have hbound : ‖canonicalFaithfulTracialState G (b - a)‖ ≤ ‖b - a‖ :=
      Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le
        (canonicalFaithfulTracialState G).toTracialState (b - a)
    have heq : canonicalFaithfulTracialState G (b - a) = κ := by
      rw [FaithfulTracialState.map_sub, hτa, hτb, sub_zero]
    rw [heq] at hbound
    calc ‖κ‖ ≤ ‖b - a‖ := hbound
      _ = ‖a - b‖ := by rw [← norm_neg, neg_sub]
      _ < δ := hab
  have hab₀ : ‖a - b₀‖ < 2 * δ := by
    have hdecomp : a - b₀ = (a - b) + κ • (1 : ReducedGroupCStar G) := by
      rw [hsplit]; abel
    have hsmul : ‖κ • (1 : ReducedGroupCStar G)‖ ≤ ‖κ‖ := by
      rw [norm_smul]
      nlinarith [norm_nonneg κ, norm_one_le_one G,
        norm_nonneg (1 : ReducedGroupCStar G)]
    calc ‖a - b₀‖ = ‖(a - b) + κ • (1 : ReducedGroupCStar G)‖ := by rw [hdecomp]
      _ ≤ ‖a - b‖ + ‖κ • (1 : ReducedGroupCStar G)‖ := norm_add_le _ _
      _ < δ + δ :=
          add_lt_add_of_lt_of_le hab (le_of_lt (lt_of_le_of_lt hsmul hκsmall))
      _ = 2 * δ := by ring
  -- Choose the number of averaging elements.
  set M : ℝ := 2 * ‖b₀‖ / δ with hM
  have hM0 : 0 ≤ M := by positivity
  set n : ℕ := ⌈M ^ 2⌉₊ + 1 with hn
  have hnpos : 0 < n := Nat.succ_pos _
  have hnM : M ^ 2 ≤ (n : ℝ) := by
    have h1 : M ^ 2 ≤ ((⌈M ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈M ^ 2⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [hn]
      exact_mod_cast Nat.le_succ _
    linarith
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
  have hMsqrt : M ≤ Real.sqrt n := by
    have hs := Real.sqrt_le_sqrt hnM
    rwa [Real.sqrt_sq hM0] at hs
  have hMd : 2 * ‖b₀‖ = M * δ := by
    rw [hM]; field_simp
  have hgain : 2 * ‖b₀‖ / Real.sqrt n ≤ δ := by
    rw [div_le_iff₀ hsqrtpos, hMd, mul_comm δ (Real.sqrt n)]
    exact mul_le_mul_of_nonneg_right hMsqrt hδ.le
  -- The Powers property, at the support of `b₀`.
  set F : Finset G := (Finset.univ.image γ).erase 1 with hF
  have hFne : (1 : G) ∉ F := by
    rw [hF]
    exact Finset.notMem_erase 1 _
  obtain ⟨C, D, g, hdisj, hunion, hFC, hgD⟩ := h F hFne n hnpos
  -- The projection hypothesis.
  have hPaP : subsetProjection G C *
      (b₀ : GroupHilbert G →L[ℂ] GroupHilbert G) * subsetProjection G C = 0 := by
    have hcoe : (b₀ : GroupHilbert G →L[ℂ] GroupHilbert G)
        = ∑ i : Fin m, c' i • leftRegularOperator G (γ i) := by
      rw [hb₀]
      exact coe_translationSum G c' γ
    rw [hcoe]
    refine subsetProjection_conj_translationSum_eq_zero G c' γ fun i ↦ ?_
    by_cases hγ : γ i = 1
    · left
      rw [hc']
      simp [hγ]
    · right
      refine hFC (γ i) ?_
      rw [hF, Finset.mem_erase]
      exact ⟨hγ, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  -- The estimate on `b₀`, and the contraction on the difference.
  have hb₀est : ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
      reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i))‖ ≤ δ :=
    le_trans (norm_reducedAverage_le_of_partition G b₀ hdisj hunion hPaP hnpos g hgD)
      hgain
  have hdiff : ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)))
      - ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i)))
      = (n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * (a - b₀) * star (reducedLeftRegular G (g i)) := by
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_sub, sub_mul]
  have hdiffbound : ‖((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)))
      - ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i)))‖
      ≤ ‖a - b₀‖ := by
    rw [hdiff]
    exact norm_reducedAverage_le G (a - b₀) hnpos g
  refine ⟨n, g, hnpos, ?_⟩
  set X : ReducedGroupCStar G := (n : ℂ)⁻¹ • ∑ i : Fin n,
    reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)) with hX
  set Y : ReducedGroupCStar G := (n : ℂ)⁻¹ • ∑ i : Fin n,
    reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i)) with hY
  have hXY : (X - Y) + Y = X := by abel
  calc ‖X‖ = ‖(X - Y) + Y‖ := by rw [hXY]
    _ ≤ ‖X - Y‖ + ‖Y‖ := norm_add_le _ _
    _ ≤ ‖a - b₀‖ + δ := add_le_add hdiffbound hb₀est
    _ ≤ 2 * δ + δ := by linarith [hab₀.le]
    _ ≤ ε := by rw [hδdef]; linarith

end

end ReducedGroupCStarTrace
end GroupApproximation

open GroupApproximation.ReducedGroupCStarTrace

#audit_axioms norm_reducedAverage_le
#audit_axioms canonicalCoefficientAtOne_reducedLeftRegular
#audit_axioms subsetProjection_conj_translationSum_eq_zero
#audit_axioms coe_translationSum
#audit_axioms powersAveragingEstimate_of_powersProperty
