import GroupApproximation.Analysis.CStarStandardModule

/-!
# Positive double series in a C⋆-algebra

The amplification `x ↦ x ⊗ 1` of `ExtensionAbsorbAmplifyOp` sends a vector of
`H_J ≅ ⊕ₖ H_J` to the family of columns `(T fₖ)ₖ`, and the new vector is square
summable because a *positive* double family `a (k, i)` is summable as soon as every row
`i ↦ a (k, i)` is summable and the row sums `k ↦ ∑' i, a (k, i)` are summable.

Positive series in a C⋆-algebra are not absolutely convergent, so this is not the
scalar Fubini--Tonelli theorem.  It is proved by the Cauchy criterion: the norm is
monotone on positive elements, so a partial sum over a finite set of pairs is dominated
by a partial sum over a rectangle, and a rectangle sum is a finite sum of row sums.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section AmplifyPos

variable {J : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **A positive double family with summable rows and summable row sums is summable.** -/
theorem summable_prod_of_nonneg {β γ : Type*} {a : β × γ → J} (ha : ∀ p, 0 ≤ a p)
    (h₁ : ∀ b, Summable fun c => a (b, c)) (h₂ : Summable fun b => ∑' c, a (b, c)) :
    Summable a := by
  classical
  rw [summable_iff_vanishing_norm]
  intro ε hε
  obtain ⟨S₀, hS₀⟩ := summable_iff_vanishing_norm.mp h₂ (ε / 2) (half_pos hε)
  have hN : (0 : ℝ) < 2 * ((S₀.card : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ (S₀.card : ℝ) * δ ≤ ε / 2 := by
    refine ⟨ε / (2 * ((S₀.card : ℝ) + 1)), div_pos hε hN, ?_⟩
    rw [← mul_div_assoc, div_le_div_iff₀ hN two_pos]
    nlinarith [hε.le]
  choose R hR using fun b => summable_iff_vanishing_norm.mp (h₁ b) δ hδ
  refine ⟨S₀ ×ˢ S₀.biUnion R, fun t ht => ?_⟩
  -- the pairs of `t` whose first coordinate lies in `S₀`: each row is a tail
  have hsubA : (t.filter fun p => p.1 ∈ S₀)
      ⊆ (S₀ ×ˢ t.image Prod.snd).filter fun p => p.2 ∉ R p.1 := by
    intro p hp
    obtain ⟨hpt, hp1⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hp1, Finset.mem_image_of_mem Prod.snd hpt⟩, fun hp2 => ?_⟩
    exact Finset.disjoint_left.mp ht hpt
      (Finset.mem_product.mpr ⟨hp1, Finset.mem_biUnion.mpr ⟨p.1, hp1, hp2⟩⟩)
  have hA2 : (∑ p ∈ (S₀ ×ˢ t.image Prod.snd).filter (fun p => p.2 ∉ R p.1), a p)
      = ∑ b ∈ S₀, ∑ c ∈ (t.image Prod.snd).filter (fun c => c ∉ R b), a (b, c) := by
    rw [Finset.sum_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun b _ => (Finset.sum_filter _ _).symm
  have hA : ‖∑ p ∈ t.filter (fun p => p.1 ∈ S₀), a p‖ ≤ ε / 2 := by
    refine le_trans (OrderZero.norm_le_norm_of_nonneg_of_le
      (Finset.sum_nonneg fun p _ => ha p)
      (Finset.sum_le_sum_of_subset_of_nonneg hsubA fun p _ _ => ha p)) ?_
    rw [hA2]
    refine le_trans (norm_sum_le _ _) (le_trans ?_ hδε)
    have hrow : ∀ b ∈ S₀,
        ‖∑ c ∈ (t.image Prod.snd).filter (fun c => c ∉ R b), a (b, c)‖ ≤ δ := fun b _ =>
      (hR b _ (Finset.disjoint_left.mpr fun _ hc hcR => (Finset.mem_filter.mp hc).2 hcR)).le
    have h := Finset.sum_le_card_nsmul S₀ _ δ hrow
    rwa [nsmul_eq_mul] at h
  -- the pairs of `t` whose first coordinate avoids `S₀`: dominated by row sums off `S₀`
  have hsubB : (t.filter fun p => p.1 ∉ S₀)
      ⊆ ((t.filter fun p => p.1 ∉ S₀).image Prod.fst) ×ˢ t.image Prod.snd := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst hp,
      Finset.mem_image_of_mem Prod.snd (Finset.mem_filter.mp hp).1⟩
  have hdisjB : Disjoint ((t.filter fun p => p.1 ∉ S₀).image Prod.fst) S₀ := by
    refine Finset.disjoint_left.mpr fun b hb hbS => ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp hp).2 hbS
  have hB : ‖∑ p ∈ t.filter (fun p => p.1 ∉ S₀), a p‖ < ε / 2 := by
    refine lt_of_le_of_lt (OrderZero.norm_le_norm_of_nonneg_of_le
      (Finset.sum_nonneg fun p _ => ha p) ?_) (hS₀ _ hdisjB)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubB fun p _ _ => ha p) ?_
    rw [Finset.sum_product]
    exact Finset.sum_le_sum fun b _ => (h₁ b).sum_le_tsum _ fun c _ => ha (b, c)
  rw [← Finset.sum_filter_add_sum_filter_not t (fun p => p.1 ∈ S₀) a]
  calc _ ≤ _ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hA hB
    _ = ε := add_halves ε

end AmplifyPos

end GroupApproximation.Full.TWWSchafhauser
