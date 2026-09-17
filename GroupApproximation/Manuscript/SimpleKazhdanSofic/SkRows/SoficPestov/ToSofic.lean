import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SoficPestov.Definition

/-!
# Pestov's normalization gives corpus soficity

The converse of `FromSofic`, from the weakest printed form (multiplicativity only when `g, h, gh`
lie in the test set).

Route.  Given a finite `F` and `ε > 0`, test Pestov's condition on
`T = F ∪ F⁻¹ ∪ F⁻¹F ∪ FF` at tolerance `δ = min 1 (ε / 3)`.
* Every pair of `F` has its product in `T`, so the corpus defect is `< δ ≤ ε`.
* For `g ≠ h` in `F`, `h⁻¹g ≠ 1` is at distance `> 1 - δ` from `1`, while
  `d(φ(h⁻¹g), φ(h⁻¹)φ(g)) < δ` and `d(φ(h⁻¹)φ(h), 1) < δ` (products `h⁻¹g, h⁻¹h ∈ T`, `φ 1 = 1`).
  Left invariance `d(φ(h⁻¹)φ(g), φ(h⁻¹)φ(h)) = d(φ g, φ h)` and two triangle inequalities give
  `d(φ g, φ h) > 1 - 3δ ≥ 1 - ε`.
* The model is nonempty: if `n = 0` every distance is `0`, contradicting separation `> 1 - δ ≥ 0`
  of a nontrivial element.  If `F ⊆ {1}` the one-point model works.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace SoficPestov

/-- **Pestov's (product-restricted) normalization implies corpus soficity.** -/
theorem isSofic_of_isSoficPestovRestricted {G : Type*} [Group G]
    (hG : IsSoficPestovRestricted G) : IsSofic G := by
  classical
  intro F ε hε
  by_cases hF : ∃ g ∈ F, g ≠ 1
  · obtain ⟨g₀, hg₀, hg₀1⟩ := hF
    obtain ⟨T, hFT, hinvT, hdivT, hprodT⟩ : ∃ T : Finset G, (∀ g ∈ F, g ∈ T) ∧
        (∀ g ∈ F, g⁻¹ ∈ T) ∧ (∀ g ∈ F, ∀ h ∈ F, h⁻¹ * g ∈ T) ∧
        ∀ g ∈ F, ∀ h ∈ F, g * h ∈ T := by
      refine ⟨F ∪ F.image (fun g => g⁻¹) ∪ (F ×ˢ F).image (fun p : G × G => p.1⁻¹ * p.2) ∪
        (F ×ˢ F).image (fun p : G × G => p.1 * p.2), ?_, ?_, ?_, ?_⟩
      · intro g hg
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hg))
      · intro g hg
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩)))
      · intro g hg h hh
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(h, g), Finset.mem_product.mpr ⟨hh, hg⟩, rfl⟩))
      · intro g hg h hh
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩)
    have hδpos : 0 < min 1 (ε / 3) := lt_min one_pos (by linarith)
    have hδ1 : min 1 (ε / 3) ≤ 1 := min_le_left _ _
    have hδ3 : min 1 (ε / 3) ≤ ε / 3 := min_le_right _ _
    obtain ⟨n, φ, hmul, hφ1, hsep⟩ := hG T (min 1 (ε / 3)) hδpos
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso
        have hs := hsep g₀ (hFT g₀ hg₀) hg₀1
        subst h0
        simp only [pestovHammingDist, Nat.cast_zero, div_zero] at hs
        linarith
      · exact h0
    refine ⟨{
      carrier := finModel n
      nonempty := by rw [card_finModel]; exact hn
      map := φ
      multiplicative := ?_
      separated := ?_ }⟩
    · intro g hg h hh
      have hm := hmul g (hFT g hg) h (hFT h hh) (hprodT g hg h hh)
      have hle : pestovHammingDist (φ (g * h)) (φ g * φ h) ≤ ε := by linarith
      exact (pestovHammingDist_eq_hammingDistance (φ (g * h)) (φ g * φ h)).symm.trans_le hle
    · intro g hg h hh hgh
      have hne : h⁻¹ * g ≠ 1 := fun heq => hgh (inv_mul_eq_one.mp heq).symm
      have m1 := hmul h⁻¹ (hinvT h hh) g (hFT g hg) (hdivT g hg h hh)
      have m2 := hmul h⁻¹ (hinvT h hh) h (hFT h hh) (hdivT h hh h hh)
      rw [inv_mul_cancel, hφ1, pestovHammingDist_comm] at m2
      have s1 := hsep (h⁻¹ * g) (hdivT g hg h hh) hne
      have t1 := pestovHammingDist_triangle (φ (h⁻¹ * g)) (φ h⁻¹ * φ g) 1
      have t2 := pestovHammingDist_triangle (φ h⁻¹ * φ g) (φ h⁻¹ * φ h) 1
      have c1 := pestovHammingDist_left_invariant (φ h⁻¹) (φ g) (φ h)
      have key : 1 - ε ≤ pestovHammingDist (φ g) (φ h) := by linarith
      exact key.trans_eq (pestovHammingDist_eq_hammingDistance (φ g) (φ h))
  · have hF' : ∀ g ∈ F, g = 1 := fun g hg => by
      by_contra hne
      exact hF ⟨g, hg, hne⟩
    refine ⟨{
      carrier := finModel 1
      nonempty := by rw [card_finModel]; exact Nat.one_pos
      map := fun _ => 1
      multiplicative := ?_
      separated := ?_ }⟩
    · intro g _ h _
      show hammingDistance (finModel 1) 1 (1 * 1) ≤ ε
      rw [mul_one, hammingDistance_self]
      exact hε.le
    · intro g hg h hh hgh
      exact absurd ((hF' g hg).trans (hF' h hh).symm) hgh

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.isSofic_of_isSoficPestovRestricted

end SoficPestov
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
