import GroupApproximation.KunThom.FixedPointNormalizationComparison
import GroupApproximation.Sofic.Asymptotics

/-!
# Summing the per-block estimates

The last Hamming estimate in Kun--Thom's proof of Theorem 4.1
(arXiv:2608.06222v3) compares a patched bisection `b̂_n` with
`u_n â_n u_n⁻¹`.  `BlockPatching.BlockArrows.card_hammingDisagreement_patch_le_references`
splits the disagreement block by block against reference arrows, and
`BlockPatching.card_disagreement_le_of_reseparation` bounds one block at a
vanishing scale.  This file combines the two.

* `card_hammingDisagreement_patch_le_reseparation`: on every retained block
  supply the reference arrow, the near bound `#disagreement < 2 * s C` from
  the cluster groupoid, the room `2 * s C + ⌊x C⌋₊ + 1 ≤ |C|`, tagged
  expansion at scale `⌊x C⌋₊ + 1` and the combined defect bound.  Then the
  patched permutation differs from the target on at most
  `offDomain + Σ_good x C + Σ_exceptional |C|` points.
* `vanishing_hammingDistance_of_card_le`: a pointwise count by a negligible
  sequence gives vanishing Hamming distance.
-/

namespace GroupApproximation
namespace BlockPatching
namespace BlockArrows

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}
variable {E : BlockEmbedding Y I} (β : BlockArrows E)

/-- **Patched permutation against a target, with re-separated blocks.** -/
theorem card_hammingDisagreement_patch_le_reseparation [Fintype I] [DecidableEq I]
    {L : Type*} [Fintype L] [DecidableEq L]
    (w : Equiv.Perm Y) (good : Finset I)
    (c : ∀ C, FinitePartialBijection (E.model C) (E.model (β.objEquiv C)))
    (hc : ∀ C ∈ good, β.RealizesOn w C (c C))
    (actY : ∀ C, L → Equiv.Perm (E.model C))
    (actZ : ∀ C, L → Equiv.Perm (E.model (β.objEquiv C)))
    (h : ℝ) (x : I → ℝ) (s : I → ℕ)
    (hx : ∀ C ∈ good, 0 ≤ x C)
    (hexp : ∀ C ∈ good, HasTaggedExpansionAtScale (actY C) h (⌊x C⌋₊ + 1))
    (hdefect : ∀ C ∈ good,
      ((((β.arrow C).equivarianceDefect (actY C) (actZ C)).card +
        ((c C).equivarianceDefect (actY C) (actZ C)).card : ℕ) : ℝ) <
          h * ((⌊x C⌋₊ + 1 : ℕ) : ℝ))
    (hnear : ∀ C ∈ good, ((β.arrow C).disagreement (c C)).card < 2 * s C)
    (hroom : ∀ C ∈ good, 2 * s C + (⌊x C⌋₊ + 1) ≤ Fintype.card (E.model C)) :
    ((hammingDisagreement β.patch w).card : ℝ) ≤
      ((Finset.univ \ β.domain).card : ℝ) + ∑ C ∈ good, x C +
        ∑ C ∈ goodᶜ, (Fintype.card (E.model C) : ℝ) := by
  have hcount := β.card_hammingDisagreement_patch_le_references w good c hc
  have hblock : ∀ C ∈ good,
      (((β.arrow C).disagreement (c C)).card : ℝ) ≤ x C := fun C hC ↦
    card_disagreement_le_of_reseparation (actY C) (actZ C) (β.arrow C) (c C)
      (hx C hC) (hexp C hC) (hdefect C hC)
      (by have h1 := hnear C hC; have h2 := hroom C hC; omega)
  have hsum : ∑ C ∈ good, (((β.arrow C).disagreement (c C)).card : ℝ) ≤
      ∑ C ∈ good, x C :=
    Finset.sum_le_sum hblock
  have hcast : ((hammingDisagreement β.patch w).card : ℝ) ≤
      ((Finset.univ \ β.domain).card : ℝ) +
        ∑ C ∈ good, (((β.arrow C).disagreement (c C)).card : ℝ) +
        ∑ C ∈ goodᶜ, (Fintype.card (E.model C) : ℝ) := by
    exact_mod_cast hcount
  linarith

end BlockArrows

/-- **Vanishing Hamming distance from a negligible count.**  If the
disagreement of two permutation sequences is bounded pointwise by a sequence
negligible against the model sizes, their Hamming distance vanishes. -/
theorem vanishing_hammingDistance_of_card_le {Y : ℕ → FiniteModel}
    (p w : ∀ n, Equiv.Perm (Y n)) (e : ℕ → ℝ)
    (hcard : ∀ n, ((hammingDisagreement (p n) (w n)).card : ℝ) ≤ e n)
    (he : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) e) :
    Vanishing fun n ↦ hammingDistance (Y n) (p n) (w n) := by
  refine Vanishing.squeeze (fun n ↦ hammingDistance_nonnegative (Y n) (p n) (w n))
    (fun n ↦ ?_) he
  rw [hammingDistance]
  exact div_le_div_of_nonneg_right (hcard n) (Nat.cast_nonneg _)

end BlockPatching
end GroupApproximation
