import GroupApproximation.KunThom.FixedPointNormalizationPatching
import GroupApproximation.Matching.PartialEquivarianceBoundary
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Comparing a patched permutation with a target permutation

`BlockPatching.BlockArrows.card_hammingDisagreement_patch_le` bounds the
disagreement of a patched permutation with a permutation `w` by the mass off
the glued domain and the glued points at which the arrows disagree with `w`.
This file splits the second term block by block, and compares each arrow with
a reference arrow that realizes `w` on its source.

`card_hammingDisagreement_patch_le_references` is the finite form of the last
Hamming estimate in Kun--Thom, arXiv:2608.06222v3, proof of Theorem 4.1.
There `w = u_n â_n u_n⁻¹`, and on a retained block the reference arrow is the
overlap transport of the conjugated arrow of `â_n`, which realizes `w` exactly
on its source.  The patched permutation then differs from `w` by at most:
* the mass off the glued domain;
* the disagreement of each retained arrow with its reference, bounded
  through `FinitePartialBijection.twoSidedDisagreement`;
* the full size of every exceptional block.
-/

namespace GroupApproximation
namespace BlockPatching
namespace BlockArrows

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}
variable {E : BlockEmbedding Y I} (β : BlockArrows E)

/-- Points of block `C` in the source of its arrow at which the arrow
disagrees with `w`. -/
noncomputable def blockArrowDisagreement (w : Equiv.Perm Y) (C : I) :
    Finset (E.model C) := by
  classical
  exact Finset.univ.filter fun x ↦ ∃ hx : x ∈ (β.arrow C).source,
    E.embed (β.objEquiv C) ((β.arrow C).apply x hx) ≠ w (E.embed C x)

theorem mem_blockArrowDisagreement {w : Equiv.Perm Y} {C : I} {x : E.model C} :
    x ∈ β.blockArrowDisagreement w C ↔ ∃ hx : x ∈ (β.arrow C).source,
      E.embed (β.objEquiv C) ((β.arrow C).apply x hx) ≠ w (E.embed C x) := by
  classical
  simp [blockArrowDisagreement]

/-- The glued disagreement with `w`, split block by block. -/
theorem card_arrowDisagreement_le_sum [Fintype I] (w : Equiv.Perm Y) :
    (β.arrowDisagreement w).card ≤ ∑ C, (β.blockArrowDisagreement w C).card := by
  classical
  have hsigma : (Finset.univ.sigma fun C ↦ β.blockArrowDisagreement w C).card =
      ∑ C, (β.blockArrowDisagreement w C).card :=
    Finset.card_sigma _ _
  rw [← hsigma]
  refine Finset.card_le_card_of_injOn
    (fun d : β.Dom ↦ (⟨d.1, d.2.1⟩ : Σ C, E.model C)) ?_ ?_
  · rintro ⟨C, x, hx⟩ hd
    have hd' := β.mem_arrowDisagreement.mp (Finset.mem_coe.mp hd)
    refine Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩)
    exact β.mem_blockArrowDisagreement.mpr ⟨hx, hd'⟩
  · rintro ⟨C, x, hx⟩ - ⟨C', x', hx'⟩ - h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, hxx⟩ := h
    obtain rfl := eq_of_heq hxx
    rfl

/-- A reference arrow on block `C` realizes `w` on its source. -/
def RealizesOn (w : Equiv.Perm Y) (C : I)
    (c : FinitePartialBijection (E.model C) (E.model (β.objEquiv C))) : Prop :=
  ∀ x (hx : x ∈ c.source), E.embed (β.objEquiv C) (c.apply x hx) = w (E.embed C x)

/-- On a block, the arrow disagrees with `w` only where it disagrees with a
reference arrow realizing `w`. -/
theorem card_blockArrowDisagreement_le_disagreement (w : Equiv.Perm Y) (C : I)
    (c : FinitePartialBijection (E.model C) (E.model (β.objEquiv C)))
    (hc : β.RealizesOn w C c) :
    (β.blockArrowDisagreement w C).card ≤ ((β.arrow C).disagreement c).card := by
  refine Finset.card_le_card fun x hx ↦ ?_
  obtain ⟨hxb, hne⟩ := β.mem_blockArrowDisagreement.mp hx
  refine (mem_disagreement _ _ _).mpr fun hb hcx hsame ↦ hne ?_
  rw [hsame]
  exact hc x hcx

/-- **Patched permutation against a target.**  A patched permutation differs
from `w` by at most the mass off the glued domain, the disagreement of every
retained arrow with a reference arrow realizing `w`, and the full size of the
exceptional blocks. -/
theorem card_hammingDisagreement_patch_le_references [Fintype I] [DecidableEq I]
    (w : Equiv.Perm Y) (good : Finset I)
    (c : ∀ C, FinitePartialBijection (E.model C) (E.model (β.objEquiv C)))
    (hc : ∀ C ∈ good, β.RealizesOn w C (c C)) :
    (hammingDisagreement β.patch w).card ≤
      (Finset.univ \ β.domain).card +
        ∑ C ∈ good, ((β.arrow C).disagreement (c C)).card +
        ∑ C ∈ goodᶜ, Fintype.card (E.model C) := by
  have h1 := β.card_hammingDisagreement_patch_le w
  have h2 := β.card_arrowDisagreement_le_sum w
  have h3 : ∑ C, (β.blockArrowDisagreement w C).card ≤
      ∑ C ∈ good, ((β.arrow C).disagreement (c C)).card +
        ∑ C ∈ goodᶜ, Fintype.card (E.model C) := by
    rw [← Finset.sum_add_sum_compl good
      (fun C ↦ (β.blockArrowDisagreement w C).card)]
    exact add_le_add
      (Finset.sum_le_sum fun C hC ↦
        β.card_blockArrowDisagreement_le_disagreement w C (c C) (hc C hC))
      (Finset.sum_le_sum fun C _ ↦ Finset.card_le_univ _)
  omega

/-- Normalized form, with each retained disagreement bounded by the two-sided
disagreement used by the cluster groupoid. -/
theorem hammingDistance_patch_le_references [Fintype I] [DecidableEq I]
    (w : Equiv.Perm Y) (good : Finset I)
    (c : ∀ C, FinitePartialBijection (E.model C) (E.model (β.objEquiv C)))
    (hc : ∀ C ∈ good, β.RealizesOn w C (c C)) :
    hammingDistance Y β.patch w ≤
      (((Finset.univ \ β.domain).card +
        ∑ C ∈ good, (β.arrow C).twoSidedDisagreement (c C) +
        ∑ C ∈ goodᶜ, Fintype.card (E.model C) : ℕ) : ℝ) / Fintype.card Y := by
  rw [hammingDistance]
  gcongr
  have hcount := β.card_hammingDisagreement_patch_le_references w good c hc
  have htwo : ∑ C ∈ good, ((β.arrow C).disagreement (c C)).card ≤
      ∑ C ∈ good, (β.arrow C).twoSidedDisagreement (c C) :=
    Finset.sum_le_sum fun C _ ↦ by
      rw [FinitePartialBijection.twoSidedDisagreement]
      omega
  exact_mod_cast (hcount.trans (by omega))

end BlockArrows

/-! ## Re-separation at a vanishing scale

The cluster gap only says that two nearby candidates disagree on fewer than
a constant fraction of a block, which does not sum to `o(|Y|)`.  The
per-block bound comes instead from separating again at a scale proportional
to the equivariance defects and the local edit budget: two partial maps that
agree on a large set, whose combined defect is below the expansion constant
times the new scale, disagree on fewer points than that scale. -/

section Reseparation

open FinitePartialBijection

variable {L : Type*} [Fintype L] [DecidableEq L] {Y' Z' : FiniteModel}

/-- **Re-separation.**  On a source with tagged expansion at scale `m'`, two
partial maps whose combined equivariance defect is below `h * m'`, and which
agree on at least `m'` points, disagree on fewer than `m'` points. -/
theorem card_disagreement_lt_of_reseparation
    (actY : L → Equiv.Perm Y') (actZ : L → Equiv.Perm Z') {h : ℝ}
    (b c : FinitePartialBijection Y' Z') (m' : ℕ)
    (hexp : HasTaggedExpansionAtScale actY h m')
    (hdefect : (((b.equivarianceDefect actY actZ).card +
      (c.equivarianceDefect actY actZ).card : ℕ) : ℝ) < h * m')
    (hnear : (b.disagreement c).card + m' ≤ Fintype.card Y') :
    (b.disagreement c).card < m' := by
  rcases agreement_or_disagreement_small actY actZ b c m' hexp hdefect with
    hagree | hdis
  · have hsum := card_agreement_add_card_disagreement b c
    omega
  · exact hdis

/-- **Re-separation with an explicit real scale.**  Taking `m' = ⌊x⌋₊ + 1`,
the disagreement is at most `x`.  In the component setting `x` is
`(2 * editBudget + 4 * defects) / cheeger`. -/
theorem card_disagreement_le_of_reseparation
    (actY : L → Equiv.Perm Y') (actZ : L → Equiv.Perm Z') {h : ℝ}
    (b c : FinitePartialBijection Y' Z') {x : ℝ} (hx : 0 ≤ x)
    (hexp : HasTaggedExpansionAtScale actY h (⌊x⌋₊ + 1))
    (hdefect : (((b.equivarianceDefect actY actZ).card +
      (c.equivarianceDefect actY actZ).card : ℕ) : ℝ) < h * ((⌊x⌋₊ + 1 : ℕ) : ℝ))
    (hnear : (b.disagreement c).card + (⌊x⌋₊ + 1) ≤ Fintype.card Y') :
    ((b.disagreement c).card : ℝ) ≤ x := by
  have hlt := card_disagreement_lt_of_reseparation actY actZ b c _ hexp hdefect hnear
  have hle : (b.disagreement c).card ≤ ⌊x⌋₊ := by omega
  calc ((b.disagreement c).card : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hle
    _ ≤ x := Nat.floor_le hx

end Reseparation

end BlockPatching
end GroupApproximation
