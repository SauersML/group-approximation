import GroupApproximation.KunThom.CentralizerToBisectionOverlap
import GroupApproximation.Matching.PartialClusterCandidates
import Mathlib.Tactic.Group

/-!
# Equivariance defects of overlap arrows

The overlap arrows of a permutation `v` (`BlockEmbedding.overlapArrow`) are
almost equivariant for the block actions wherever `v` almost commutes with the
ambient action and the block actions almost agree with it.

* `BlockAction.overlapFailure v s`: the compatibility failures of label `s`,
  their preimages under `v`, and the points where `v` fails to commute with
  the label.  Its size is at most twice the compatibility failures plus the
  commutation defect (`card_overlapFailure_le`).
* `BlockAction.card_equivarianceDefect_overlapArrow_le`: an overlap arrow fails
  equivariance only at missing source points, `|L|` times each, or at source
  points lying over an overlap failure.
* `BlockAction.sum_card_equivarianceDefect_overlapArrow_le` and
  `sum_card_symm_equivarianceDefect_overlapArrow_le`: along any object map, the
  total forward (inverse) defect is at most `|L|` times the total source
  (target) defect plus the overlap failures of `v` (of `v⁻¹`), summed over the
  labels.
* `card_hammingDisagreement_inv_commutator`: `v⁻¹` has the same commutation
  defect as `v`.
* `isClusterCandidate_of_card_equivarianceDefect_lt`: with expansion constant
  at most `2 |L|`, forward and inverse defects below `h m / 2` make a partial
  bijection a cluster candidate; `le_two_mul_card_of_hasTaggedExpansionAtScale`
  supplies that bound from expansion.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

/-- Inverting the permutation preserves the commutation defect. -/
theorem card_hammingDisagreement_inv_commutator {Y : FiniteModel}
    (v a : Equiv.Perm Y) :
    (hammingDisagreement (v⁻¹ * a) (a * v⁻¹)).card =
      (hammingDisagreement (v * a) (a * v)).card := by
  rw [hammingDisagreement_eq_support, hammingDisagreement_eq_support]
  have hconj : (a * v⁻¹)⁻¹ * (v⁻¹ * a) = (v * ((a * v)⁻¹ * (v * a)) * v⁻¹)⁻¹ := by
    group
  rw [hconj, Equiv.Perm.support_inv, Equiv.Perm.card_support_conj]

/-- Every tagged boundary has at most `2 |L| |A|` arcs. -/
theorem card_taggedBoundary_le {L : Type*} [Fintype L] {Y : FiniteModel}
    (act : L → Equiv.Perm Y) (A : Finset Y) :
    (taggedBoundary act A).card ≤ 2 * (Fintype.card L * A.card) := by
  classical
  have hsub : taggedBoundary act A ⊆ (Finset.univ ×ˢ A) ∪
      (Finset.univ ×ˢ A).image fun p ↦ (p.1, (act p.1).symm p.2) := by
    intro p hp
    rw [mem_taggedBoundary] at hp
    rcases hp with ⟨hA, _⟩ | ⟨_, hsA⟩
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨Finset.mem_univ _, hA⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(p.1, act p.1 p.2), Finset.mem_product.mpr ⟨Finset.mem_univ _, hsA⟩, ?_⟩)
      exact Prod.ext rfl ((act p.1).symm_apply_apply p.2)
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le (Finset.univ ×ˢ A)
    ((Finset.univ ×ˢ A).image fun p ↦ (p.1, (act p.1).symm p.2))
  have h₃ : ((Finset.univ ×ˢ A).image fun p ↦ (p.1, (act p.1).symm p.2)).card ≤
      (Finset.univ ×ˢ A).card := Finset.card_image_le
  have h₄ : ((Finset.univ : Finset L) ×ˢ A).card = Fintype.card L * A.card := by
    rw [Finset.card_product, Finset.card_univ]
  omega

/-- Expansion at a positive scale, in a model with at least twice that many
points, bounds the expansion constant by `2 |L|`. -/
theorem le_two_mul_card_of_hasTaggedExpansionAtScale {L : Type*} [Fintype L]
    {Y : FiniteModel} {act : L → Equiv.Perm Y} {h : ℝ} {m : ℕ}
    (hexp : HasTaggedExpansionAtScale act h m) (hm : 0 < m)
    (hsize : 2 * m ≤ Fintype.card Y) : h ≤ 2 * Fintype.card L := by
  classical
  obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset Y))
    (n := m) (by rw [Finset.card_univ]; omega)
  have hexpand := hexp.2 A (le_of_eq hA.symm) (by omega)
  have hbound := card_taggedBoundary_le act A
  rw [hA] at hexpand hbound
  have hboundR : ((taggedBoundary act A).card : ℝ) ≤ 2 * (Fintype.card L * m) := by
    exact_mod_cast hbound
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hprod : h * m ≤ 2 * Fintype.card L * m := by
    have hchain := hexpand.trans hboundR
    linarith
  exact le_of_mul_le_mul_right hprod hmR

/-- **Candidates from defects.**  If the expansion constant is at most `2 |L|`,
forward and inverse equivariance defects below `h m / 2` make a partial
bijection a cluster candidate. -/
theorem isClusterCandidate_of_card_equivarianceDefect_lt {L : Type*} [Fintype L]
    {Y Z : FiniteModel} (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    {h : ℝ} {m : ℕ} (hh : h ≤ 2 * Fintype.card L) (f : FinitePartialBijection Y Z)
    (hfwd : ((f.equivarianceDefect actY actZ).card : ℝ) < h * m / 2)
    (hbwd : ((f.symm.equivarianceDefect actZ actY).card : ℝ) < h * m / 2) :
    f.IsClusterCandidate actY actZ h m := by
  refine ⟨?_, hfwd, hbwd⟩
  by_contra hself
  have hself' : 2 * m ≤ f.sourceDefect + f.targetDefect := by omega
  have hs := card_mul_sourceDefect_le_card_equivarianceDefect f actY actZ
  have ht := card_mul_targetDefect_le_card_symm_equivarianceDefect f actY actZ
  have hmul : Fintype.card L * (2 * m) ≤
      (f.equivarianceDefect actY actZ).card +
        (f.symm.equivarianceDefect actZ actY).card := by
    calc Fintype.card L * (2 * m)
        ≤ Fintype.card L * (f.sourceDefect + f.targetDefect) :=
          Nat.mul_le_mul_left _ hself'
      _ = Fintype.card L * f.sourceDefect + Fintype.card L * f.targetDefect :=
          Nat.mul_add _ _ _
      _ ≤ _ := Nat.add_le_add hs ht
  have hmulR : (Fintype.card L : ℝ) * (2 * m) ≤
      ((f.equivarianceDefect actY actZ).card : ℝ) +
        ((f.symm.equivarianceDefect actZ actY).card : ℝ) := by
    exact_mod_cast hmul
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hhm : h * m ≤ 2 * Fintype.card L * m := mul_le_mul_of_nonneg_right hh hm
  linarith

namespace BlockAction

variable {Y : FiniteModel} {I : Type u} {E : BlockEmbedding Y I} {L : Type*}
variable (A : BlockAction E L)

/-- Ambient points at which reading `v` block by block may fail to be
equivariant for the label `s`: compatibility failures of the block actions,
their preimages under `v`, and commutation failures of `v`. -/
noncomputable def overlapFailure [Fintype I] (v : Equiv.Perm Y) (s : L) : Finset Y :=
  A.globalCompatFailure s ∪ hammingDisagreement (v * A.act s) (A.act s * v) ∪
    (A.globalCompatFailure s).image v.symm

theorem card_overlapFailure_le [Fintype I] (v : Equiv.Perm Y) (s : L) :
    (A.overlapFailure v s).card ≤ 2 * (A.globalCompatFailure s).card +
      (hammingDisagreement (v * A.act s) (A.act s * v)).card := by
  have h₁ := Finset.card_union_le (A.globalCompatFailure s ∪
    hammingDisagreement (v * A.act s) (A.act s * v))
    ((A.globalCompatFailure s).image v.symm)
  have h₂ := Finset.card_union_le (A.globalCompatFailure s)
    (hammingDisagreement (v * A.act s) (A.act s * v))
  have h₃ : ((A.globalCompatFailure s).image v.symm).card ≤
      (A.globalCompatFailure s).card := Finset.card_image_le
  unfold overlapFailure
  omega

/-- **Equivariance off the failures.**  At a source point lying over no overlap
failure, the overlap arrow commutes with the label. -/
theorem overlapArrow_apply_blockAct [Fintype I] {v : Equiv.Perm Y} {C C' : I}
    {s : L} {x : E.model C} (hx : x ∈ (E.overlapArrow v C C').source)
    (hfail : E.embed C x ∉ A.overlapFailure v s) :
    ∃ hsx : A.blockAct C s x ∈ (E.overlapArrow v C C').source,
      (E.overlapArrow v C C').apply (A.blockAct C s x) hsx =
        A.blockAct C' s ((E.overlapArrow v C C').apply x hx) := by
  have hF : E.embed C x ∉ A.globalCompatFailure s := fun h ↦
    hfail (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hK : E.embed C x ∉ hammingDisagreement (v * A.act s) (A.act s * v) := fun h ↦
    hfail (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hF' : v (E.embed C x) ∉ A.globalCompatFailure s := fun h ↦
    hfail (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨v (E.embed C x), h, v.symm_apply_apply _⟩))
  have hvx : v (E.embed C x) = E.embed C' ((E.overlapArrow v C C').apply x hx) :=
    (E.embed_overlapArrow_apply v C C' x hx).symm
  have hcompat : E.embed C (A.blockAct C s x) = A.act s (E.embed C x) :=
    A.embed_blockAct_of_not_mem fun h ↦ hF (A.embed_mem_globalCompatFailure h)
  have hcomm : v (A.act s (E.embed C x)) = A.act s (v (E.embed C x)) := by
    by_contra hne
    apply hK
    rw [mem_hammingDisagreement]
    exact hne
  have hcompat' : E.embed C' (A.blockAct C' s ((E.overlapArrow v C C').apply x hx)) =
      A.act s (E.embed C' ((E.overlapArrow v C C').apply x hx)) := by
    refine A.embed_blockAct_of_not_mem fun h ↦ hF' ?_
    rw [hvx]
    exact A.embed_mem_globalCompatFailure h
  have himage : v (E.embed C (A.blockAct C s x)) =
      E.embed C' (A.blockAct C' s ((E.overlapArrow v C C').apply x hx)) := by
    rw [hcompat, hcomm, hvx, hcompat']
  exact ⟨E.mem_overlapArrow_source_of_apply himage,
    E.overlapArrow_apply_eq_of_apply himage⟩

/-- An equivariance failure of an overlap arrow is a missing source point or a
point lying over an overlap failure. -/
theorem mem_equivarianceDefect_overlapArrow [Fintype I] [Fintype L]
    {v : Equiv.Perm Y} {C C' : I} {p : L × E.model C}
    (hp : p ∈ (E.overlapArrow v C C').equivarianceDefect (A.blockAct C)
      (A.blockAct C')) :
    p.2 ∉ (E.overlapArrow v C C').source ∨
      E.embed C p.2 ∈ A.overlapFailure v p.1 := by
  by_contra hnot
  push Not at hnot
  obtain ⟨hx, hfail⟩ := hnot
  obtain ⟨hsx, heq⟩ := A.overlapArrow_apply_blockAct hx hfail
  exact (mem_equivarianceDefect _ _ _ p).mp hp hx hsx heq

/-- Label-point pairs of block `C` at source points of the overlap arrow into
`C'` lying over an overlap failure. -/
noncomputable def blockFailure [Fintype I] [Fintype L] (v : Equiv.Perm Y)
    (C C' : I) : Finset (L × E.model C) := by
  classical
  exact Finset.univ.filter fun p ↦
    p.2 ∈ (E.overlapArrow v C C').source ∧ E.embed C p.2 ∈ A.overlapFailure v p.1

/-- **Defect of one overlap arrow.** -/
theorem card_equivarianceDefect_overlapArrow_le [Fintype I] [Fintype L]
    (v : Equiv.Perm Y) (C C' : I) :
    ((E.overlapArrow v C C').equivarianceDefect (A.blockAct C)
        (A.blockAct C')).card ≤
      Fintype.card L * (E.overlapArrow v C C').sourceDefect +
        (A.blockFailure v C C').card := by
  classical
  have hsub : (E.overlapArrow v C C').equivarianceDefect (A.blockAct C)
      (A.blockAct C') ⊆
        (Finset.univ ×ˢ (Finset.univ \ (E.overlapArrow v C C').source)) ∪
          A.blockFailure v C C' := by
    intro p hp
    rcases A.mem_equivarianceDefect_overlapArrow hp with hmiss | hfail
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hmiss⟩⟩)
    · by_cases hx : p.2 ∈ (E.overlapArrow v C C').source
      · refine Finset.mem_union_right _ ?_
        simp only [blockFailure, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hx, hfail⟩
      · exact Finset.mem_union_left _ (Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hprod : ((Finset.univ : Finset L) ×ˢ
      (Finset.univ \ (E.overlapArrow v C C').source)).card =
        Fintype.card L * (E.overlapArrow v C C').sourceDefect := by
    rw [Finset.card_product, Finset.card_univ,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    rfl
  omega

/-- **Total forward defect.**  Along any object map the overlap arrows of `v`
fail equivariance on at most `|L|` times their total source defect plus the
overlap failures of `v`, summed over the labels. -/
theorem sum_card_equivarianceDefect_overlapArrow_le [Fintype I] [Fintype L]
    (v : Equiv.Perm Y) (π : I → I) :
    ∑ C, ((E.overlapArrow v C (π C)).equivarianceDefect (A.blockAct C)
        (A.blockAct (π C))).card ≤
      Fintype.card L * ∑ C, (E.overlapArrow v C (π C)).sourceDefect +
        ∑ s, (A.overlapFailure v s).card := by
  classical
  have hsum : ∑ C, ((E.overlapArrow v C (π C)).equivarianceDefect (A.blockAct C)
        (A.blockAct (π C))).card ≤
      ∑ C, (Fintype.card L * (E.overlapArrow v C (π C)).sourceDefect +
        (A.blockFailure v C (π C)).card) :=
    Finset.sum_le_sum fun C _ ↦ A.card_equivarianceDefect_overlapArrow_le v C (π C)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hinj : ∑ C, (A.blockFailure v C (π C)).card ≤
      ∑ s, (A.overlapFailure v s).card := by
    rw [← Finset.card_sigma, ← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn
      (fun q ↦ (⟨q.2.1, E.embed q.1 q.2.2⟩ : Σ _ : L, Y)) ?_ ?_
    · intro q hq
      have hq' := Finset.mem_sigma.mp (Finset.mem_coe.mp hq)
      have hbf : q.2 ∈ A.blockFailure v q.1 (π q.1) := hq'.2
      simp only [blockFailure, Finset.mem_filter, Finset.mem_univ, true_and] at hbf
      exact Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hbf.2⟩)
    · rintro ⟨C₁, s₁, x₁⟩ _ ⟨C₂, s₂, x₂⟩ _ h
      obtain ⟨hs, hx⟩ := Sigma.mk.inj_iff.mp h
      have hxeq : E.embed C₁ x₁ = E.embed C₂ x₂ := eq_of_heq hx
      have hC : C₁ = C₂ := E.embed_disjoint C₁ C₂ x₁ x₂ hxeq
      subst hC
      have hxx : x₁ = x₂ := E.embed_injective C₁ hxeq
      subst hxx
      subst hs
      rfl
  exact hsum.trans (Nat.add_le_add_left hinj _)

/-- **Total inverse defect.**  Along any object map the inverses of the overlap
arrows of `v` fail equivariance on at most `|L|` times their total target
defect plus the overlap failures of `v⁻¹`, summed over the labels. -/
theorem sum_card_symm_equivarianceDefect_overlapArrow_le [Fintype I] [Fintype L]
    (v : Equiv.Perm Y) (π : I → I) :
    ∑ C, ((E.overlapArrow v C (π C)).symm.equivarianceDefect (A.blockAct (π C))
        (A.blockAct C)).card ≤
      Fintype.card L * ∑ C, (E.overlapArrow v C (π C)).targetDefect +
        ∑ s, (A.overlapFailure v⁻¹ s).card := by
  classical
  have hblock : ∀ C, ((E.overlapArrow v C (π C)).symm.equivarianceDefect
      (A.blockAct (π C)) (A.blockAct C)).card ≤
        Fintype.card L * (E.overlapArrow v C (π C)).targetDefect +
          (A.blockFailure v⁻¹ (π C) C).card := by
    intro C
    have ht : (E.overlapArrow v⁻¹ (π C) C).sourceDefect =
        (E.overlapArrow v C (π C)).targetDefect := by
      rw [← E.overlapArrow_symm v C (π C), sourceDefect_symm]
    rw [E.overlapArrow_symm v C (π C), ← ht]
    exact A.card_equivarianceDefect_overlapArrow_le v⁻¹ (π C) C
  have hsum : ∑ C, ((E.overlapArrow v C (π C)).symm.equivarianceDefect
        (A.blockAct (π C)) (A.blockAct C)).card ≤
      ∑ C, (Fintype.card L * (E.overlapArrow v C (π C)).targetDefect +
        (A.blockFailure v⁻¹ (π C) C).card) :=
    Finset.sum_le_sum fun C _ ↦ hblock C
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hinj : ∑ C, (A.blockFailure v⁻¹ (π C) C).card ≤
      ∑ s, (A.overlapFailure v⁻¹ s).card := by
    rw [← Finset.card_sigma, ← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn
      (fun q ↦ (⟨q.2.1, E.embed (π q.1) q.2.2⟩ : Σ _ : L, Y)) ?_ ?_
    · intro q hq
      have hq' := Finset.mem_sigma.mp (Finset.mem_coe.mp hq)
      have hbf : q.2 ∈ A.blockFailure v⁻¹ (π q.1) q.1 := hq'.2
      simp only [blockFailure, Finset.mem_filter, Finset.mem_univ, true_and] at hbf
      exact Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hbf.2⟩)
    · rintro ⟨C₁, s₁, x₁⟩ hq₁ ⟨C₂, s₂, x₂⟩ hq₂ h
      obtain ⟨hs, hx⟩ := Sigma.mk.inj_iff.mp h
      have hxeq : E.embed (π C₁) x₁ = E.embed (π C₂) x₂ := eq_of_heq hx
      have hb₁ : (s₁, x₁) ∈ A.blockFailure v⁻¹ (π C₁) C₁ :=
        (Finset.mem_sigma.mp (Finset.mem_coe.mp hq₁)).2
      have hb₂ : (s₂, x₂) ∈ A.blockFailure v⁻¹ (π C₂) C₂ :=
        (Finset.mem_sigma.mp (Finset.mem_coe.mp hq₂)).2
      simp only [blockFailure, Finset.mem_filter, Finset.mem_univ, true_and] at hb₁ hb₂
      obtain ⟨a, ha⟩ := E.mem_overlapSource.mp hb₁.1
      obtain ⟨b, hb⟩ := E.mem_overlapSource.mp hb₂.1
      have hab : E.embed C₁ a = E.embed C₂ b :=
        ha.symm.trans ((congrArg (fun y ↦ v⁻¹ y) hxeq).trans hb)
      have hC : C₁ = C₂ := E.embed_disjoint C₁ C₂ a b hab
      subst hC
      have hxx : x₁ = x₂ := E.embed_injective (π C₁) hxeq
      subst hxx
      subst hs
      rfl
  exact hsum.trans (Nat.add_le_add_left hinj _)

end BlockAction

end BlockPatching
end GroupApproximation
