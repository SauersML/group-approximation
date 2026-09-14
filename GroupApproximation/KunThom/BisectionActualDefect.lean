import GroupApproximation.KunThom.FixedPointNormalizationBisection
import GroupApproximation.KunThom.FixedPointNormalizationScaleSums
import GroupApproximation.KunThom.FixedPointNormalizationSummation

/-!
# Patched commutation from actual arrow defects

`BlockPatching.BlockArrows.card_commutationDefect_patch_le` bounds how far a
patched permutation is from commuting with a label: twice the mass off the
glued domain, twice the compatibility failures of the block actions, and the
equivariance defects of the block arrows.  This file removes the glued domain
from that bound, allows a separate scale on every block, and gives the
sequential form.

* `BlockArrows.card_compl_domain_le`: a point off the glued domain lies in no
  block, or is a missing source point of the arrow of its block.
* `BlockArrows.card_commutationDefect_patch_le_actual`: with at least one
  label, the commutation defect is at most twice the uncovered mass, twice the
  compatibility failures and three times the total equivariance defect.
* `BlockArrows.card_commutationDefect_patch_le_of_candidates`: if the arrow of
  every block `C` is a cluster candidate at threshold `h` and scale `m C` with
  `17 * m C ≤ |C|`, the defect term is at most `3 * (h / 34) * |Y|`.
* `vanishing_commutator_patch_of_candidates`: along a sequence, negligible
  uncovered mass and compatibility failures, together with thresholds `h n`
  tending to zero, make the patched permutations almost commute with the label.
* `card_commutationDefect_bisectionPatch_le_uncovered` and
  `vanishing_commutator_bisectionPatch`: the same for patched bisections of a
  `PartialClusterSystem`.

## Where the threshold term goes

The candidate term vanishes because the threshold does.  In Kun--Thom,
arXiv:2608.06222v3, Lemma 4.2(1) and (4), an allowed arrow has normalized
source, range and equivariance defects at most `ε_n`, with `ε_n → 0` along
the ultrafilter, and every sequence of patched bisections of allowed arrows
represents an element of the centralizer.  Alekseev--Thom, arXiv:2608.05362v1,
Proposition 4.5(b), states the finite form: the commutation defect of every
patched bisection is at most `ε_n`.  The bisection patched at the end of the
proof of Kun--Thom Theorem 4.1 is chosen through the relative functor and
completed arbitrarily, so the only control on its arrows is that they are
allowed.  The expansion constant stays fixed and serves only the distance gap.

Here a candidate at threshold `h` and scale `m = |C| / 18` has fewer than
`h * m / 2` failing label-point pairs, so the threshold `h` itself must tend to
zero while the scale stays a fixed fraction of the block.
`hasTaggedExpansionAtScale_of_le` transfers the expansion hypothesis from the
Cheeger level to every smaller positive threshold.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

/-- Expansion at level `h'` gives expansion at every smaller positive level. -/
theorem hasTaggedExpansionAtScale_of_le {L : Type*} [Fintype L] {Y : FiniteModel}
    {act : L → Equiv.Perm Y} {h h' : ℝ} {m : ℕ}
    (hexp : HasTaggedExpansionAtScale act h' m) (hpos : 0 < h) (hle : h ≤ h') :
    HasTaggedExpansionAtScale act h m := by
  refine ⟨hpos, fun A hA hhalf ↦ ?_⟩
  have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  exact (mul_le_mul_of_nonneg_right hle hA0).trans (hexp.2 A hA hhalf)

/-- With at least one label, a partial bijection has at least as many
equivariance failures as missing source points. -/
theorem sourceDefect_le_card_equivarianceDefect {L : Type*} [Fintype L]
    [Nonempty L] {Y Z : FiniteModel} (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    b.sourceDefect ≤ (b.equivarianceDefect actY actZ).card := by
  have hlabels : 1 ≤ Fintype.card L := Fintype.card_pos
  calc b.sourceDefect = 1 * b.sourceDefect := by omega
    _ ≤ Fintype.card L * b.sourceDefect :=
      Nat.mul_le_mul_right b.sourceDefect hlabels
    _ ≤ (b.equivarianceDefect actY actZ).card :=
      card_mul_sourceDefect_le_card_equivarianceDefect b actY actZ

namespace BlockEmbedding

variable {Y : FiniteModel} {I : Type u} (E : BlockEmbedding Y I)

/-- Ambient points lying in no block. -/
noncomputable def uncovered : Finset Y := by
  classical
  exact Finset.univ.filter fun y ↦ ∀ (C : I) (x : E.model C), E.embed C x ≠ y

theorem mem_uncovered {y : Y} :
    y ∈ E.uncovered ↔ ∀ (C : I) (x : E.model C), E.embed C x ≠ y := by
  simp [uncovered]

end BlockEmbedding

namespace BlockArrows

variable {Y : FiniteModel} {I : Type u}
variable {E : BlockEmbedding Y I} (β : BlockArrows E)

/-- **Off the glued domain.**  A point off the glued domain lies in no block,
or is a missing source point of the arrow of its block. -/
theorem card_compl_domain_le [Fintype I] :
    (Finset.univ \ β.domain).card ≤
      E.uncovered.card + ∑ C, (β.arrow C).sourceDefect := by
  have hmissing : (Finset.univ.sigma fun C ↦
      Finset.univ \ (β.arrow C).source).card =
        ∑ C, (β.arrow C).sourceDefect := by
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [FinitePartialBijection.sourceDefect]
  have hsub : Finset.univ \ β.domain ⊆ E.uncovered ∪
      (Finset.univ.sigma fun C ↦ Finset.univ \ (β.arrow C).source).image
        fun p ↦ E.embed p.1 p.2 := by
    intro y hy
    rw [Finset.mem_union]
    by_cases hcov : y ∈ E.uncovered
    · exact Or.inl hcov
    · right
      rw [E.mem_uncovered] at hcov
      push Not at hcov
      obtain ⟨C, x, rfl⟩ := hcov
      have hx : x ∉ (β.arrow C).source := fun hx ↦
        (Finset.mem_sdiff.mp hy).2 (β.mem_domain.mpr ⟨⟨C, x, hx⟩, rfl⟩)
      rw [Finset.mem_image]
      exact ⟨⟨C, x⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩, rfl⟩
  have hle := Finset.card_le_card hsub
  have hunion := Finset.card_union_le E.uncovered
    ((Finset.univ.sigma fun C ↦ Finset.univ \ (β.arrow C).source).image
      fun p ↦ E.embed p.1 p.2)
  have himage : ((Finset.univ.sigma fun C ↦
      Finset.univ \ (β.arrow C).source).image fun p ↦ E.embed p.1 p.2).card ≤
        (Finset.univ.sigma fun C ↦ Finset.univ \ (β.arrow C).source).card :=
    Finset.card_image_le
  omega

/-- **Patched commutation from actual defects.**  With at least one label, a
patched permutation fails to commute with a label on at most twice the
uncovered mass, twice the compatibility failures of the block actions, and
three times the total equivariance defect of the block arrows. -/
theorem card_commutationDefect_patch_le_actual [Fintype I] {L : Type*}
    [Fintype L] [Nonempty L] (A : BlockAction E L) (s : L) :
    (hammingDisagreement (β.patch * A.act s) (A.act s * β.patch)).card ≤
      2 * E.uncovered.card + 2 * ∑ C, (A.compatFailure C s).card +
        3 * ∑ C, ((β.arrow C).equivarianceDefect (A.blockAct C)
          (A.blockAct (β.objEquiv C))).card := by
  have hcount := β.card_commutationDefect_patch_le A s
  have hdomain := β.card_compl_domain_le
  have hcompat := A.card_globalCompatFailure_le s
  have hsource : ∑ C, (β.arrow C).sourceDefect ≤
      ∑ C, ((β.arrow C).equivarianceDefect (A.blockAct C)
        (A.blockAct (β.objEquiv C))).card :=
    Finset.sum_le_sum fun C _ ↦ sourceDefect_le_card_equivarianceDefect
      (β.arrow C) (A.blockAct C) (A.blockAct (β.objEquiv C))
  omega

/-- **Patched commutation at a proportional threshold.**  If every block arrow
has at most `η |C|` equivariance failures, the defect term is at most
`3 η |Y|`. -/
theorem card_commutationDefect_patch_le_of_defect_le [Fintype I] {L : Type*}
    [Fintype L] [Nonempty L] (A : BlockAction E L) (s : L) {η : ℝ} (hη : 0 ≤ η)
    (hdefect : ∀ C, (((β.arrow C).equivarianceDefect (A.blockAct C)
      (A.blockAct (β.objEquiv C))).card : ℝ) ≤ η * Fintype.card (E.model C)) :
    ((hammingDisagreement (β.patch * A.act s) (A.act s * β.patch)).card : ℝ) ≤
      2 * (E.uncovered.card : ℝ) + 2 * ∑ C, ((A.compatFailure C s).card : ℝ) +
        3 * (η * Fintype.card Y) := by
  have hcast : ((hammingDisagreement (β.patch * A.act s)
      (A.act s * β.patch)).card : ℝ) ≤
        2 * (E.uncovered.card : ℝ) + 2 * ∑ C, ((A.compatFailure C s).card : ℝ) +
          3 * ∑ C, (((β.arrow C).equivarianceDefect (A.blockAct C)
            (A.blockAct (β.objEquiv C))).card : ℝ) := by
    exact_mod_cast β.card_commutationDefect_patch_le_actual A s
  have hsum : ∑ C, (((β.arrow C).equivarianceDefect (A.blockAct C)
      (A.blockAct (β.objEquiv C))).card : ℝ) ≤ η * Fintype.card Y :=
    (Finset.sum_le_sum fun C _ ↦ hdefect C).trans (E.sum_mul_card_model_le hη)
  linarith

/-- **Patched commutation for cluster candidates.**  If the arrow of every
block `C` is a cluster candidate at threshold `h` and at a scale `m C` with
`17 * m C ≤ |C|`, the defect term is at most `3 (h / 34) |Y|`. -/
theorem card_commutationDefect_patch_le_of_candidates [Fintype I] {L : Type*}
    [Fintype L] [Nonempty L] (A : BlockAction E L) (s : L) {h : ℝ} (hh : 0 ≤ h)
    (m : I → ℕ) (hsize : ∀ C, 17 * m C ≤ Fintype.card (E.model C))
    (hcand : ∀ C, (β.arrow C).IsClusterCandidate (A.blockAct C)
      (A.blockAct (β.objEquiv C)) h (m C)) :
    ((hammingDisagreement (β.patch * A.act s) (A.act s * β.patch)).card : ℝ) ≤
      2 * (E.uncovered.card : ℝ) + 2 * ∑ C, ((A.compatFailure C s).card : ℝ) +
        3 * (h / 34 * Fintype.card Y) := by
  have hη : 0 ≤ h / 34 := div_nonneg hh (by norm_num)
  refine β.card_commutationDefect_patch_le_of_defect_le A s hη fun C ↦ ?_
  have hlt := (hcand C).forwardSmall
  have hm : (17 * m C : ℝ) ≤ Fintype.card (E.model C) := by
    exact_mod_cast hsize C
  have hscaled : h * (17 * m C : ℝ) ≤ h * Fintype.card (E.model C) :=
    mul_le_mul_of_nonneg_left hm hh
  linarith

end BlockArrows

/-- **Vanishing commutation of patched candidates.**  Along a sequence of
patched permutations, suppose the uncovered mass and the compatibility failures
of a label are negligible, and every block arrow is a cluster candidate at a
threshold `h n` tending to zero and at a scale of at most a seventeenth of its
block.  Then the patched permutations almost commute with the label. -/
theorem vanishing_commutator_patch_of_candidates {Y : ℕ → FiniteModel}
    {I : ℕ → Type u} [∀ n, Fintype (I n)] {E : ∀ n, BlockEmbedding (Y n) (I n)}
    (β : ∀ n, BlockArrows (E n)) {L : Type*} [Fintype L] [Nonempty L]
    (A : ∀ n, BlockAction (E n) L) (s : L) (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n)
    (hvanish : Vanishing h) (m : ∀ n, I n → ℕ)
    (hsize : ∀ n C, 17 * m n C ≤ Fintype.card ((E n).model C))
    (hcand : ∀ n C, ((β n).arrow C).IsClusterCandidate ((A n).blockAct C)
      ((A n).blockAct ((β n).objEquiv C)) (h n) (m n C))
    (huncovered : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ((E n).uncovered.card : ℝ))
    (hcompat : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ C, (((A n).compatFailure C s).card : ℝ)) :
    Vanishing fun n ↦ hammingDistance (Y n)
      ((β n).patch * (A n).act s) ((A n).act s * (β n).patch) := by
  refine vanishing_hammingDistance_of_card_le
    (fun n ↦ (β n).patch * (A n).act s) (fun n ↦ (A n).act s * (β n).patch)
    (fun n ↦ 2 * ((E n).uncovered.card : ℝ) +
      2 * ∑ C, (((A n).compatFailure C s).card : ℝ) +
        3 * (h n / 34 * Fintype.card (Y n)))
    (fun n ↦ (β n).card_commutationDefect_patch_le_of_candidates (A n) s (hh n)
      (m n) (hsize n) (hcand n)) ?_
  have hthreshold : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ h n / 34 * Fintype.card (Y n) := by
    refine Vanishing.squeeze (fun n ↦ ?_) (fun n ↦ ?_)
      (hvanish.const_mul (1 / 34))
    · exact div_nonneg (mul_nonneg (div_nonneg (hh n) (by norm_num))
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    · show h n / 34 * (Fintype.card (Y n) : ℝ) / Fintype.card (Y n) ≤
        1 / 34 * h n
      by_cases hcard : Fintype.card (Y n) = 0
      · rw [hcard, Nat.cast_zero, div_zero]
        exact mul_nonneg (by norm_num) (hh n)
      · have hpos : (0 : ℝ) < Fintype.card (Y n) := by
          exact_mod_cast Nat.pos_of_ne_zero hcard
        rw [mul_div_assoc, div_self hpos.ne', mul_one]
        linarith
  exact ((huncovered.const_mul 2).add (hcompat.const_mul 2)).add
    (hthreshold.const_mul 3)

/-- **Patched bisections, from the uncovered mass.**  The commutation defect of
a patched bisection of a cluster system with a label is at most twice the
uncovered mass, twice the compatibility failures, and `3 (h / 34) |Y|`. -/
theorem card_commutationDefect_bisectionPatch_le_uncovered {I : Type u}
    [Fintype I] {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    {D : PartialClusterSystem I L} {Y : FiniteModel}
    {ι : ∀ X, D.model X → Y} {hinj : ∀ X, Function.Injective (ι X)}
    {hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
      ι X x = ι X' z → X = X'}
    (b : FiniteGroupoid.Bisection D.presentation.Obj)
    (act : L → Equiv.Perm Y) (s : L) :
    ((hammingDisagreement
        ((bisectionArrows (ι := ι) (hinj := hinj) (hdisj := hdisj) b).patch *
          act s)
        (act s *
          (bisectionArrows (ι := ι) (hinj := hinj) (hdisj := hdisj) b).patch)
      ).card : ℝ) ≤
      2 * ((clusterEmbedding D ι hinj hdisj).uncovered.card : ℝ) +
        2 * ∑ X, (((clusterAction (ι := ι) (hinj := hinj) (hdisj := hdisj)
          (D := D) act).compatFailure X s).card : ℝ) +
        3 * (D.h / 34 * Fintype.card Y) :=
  (bisectionArrows (ι := ι) (hinj := hinj) (hdisj := hdisj)
    b).card_commutationDefect_patch_le_of_candidates
    (clusterAction (ι := ι) (hinj := hinj) (hdisj := hdisj) (D := D) act) s
    D.h_pos.le (fun _ ↦ D.scale) (fun X ↦ D.size X)
    (fun X ↦ bisectionArrows_isClusterCandidate (ι := ι) (hinj := hinj)
      (hdisj := hdisj) b X)

/-- **Vanishing commutation of patched bisections.**  For a sequence of
cluster systems whose thresholds tend to zero, with negligible uncovered mass
and negligible compatibility failures of a label, patched bisections almost
commute with the label. -/
theorem vanishing_commutator_bisectionPatch {I : ℕ → Type u}
    [∀ n, Fintype (I n)] {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (D : ∀ n, PartialClusterSystem (I n) L) {Y : ℕ → FiniteModel}
    (ι : ∀ n X, (D n).model X → Y n)
    (hinj : ∀ n X, Function.Injective (ι n X))
    (hdisj : ∀ n (X X' : I n) (x : (D n).model X) (z : (D n).model X'),
      ι n X x = ι n X' z → X = X')
    (b : ∀ n, FiniteGroupoid.Bisection (D n).presentation.Obj)
    (act : ∀ n, L → Equiv.Perm (Y n)) (s : L)
    (hh : Vanishing fun n ↦ (D n).h)
    (huncovered : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ((clusterEmbedding (D n) (ι n) (hinj n) (hdisj n)).uncovered.card : ℝ))
    (hcompat : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ X, (((clusterAction (ι := ι n) (hinj := hinj n)
        (hdisj := hdisj n) (D := D n) (act n)).compatFailure X s).card : ℝ)) :
    Vanishing fun n ↦ hammingDistance (Y n)
      ((bisectionArrows (ι := ι n) (hinj := hinj n) (hdisj := hdisj n)
        (b n)).patch * act n s)
      (act n s * (bisectionArrows (ι := ι n) (hinj := hinj n)
        (hdisj := hdisj n) (b n)).patch) :=
  vanishing_commutator_patch_of_candidates
    (fun n ↦ bisectionArrows (ι := ι n) (hinj := hinj n) (hdisj := hdisj n) (b n))
    (fun n ↦ clusterAction (ι := ι n) (hinj := hinj n) (hdisj := hdisj n)
      (D := D n) (act n)) s
    (fun n ↦ (D n).h) (fun n ↦ (D n).h_pos.le) hh (fun n _ ↦ (D n).scale)
    (fun n X ↦ (D n).size X)
    (fun n X ↦ bisectionArrows_isClusterCandidate (ι := ι n) (hinj := hinj n)
      (hdisj := hdisj n) (b n) X)
    huncovered hcompat

end BlockPatching
end GroupApproximation
