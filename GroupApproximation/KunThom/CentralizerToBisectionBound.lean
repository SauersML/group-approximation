import GroupApproximation.KunThom.CentralizerToBisection
import GroupApproximation.KunThom.BisectionActualDefect

/-!
# The representing patch is close to the permutation

`PartialClusterSystem.card_hammingDisagreement_representingPatch_le` bounds how
far the patched representing arrows of a permutation `v` are from `v`, by the
mass off the glued domain and the objects outside `overlapGood v`.  This file
restates that bound in quantities which vanish along a sofic approximation
(Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4)).

* `sourceDefect_representingArrow_le`: on a good object the representing arrow
  misses at most twice as many source points as the overlap arrow into any
  object.  So the leakage of the representing arrows is controlled by the
  leakage along any object map, for instance the dominant targets.
* `card_hammingDisagreement_representingPatch_le_leakage`: along any object map
  `π`, the patch differs from `v` on at most the uncovered mass, twice the
  leakage along `π`, and twice the mass of the objects outside `overlapGood v`.
* `mul_sum_card_compl_overlapGood_le`: if every object has at most `K * scale`
  points, `h / 2` times the mass outside `overlapGood v` is at most `K` times
  the total forward and inverse defect along `π`.
-/

namespace GroupApproximation

universe u

namespace PartialClusterSystem

open BlockPatching FinitePartialBijection

variable {I : Type u} [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
variable (D : PartialClusterSystem I L) {Y : FiniteModel} (ι : ∀ X, D.model X → Y)
  (hinj : ∀ X, Function.Injective (ι X))
  (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')

/-- Overlap arrows of `v` out of one object into different objects have
disjoint sources. -/
theorem disjoint_clusterOverlap_source (v : Equiv.Perm Y) (X : I) {Z Z' : I}
    (hne : Z ≠ Z') :
    Disjoint (D.clusterOverlap ι hinj hdisj v X Z).source
      (D.clusterOverlap ι hinj hdisj v X Z').source := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨z, hz⟩ := (clusterEmbedding D ι hinj hdisj).mem_overlapSource.mp hx
  obtain ⟨z', hz'⟩ := (clusterEmbedding D ι hinj hdisj).mem_overlapSource.mp hx'
  exact hne (hdisj Z Z' z z' (hz.symm.trans hz'))

/-- **Leakage of the representing arrows.**  On a good object the representing
arrow misses at most twice as many source points as the overlap arrow into any
object. -/
theorem sourceDefect_representingArrow_le {v : Equiv.Perm Y} {X : I}
    (hX : X ∈ D.overlapGood ι hinj hdisj v) (Z : I) :
    (D.representingArrow ι hinj hdisj v X).sourceDefect ≤
      2 * (D.clusterOverlap ι hinj hdisj v X Z).sourceDefect := by
  have hcand := D.representingArrow_isClusterCandidate ι hinj hdisj v X
  rw [D.representingArrow_of_mem ι hinj hdisj hX] at hcand ⊢
  have hself := hcand.selfSmall
  have hsize := D.size X
  by_cases hZ : D.representingPerm ι hinj hdisj v X = Z
  · rw [hZ]
    omega
  · have hd := D.disjoint_clusterOverlap_source ι hinj hdisj v X hZ
    have hunion := Finset.card_union_of_disjoint hd
    have hle := Finset.card_le_univ
      ((D.clusterOverlap ι hinj hdisj v X (D.representingPerm ι hinj hdisj v X)).source ∪
        (D.clusterOverlap ι hinj hdisj v X Z).source)
    have h₁ := Finset.card_le_univ
      (D.clusterOverlap ι hinj hdisj v X (D.representingPerm ι hinj hdisj v X)).source
    have h₂ := Finset.card_le_univ (D.clusterOverlap ι hinj hdisj v X Z).source
    unfold FinitePartialBijection.sourceDefect at hself ⊢
    omega

/-- **End-to-end Hamming bound.**  Along any object map `π`, the patched
representing arrows differ from `v` on at most the uncovered mass, twice the
leakage of the overlap arrows along `π`, and twice the mass of the objects
outside `overlapGood v`. -/
theorem card_hammingDisagreement_representingPatch_le_leakage [DecidableEq I]
    (v : Equiv.Perm Y) (π : I → I) :
    (hammingDisagreement (D.representingArrows ι hinj hdisj v).patch v).card ≤
      (clusterEmbedding D ι hinj hdisj).uncovered.card +
        2 * ∑ X, (D.clusterOverlap ι hinj hdisj v X (π X)).sourceDefect +
        2 * ∑ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ, Fintype.card (D.model X) := by
  have h₁ := D.card_hammingDisagreement_representingPatch_le ι hinj hdisj v
  have h₂ : (Finset.univ \ (D.representingArrows ι hinj hdisj v).domain).card ≤
      (clusterEmbedding D ι hinj hdisj).uncovered.card +
        ∑ X, (D.representingArrow ι hinj hdisj v X).sourceDefect :=
    (D.representingArrows ι hinj hdisj v).card_compl_domain_le
  have hsplit : ∑ X ∈ D.overlapGood ι hinj hdisj v,
      (D.representingArrow ι hinj hdisj v X).sourceDefect +
        ∑ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ,
          (D.representingArrow ι hinj hdisj v X).sourceDefect =
      ∑ X, (D.representingArrow ι hinj hdisj v X).sourceDefect :=
    Finset.sum_add_sum_compl _ _
  have hgood : ∑ X ∈ D.overlapGood ι hinj hdisj v,
      (D.representingArrow ι hinj hdisj v X).sourceDefect ≤
        ∑ X ∈ D.overlapGood ι hinj hdisj v,
          2 * (D.clusterOverlap ι hinj hdisj v X (π X)).sourceDefect :=
    Finset.sum_le_sum fun X hX ↦ D.sourceDefect_representingArrow_le ι hinj hdisj hX (π X)
  have hgood' : ∑ X ∈ D.overlapGood ι hinj hdisj v,
      2 * (D.clusterOverlap ι hinj hdisj v X (π X)).sourceDefect ≤
        2 * ∑ X, (D.clusterOverlap ι hinj hdisj v X (π X)).sourceDefect := by
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left 2 (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) fun _ _ _ ↦ Nat.zero_le _)
  have hbad : ∑ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ,
      (D.representingArrow ι hinj hdisj v X).sourceDefect ≤
        ∑ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ, Fintype.card (D.model X) :=
    Finset.sum_le_sum fun X _ ↦ Nat.sub_le _ _
  omega

/-- **Mass outside the good objects.**  If every object has at most `K * scale`
points, then `h / 2` times the mass outside `overlapGood v` is at most `K` times
the total forward and inverse defect of the overlap arrows along `π`. -/
theorem mul_sum_card_compl_overlapGood_le [DecidableEq I] (v : Equiv.Perm Y)
    (π : I → I) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ X, (Fintype.card (D.model X) : ℝ) ≤ K * D.scale) :
    D.h / 2 * ∑ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ, (Fintype.card (D.model X) : ℝ) ≤
      K * (∑ X, (((D.clusterOverlap ι hinj hdisj v X (π X)).equivarianceDefect
          (D.act X) (D.act (π X))).card : ℝ) +
        ∑ X, (((D.clusterOverlap ι hinj hdisj v X (π X)).symm.equivarianceDefect
          (D.act (π X)) (D.act X)).card : ℝ)) := by
  have hmass : ∑ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ, (Fintype.card (D.model X) : ℝ) ≤
      ((D.overlapGood ι hinj hdisj v)ᶜ.card : ℝ) * (K * D.scale) := by
    calc ∑ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ, (Fintype.card (D.model X) : ℝ)
        ≤ ∑ _X ∈ (D.overlapGood ι hinj hdisj v)ᶜ, K * (D.scale : ℝ) :=
          Finset.sum_le_sum fun X _ ↦ hK X
      _ = ((D.overlapGood ι hinj hdisj v)ᶜ.card : ℝ) * (K * D.scale) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcount := D.card_compl_overlapGood_mul_le ι hinj hdisj v π
  have hh : 0 ≤ D.h / 2 := div_nonneg D.h_pos.le (by norm_num)
  calc D.h / 2 * ∑ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ, (Fintype.card (D.model X) : ℝ)
      ≤ D.h / 2 * (((D.overlapGood ι hinj hdisj v)ᶜ.card : ℝ) * (K * D.scale)) :=
        mul_le_mul_of_nonneg_left hmass hh
    _ = K * (((D.overlapGood ι hinj hdisj v)ᶜ.card : ℝ) * (D.h * D.scale / 2)) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcount hK0

end PartialClusterSystem
end GroupApproximation
