import GroupApproximation.KunThom.CentralizerBisectionRepresentation
import GroupApproximation.KunThom.CentralizerBisectionRepresentationCharges
import GroupApproximation.KunThom.ScaledBisectionConverse

/-!
# The patched bisection representing a permutation, on a scaled cluster system

Forward half of Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4), finite form.  Let `D` be a
`ScaledPartialClusterSystem` placed disjointly in a model `Y`, `act` an ambient labelled
action and `q` a permutation of `Y`.  Let `b` be a total bisection of the cluster groupoid
completing the selected arrows of `q` (`exists_bisection_selected`).  Suppose the block
actions have tagged expansion at a fixed level `c > 0` and scale `1`.

`mul_card_hammingDisagreement_scaledBisectionPatch_le` bounds `c² h` times the Hamming
disagreement of the patched bisection with `q` by:
* the uncovered mass;
* the candidate threshold total `h |Y| / 36`;
* the piece charges and local obstructions of `q` and `q⁻¹`.

`CentralizerBisectionRepresentationCharges` bounds those by the uncovered mass, the
commutation failures of `q` and the compatibility failures.

The ingredients are:
* `card_model_le_of_two_mul_card_bridgeSource_scaled`: a two-sided majority bounds a
  block by `38` times the pair scale;
* `sum_card_equivarianceDefect_scaledBisectionArrows_le`: the arrows of a bisection
  have total defect at most `h |Y| / 36`;
* `mul_card_equivarianceDefect_bridge_selected_le`: at a selected object the bridge into
  the completed target has defect at most `|L|` piece charges plus the obstructions.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection CategoryTheory

universe u

variable {Y : FiniteModel} {I : Type u}

section Scaled

variable [Fintype I] {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
variable (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
  (hinj : ∀ X, Function.Injective (ι X))
  (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')

/-- **A majority piece bounds the block by the pair scale.** -/
theorem card_model_le_of_two_mul_card_bridgeSource_scaled (q : Equiv.Perm Y) {C X : I}
    (hC : Fintype.card (D.model C) <
      2 * ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q C X).source.card) :
    (Fintype.card (D.model C) : ℝ) ≤ 38 * ((min (D.scale C) (D.scale X) : ℕ) : ℝ) := by
  have hW : ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q C X).source.card ≤
      Fintype.card (D.model C) := Finset.card_le_univ _
  have hW' : ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q C X).target.card ≤
      Fintype.card (D.model X) := Finset.card_le_univ _
  have heq := ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q C
    X).card_source_eq_card_target
  have hsC := D.scale_eq C
  have hsX := D.scale_eq X
  have hlC := D.scale_large C
  have hlX := D.scale_large X
  have hnat : Fintype.card (D.model C) ≤ 38 * min (D.scale C) (D.scale X) := by
    omega
  exact_mod_cast hnat

/-- **The arrows of a bisection have small total defect.** -/
theorem sum_card_equivarianceDefect_scaledBisectionArrows_le
    (b : FiniteGroupoid.Bisection D.presentation.Obj) :
    ∑ X, ((((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
      ).equivarianceDefect (D.act X)
        (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) ≤
      D.h / 36 * Fintype.card Y := by
  have hτ : ∀ X, ((((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
      ).equivarianceDefect (D.act X)
        (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) ≤
      D.h * ((Fintype.card (D.model X) / 18 : ℕ) : ℝ) / 2 := by
    intro X
    have hcand : ((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
        ).IsClusterCandidate (D.act X)
          (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X)) D.h
          (min (D.scale X) (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X))) :=
      scaledBisectionArrows_isClusterCandidate D ι hinj hdisj b X
    have hmin : ((min (D.scale X)
        (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X)) : ℕ) : ℝ) ≤
        ((Fintype.card (D.model X) / 18 : ℕ) : ℝ) := by
      rw [← D.scale_eq X]
      exact_mod_cast min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_left hmin D.h_pos.le
    exact hcand.forwardSmall.le.trans (div_le_div_of_nonneg_right hmul (by norm_num))
  exact (Finset.sum_le_sum fun X _ ↦ hτ X).trans
    ((scaledClusterEmbedding D.clusterData ι hinj hdisj).sum_scaleThreshold_le D.h_pos.le)

/-- **The bridge at a selected object.**  Its defect is at most `|L|` times the piece
charge of the object plus the local obstructions there. -/
theorem mul_card_equivarianceDefect_bridge_selected_le (act : L → Equiv.Perm Y)
    (q : Equiv.Perm Y) (b : FiniteGroupoid.Bisection D.presentation.Obj)
    (hb : ∀ X (hX : X ∈ selectedObjects D ι hinj hdisj q),
      ∃ e : b.objEquiv X = selectedObjectTarget D ι hinj hdisj q X,
        b.hom X ≫ eqToHom e = selectedArrow D ι hinj hdisj q X hX)
    {c : ℝ} (hc : 0 ≤ c) (hexp : ∀ X, HasTaggedExpansionAtScale (D.act X) c 1) {X : I}
    (hX : (⟨X⟩ : D.presentation.Obj) ∈ selectedObjects D ι hinj hdisj q) :
    c * ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
        (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
          (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) ≤
      Fintype.card L *
          (scaledClusterAction (D := D.clusterData) ι hinj hdisj act D.act).pieceCharge q c X +
        c * (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
          D.act).obstructionMass q X := by
  obtain ⟨e, he⟩ := hb ⟨X⟩ hX
  obtain ⟨hcand₀, -⟩ := hom_eq_ofRep_bridge D ι hinj hdisj q hX (b.hom ⟨X⟩) e he
  have hcand : ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
      (scaledBisectionIndexEquiv (D := D.clusterData) b X)).IsClusterCandidate (D.act X)
        (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X)) D.h
        (min (D.scale X) (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X))) :=
    hcand₀
  have hself := hcand.selfSmall
  have hsX := D.scale_eq X
  have hsrc : ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
      (scaledBisectionIndexEquiv (D := D.clusterData) b X)).source.card ≤
        Fintype.card (D.model X) := Finset.card_le_univ _
  have hmaj : Fintype.card ((scaledClusterEmbedding D.clusterData ι hinj hdisj).model X) <
      2 * ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
        (scaledBisectionIndexEquiv (D := D.clusterData) b X)).source.card := by
    have hmin : min (D.scale X) (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X))
        ≤ D.scale X := min_le_left _ _
    have hsd : Fintype.card (D.model X) - ((scaledClusterEmbedding D.clusterData ι hinj
        hdisj).bridge q X (scaledBisectionIndexEquiv (D := D.clusterData) b X)).source.card <
          2 * min (D.scale X) (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X)) :=
      lt_of_le_of_lt (Nat.le_add_right _ _) hself
    have hlX := D.scale_large X
    show Fintype.card (D.model X) < _
    omega
  have hdom := (scaledClusterEmbedding D.clusterData ι hinj hdisj).dominant_of_two_mul_card_bridgeSource_gt
    q hmaj
  have hsd := (scaledClusterAction (D := D.clusterData) ι hinj hdisj act D.act).mul_sourceDefect_dominant_le
    q X hc (hexp X) hdom
  have hfwd := (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
    D.act).card_equivarianceDefect_bridge_le_localObstruction q X
      (scaledBisectionIndexEquiv (D := D.clusterData) b X)
  have hfwd' : ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
        (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
          (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) ≤
      (Fintype.card L : ℝ) * (((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
        (scaledBisectionIndexEquiv (D := D.clusterData) b X)).sourceDefect : ℝ) +
        (scaledClusterAction (D := D.clusterData) ι hinj hdisj act D.act).obstructionMass q X := by
    have hcast : ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
        (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
          (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) ≤
        ∑ s : L, ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
          (scaledBisectionIndexEquiv (D := D.clusterData) b X)).sourceDefect : ℝ) +
          (((scaledClusterAction (D := D.clusterData) ι hinj hdisj act
            D.act).localObstruction q X s).card : ℝ)) := by
      exact_mod_cast hfwd
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcast
    exact hcast
  have hL : (0 : ℝ) ≤ Fintype.card L := Nat.cast_nonneg _
  calc c * ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
        (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
          (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ)
      ≤ c * ((Fintype.card L : ℝ) * (((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge
          q X (scaledBisectionIndexEquiv (D := D.clusterData) b X)).sourceDefect : ℝ) +
          (scaledClusterAction (D := D.clusterData) ι hinj hdisj act D.act).obstructionMass q X) :=
        mul_le_mul_of_nonneg_left hfwd' hc
    _ = (Fintype.card L : ℝ) * (c * (((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge
          q X (scaledBisectionIndexEquiv (D := D.clusterData) b X)).sourceDefect : ℝ)) +
          c * (scaledClusterAction (D := D.clusterData) ι hinj hdisj act D.act).obstructionMass
            q X := by
        ring
    _ ≤ Fintype.card L *
          (scaledClusterAction (D := D.clusterData) ι hinj hdisj act D.act).pieceCharge q c X +
        c * (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
          D.act).obstructionMass q X :=
        add_le_add (mul_le_mul_of_nonneg_left hsd hL) le_rfl

end Scaled

end BlockPatching
end GroupApproximation
