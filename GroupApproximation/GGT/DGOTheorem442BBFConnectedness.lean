import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import GroupApproximation.GGT.DGOTheorem442BBFMonotonicity
import GroupApproximation.GGT.DGOTheorem442ProjectionComplex

/-!
# Connectedness of the BBF projection graph

This file proves BBF Proposition 3.7, the connectedness of the projection
graph.  A blocker `Y` for `(X,Z)` splits the problem into `(X,Y)` and `(Y,Z)`.
Monotonicity makes both new blocker sets proper subsets of the old finite
blocker set, so induction on its cardinality supplies the two paths.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

universe u

variable {V : Type u}

/-- A large projection at `Y` makes every blocker between `X` and `Y` a
blocker between `X` and `Z`.  The possible exceptional vertex `Z` is excluded
by the endpoint-smallness estimate. -/
theorem bbf_blockers_left_subset
    (P : ProjectionSystem V) {K : ℝ} (hK : 4 * P.ξ ≤ K)
    {X Z Y : V}
    (hY : Y ∈ (ProjectionPerturbation.bbf P).blockers K X Z) :
    (ProjectionPerturbation.bbf P).blockers K X Y ⊆
      (ProjectionPerturbation.bbf P).blockers K X Z := by
  intro W hW
  have hYX : Y ≠ X := hY.1
  have hYZ : Y ≠ Z := hY.2.1
  have hXZ : X ≠ Z := by
    intro hXZ'
    subst Z
    have hzero : P.bbfProjDist Y X X = 0 := by
      rw [bbfProjDist, bbfRawProjDist,
        if_pos (Or.inr (Or.inr (Or.inl rfl)))]
    have hdist : K < P.bbfProjDist Y X X := hY.2.2
    rw [hzero] at hdist
    linarith [P.ξ_pos]
  have hlarge : 4 * P.ξ < P.bbfProjDist Y X Z := by
    linarith [hY.2.2]
  have hWZ : W ≠ Z := by
    intro hWZ'
    subst W
    have hend := P.bbfProjDist_endpoints_lt hYX hYZ hXZ (by
      linarith [hY.2.2, P.ξ_pos])
    linarith [hW.2.2, hend.2, P.ξ_pos]
  refine ⟨hW.1, hWZ, ?_⟩
  have hmono := P.bbfProjDist_left_mono hW.1 hW.2.1 hWZ
    hYX hYZ hXZ hlarge
  linarith [hW.2.2]

/-- The left blocker set in the blocker split is a proper subset: the
splitting vertex `Y` belongs to the old set and cannot belong to a blocker set
having `Y` as an endpoint. -/
theorem bbf_blockers_left_ssubset
    (P : ProjectionSystem V) {K : ℝ} (hK : 4 * P.ξ ≤ K)
    {X Z Y : V}
    (hY : Y ∈ (ProjectionPerturbation.bbf P).blockers K X Z) :
    (ProjectionPerturbation.bbf P).blockers K X Y ⊂
      (ProjectionPerturbation.bbf P).blockers K X Z := by
  rw [Set.ssubset_iff_exists]
  refine ⟨P.bbf_blockers_left_subset hK hY, Y, hY, ?_⟩
  intro h
  exact h.2.1 rfl

/-- The symmetric half of the blocker split. -/
theorem bbf_blockers_right_subset
    (P : ProjectionSystem V) {K : ℝ} (hK : 4 * P.ξ ≤ K)
    {X Z Y : V}
    (hY : Y ∈ (ProjectionPerturbation.bbf P).blockers K X Z) :
    (ProjectionPerturbation.bbf P).blockers K Y Z ⊆
      (ProjectionPerturbation.bbf P).blockers K X Z := by
  intro W hW
  have hYX : Y ≠ X := hY.1
  have hYZ : Y ≠ Z := hY.2.1
  have hXZ : X ≠ Z := by
    intro hXZ'
    subst Z
    have hzero : P.bbfProjDist Y X X = 0 := by
      rw [bbfProjDist, bbfRawProjDist,
        if_pos (Or.inr (Or.inr (Or.inl rfl)))]
    have hdist : K < P.bbfProjDist Y X X := hY.2.2
    rw [hzero] at hdist
    linarith [P.ξ_pos]
  have hlarge : 4 * P.ξ < P.bbfProjDist Y X Z := by
    linarith [hY.2.2]
  have hWX : W ≠ X := by
    intro hWX'
    subst W
    have hend := P.bbfProjDist_endpoints_lt hYX hYZ hXZ (by
      linarith [hY.2.2, P.ξ_pos])
    linarith [hW.2.2, hend.1, P.ξ_pos]
  refine ⟨hWX, hW.2.1, ?_⟩
  have hmono := P.bbfProjDist_right_mono hWX hW.1 hW.2.1
    hYX hYZ hXZ hlarge
  rw [P.bbfProjDist_comm W Z Y] at hmono
  linarith [hW.2.2]

/-- The right blocker set in the blocker split is proper for the same endpoint
reason. -/
theorem bbf_blockers_right_ssubset
    (P : ProjectionSystem V) {K : ℝ} (hK : 4 * P.ξ ≤ K)
    {X Z Y : V}
    (hY : Y ∈ (ProjectionPerturbation.bbf P).blockers K X Z) :
    (ProjectionPerturbation.bbf P).blockers K Y Z ⊂
      (ProjectionPerturbation.bbf P).blockers K X Z := by
  rw [Set.ssubset_iff_exists]
  refine ⟨P.bbf_blockers_right_subset hK hY, Y, hY, ?_⟩
  intro h
  exact h.1 rfl

/-- Induction form of BBF Proposition 3.7.  A bound on the number of blockers
is enough to construct a walk between the endpoints. -/
theorem bbf_graph_reachable_of_blockers_ncard_le
    (P : ProjectionSystem V) {K : ℝ} (hK : 4 * P.ξ ≤ K) (n : ℕ) :
    ∀ X Z : V,
      ((ProjectionPerturbation.bbf P).blockers K X Z).ncard ≤ n →
        ((ProjectionPerturbation.bbf P).graph K).Reachable X Z := by
  induction n with
  | zero =>
      intro X Z hn
      by_cases hXZ : X = Z
      · subst Z
        exact SimpleGraph.Reachable.rfl
      · have hfin : ((ProjectionPerturbation.bbf P).blockers K X Z).Finite :=
          ProjectionPerturbation.blockers_finite _ (by linarith [P.ξ_pos]) hXZ
        have hcard : ((ProjectionPerturbation.bbf P).blockers K X Z).ncard = 0 :=
          Nat.eq_zero_of_le_zero hn
        have hempty : (ProjectionPerturbation.bbf P).blockers K X Z = ∅ :=
          (Set.ncard_eq_zero hfin).mp hcard
        have hadj : ((ProjectionPerturbation.bbf P).graph K).Adj X Z :=
          (ProjectionPerturbation.graph_adj_iff_blockers_eq_empty _ K X Z).mpr
            ⟨hXZ, hempty⟩
        exact hadj.reachable
  | succ n ih =>
      intro X Z hn
      by_cases hXZ : X = Z
      · subst Z
        exact SimpleGraph.Reachable.rfl
      · have hfin : ((ProjectionPerturbation.bbf P).blockers K X Z).Finite :=
          ProjectionPerturbation.blockers_finite _ (by linarith [P.ξ_pos]) hXZ
        by_cases hempty : (ProjectionPerturbation.bbf P).blockers K X Z = ∅
        · have hadj : ((ProjectionPerturbation.bbf P).graph K).Adj X Z :=
            (ProjectionPerturbation.graph_adj_iff_blockers_eq_empty _ K X Z).mpr
              ⟨hXZ, hempty⟩
          exact hadj.reachable
        · obtain ⟨Y, hY⟩ :
              ((ProjectionPerturbation.bbf P).blockers K X Z).Nonempty :=
            Set.nonempty_iff_ne_empty.mpr hempty
          have hleft := P.bbf_blockers_left_ssubset hK hY
          have hright := P.bbf_blockers_right_ssubset hK hY
          have hcardLeft :
              ((ProjectionPerturbation.bbf P).blockers K X Y).ncard <
                ((ProjectionPerturbation.bbf P).blockers K X Z).ncard :=
            Set.ncard_lt_ncard hleft hfin
          have hcardRight :
              ((ProjectionPerturbation.bbf P).blockers K Y Z).ncard <
                ((ProjectionPerturbation.bbf P).blockers K X Z).ncard :=
            Set.ncard_lt_ncard hright hfin
          have hleftLe :
              ((ProjectionPerturbation.bbf P).blockers K X Y).ncard ≤ n := by
            omega
          have hrightLe :
              ((ProjectionPerturbation.bbf P).blockers K Y Z).ncard ≤ n := by
            omega
          exact (ih X Y hleftLe).trans (ih Y Z hrightLe)

/-- **BBF Proposition 3.7.**  At every threshold `K ≥ 4ξ`, the projection
graph of the BBF perturbation is connected. -/
theorem bbf_graph_preconnected
    (P : ProjectionSystem V) {K : ℝ} (hK : 4 * P.ξ ≤ K) :
    ((ProjectionPerturbation.bbf P).graph K).Preconnected := by
  intro X Z
  exact P.bbf_graph_reachable_of_blockers_ncard_le hK
    (((ProjectionPerturbation.bbf P).blockers K X Z).ncard) X Z le_rfl

end ProjectionSystem

namespace Elementary

open GroupApproximation.HullGeometry

universe v w

variable {G : Type v} [Group G] {S : Type w} [PseudoMetricSpace S]
  [MulAction G S]

/-- The coset-orbit projection graph used in DGO Theorem 4.42 is connected at
every threshold at least four times its assembled projection constant. -/
theorem approxCosetProjectionComplex_preconnected
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) {K : ℝ}
    (hK : let P := approxCosetEquivariantProjectionSystem
      hδ hδ0 hδpos hgeo hiso H s hqc hsep
      4 * P.ξ ≤ K) :
    (approxCosetProjectionComplex
      hδ hδ0 hδpos hgeo hiso H s hqc hsep K).Preconnected := by
  let P := approxCosetEquivariantProjectionSystem
    hδ hδ0 hδpos hgeo hiso H s hqc hsep
  exact P.toProjectionSystem.bbf_graph_preconnected hK

end Elementary
end GGT
end GroupApproximation
