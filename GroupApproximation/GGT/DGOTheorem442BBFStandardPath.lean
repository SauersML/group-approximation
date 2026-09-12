import GroupApproximation.GGT.DGOTheorem442BBFOrder
import GroupApproximation.GGT.DGOTheorem442BBFConnectedness

/-!
# Consecutive large projections form the BBF standard path

This file proves the edge step in Bestvina--Bromberg--Fujiwara Proposition
3.7.  At a threshold `K ≥ 12ξ`, the large projections of `(X,Z)` are
ordered by

`W < U  ↔  5ξ < d_W(X,U)`.

If `Y₀ < Y₁` and no other large projection lies strictly between them,
then `Y₀` and `Y₁` are adjacent in the projection graph.  The key point
is that a blocker for this edge is itself a large projection of `(X,Z)`.
Order totality then places it either between the proposed consecutive
vertices or outside them; the two outside cases have projection below `ξ`.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

universe u

variable {V : Type u}

/-- The endpoint pair of the BBF order is distinct whenever its large
projection set is nonempty. -/
theorem ne_of_mem_bbf_blockers
    (P : ProjectionSystem V) {K : ℝ} (hK : 0 ≤ K) {X Z Y : V}
    (hY : Y ∈ (ProjectionPerturbation.bbf P).blockers K X Z) :
    X ≠ Z := by
  change Y ≠ X ∧ Y ≠ Z ∧ K < P.bbfProjDist Y X Z at hY
  intro hXZ
  subst Z
  have hzero : P.bbfProjDist Y X X = 0 := by
    rw [bbfProjDist, bbfRawProjDist,
      if_pos (Or.inr (Or.inr (Or.inl rfl)))]
  have hlarge : K < P.bbfProjDist Y X X := hY.2.2
  rw [hzero] at hlarge
  exact (not_lt_of_ge hK) hlarge

/-- If `W < U` in the large-projection order of `(X,Z)`, then the three
other comparisons used in BBF Theorem 3.3(G) follow with explicit constants:
`d_U(X,W) < ξ`, `K - 5ξ < d_U(W,Z)`, and `d_W(U,Z) < ξ`. -/
theorem bbf_before_consequences
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z W U : V}
    (hW : W ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hU : U ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hWU : W ≠ U)
    (hbefore : 5 * P.ξ < P.bbfProjDist W X U) :
    P.bbfProjDist U X W < P.ξ ∧
      K - 5 * P.ξ < P.bbfProjDist U W Z ∧
      P.bbfProjDist W U Z < P.ξ := by
  change W ≠ X ∧ W ≠ Z ∧ K < P.bbfProjDist W X Z at hW
  change U ≠ X ∧ U ≠ Z ∧ K < P.bbfProjDist U X Z at hU
  have hXZ : X ≠ Z := P.ne_of_mem_bbf_blockers (by
    linarith [hK, P.ξ_pos]) hW
  have hendXU := P.bbfProjDist_endpoints_lt hW.1 hWU hU.1.symm (by
    linarith [hbefore, P.ξ_pos])
  have htri := P.bbfProjDist_triangle hU.1 hWU.symm hU.2.1
    hW.1.symm hW.2.1 hXZ
  have hUWZ : K - 5 * P.ξ < P.bbfProjDist U W Z := by
    linarith [hU.2.2, hendXU.2]
  have hUWZlarge : 2 * P.ξ < P.bbfProjDist U W Z := by
    linarith [hUWZ, hK, P.ξ_pos]
  have hendWZ := P.bbfProjDist_endpoints_lt hWU.symm hU.2.1
    hW.2.1 hUWZlarge
  exact ⟨hendXU.2, hUWZ, hendWZ.1⟩

/-- A large projection strictly to the left of two ordered large projections
sees their pair with modified projection below `ξ`.  This is the first
outer-vertex estimate in BBF Theorem 3.3(G). -/
theorem bbf_before_before_projDist_lt
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z W Y₀ Y₁ : V}
    (hW : W ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hY₀ : Y₀ ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hY₁ : Y₁ ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hWY₀ : W ≠ Y₀) (hY₀Y₁ : Y₀ ≠ Y₁) (hWY₁ : W ≠ Y₁)
    (hWY₀before : 5 * P.ξ < P.bbfProjDist W X Y₀)
    (hY₀Y₁before : 5 * P.ξ < P.bbfProjDist Y₀ X Y₁) :
    P.bbfProjDist W Y₀ Y₁ < P.ξ := by
  change W ≠ X ∧ W ≠ Z ∧ K < P.bbfProjDist W X Z at hW
  change Y₀ ≠ X ∧ Y₀ ≠ Z ∧ K < P.bbfProjDist Y₀ X Z at hY₀
  change Y₁ ≠ X ∧ Y₁ ≠ Z ∧ K < P.bbfProjDist Y₁ X Z at hY₁
  have hfirst := P.bbf_before_consequences hK hW hY₀ hWY₀ hWY₀before
  have hsecond :=
    P.bbf_before_consequences hK hY₀ hY₁ hY₀Y₁ hY₀Y₁before
  have htri := P.bbfProjDist_triangle hWY₀.symm hY₀Y₁ hY₀.2.1
    hWY₁ hY₁.2.1 hW.2.1
  have hmiddle : 2 * P.ξ < P.bbfProjDist Y₀ W Y₁ := by
    linarith [hfirst.2.1, hsecond.2.2, hK, P.ξ_pos]
  have hend := P.bbfProjDist_endpoints_lt hWY₀.symm hY₀Y₁
    hWY₁ hmiddle
  exact hend.1

/-- The symmetric outer-vertex estimate: a large projection strictly to the
right of two ordered large projections also sees their pair below `ξ`. -/
theorem bbf_projDist_lt_of_before_before
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z Y₀ Y₁ W : V}
    (hY₀ : Y₀ ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hY₁ : Y₁ ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hW : W ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hY₀Y₁ : Y₀ ≠ Y₁) (hY₁W : Y₁ ≠ W) (hY₀W : Y₀ ≠ W)
    (hY₀Y₁before : 5 * P.ξ < P.bbfProjDist Y₀ X Y₁)
    (hY₁Wbefore : 5 * P.ξ < P.bbfProjDist Y₁ X W) :
    P.bbfProjDist W Y₀ Y₁ < P.ξ := by
  change Y₀ ≠ X ∧ Y₀ ≠ Z ∧ K < P.bbfProjDist Y₀ X Z at hY₀
  change Y₁ ≠ X ∧ Y₁ ≠ Z ∧ K < P.bbfProjDist Y₁ X Z at hY₁
  change W ≠ X ∧ W ≠ Z ∧ K < P.bbfProjDist W X Z at hW
  have hfirst :=
    P.bbf_before_consequences hK hY₀ hY₁ hY₀Y₁ hY₀Y₁before
  have hsecond := P.bbf_before_consequences hK hY₁ hW hY₁W hY₁Wbefore
  have hXZ : X ≠ Z := P.ne_of_mem_bbf_blockers (by
    linarith [hK, P.ξ_pos]) hY₀
  have htriXZ := P.bbfProjDist_triangle hY₁.1 hY₁W hY₁.2.1
    hW.1.symm hW.2.1 hXZ
  have hXW : K - 5 * P.ξ < P.bbfProjDist Y₁ X W := by
    linarith [hY₁.2.2, hsecond.2.2]
  have htri := P.bbfProjDist_triangle hY₁.1 hY₀Y₁.symm hY₁W
    hY₀.1.symm hY₀W hW.1.symm
  have hmiddle : 2 * P.ξ < P.bbfProjDist Y₁ Y₀ W := by
    linarith [hXW, hfirst.1, hK, P.ξ_pos]
  have hend := P.bbfProjDist_endpoints_lt hY₀Y₁.symm hY₁W hY₀W hmiddle
  exact hend.2

/-- Every blocker of an ordered candidate edge is also a blocker of the
original endpoint pair.  This is the inclusion used in the standard-path
proof of BBF Proposition 3.7. -/
theorem bbf_blocker_of_ordered_pair_mem
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z Y₀ Y₁ W : V}
    (hY₀ : Y₀ ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hY₁ : Y₁ ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hY₀Y₁ : Y₀ ≠ Y₁)
    (hbefore : 5 * P.ξ < P.bbfProjDist Y₀ X Y₁)
    (hW : W ∈ (ProjectionPerturbation.bbf P).blockers K Y₀ Y₁) :
    W ∈ (ProjectionPerturbation.bbf P).blockers K X Z := by
  change Y₀ ≠ X ∧ Y₀ ≠ Z ∧ K < P.bbfProjDist Y₀ X Z at hY₀
  change Y₁ ≠ X ∧ Y₁ ≠ Z ∧ K < P.bbfProjDist Y₁ X Z at hY₁
  change W ≠ Y₀ ∧ W ≠ Y₁ ∧ K < P.bbfProjDist W Y₀ Y₁ at hW
  change W ≠ X ∧ W ≠ Z ∧ K < P.bbfProjDist W X Z
  have hXZ : X ≠ Z := P.ne_of_mem_bbf_blockers (by
    linarith [hK, P.ξ_pos]) hY₀
  have hendXY := P.bbfProjDist_endpoints_lt hY₀.1 hY₀Y₁ hY₁.1.symm (by
    linarith [hbefore, P.ξ_pos])
  have hWneX : W ≠ X := by
    intro hWX
    subst W
    linarith [hW.2.2, hendXY.1, hK, P.ξ_pos]
  have hY₁YZ :=
    (P.bbf_before_consequences hK hY₀ hY₁ hY₀Y₁ hbefore).2.1
  have hY₁large : 4 * P.ξ < P.bbfProjDist Y₁ Y₀ Z := by
    linarith [hY₁YZ, hK, P.ξ_pos]
  have hendYZ := P.bbfProjDist_endpoints_lt hY₀Y₁.symm hY₁.2.1
    hY₀.2.1 (by linarith [hY₁large, P.ξ_pos])
  have hWneZ : W ≠ Z := by
    intro hWZ
    subst W
    linarith [hW.2.2, hendYZ.2, hK, P.ξ_pos]
  refine ⟨hWneX, hWneZ, ?_⟩
  have hY₁Y₀ : Y₁ ≠ Y₀ := hY₀Y₁.symm
  have hleft := P.bbfProjDist_left_mono hW.1 hW.2.1 hWneZ
    hY₁Y₀ hY₁.2.1 hY₀.2.1 hY₁large
  have hY₀large : 4 * P.ξ < P.bbfProjDist Y₀ X Z := by
    linarith [hY₀.2.2, hK, P.ξ_pos]
  have hright := P.bbfProjDist_right_mono hWneX hW.1 hWneZ
    hY₀.1 hY₀.2.1 hXZ hY₀large
  rw [P.bbfProjDist_comm W Z Y₀] at hright
  exact hW.2.2.trans_le (hleft.trans hright)

/-- **The edge step of the BBF standard path.**  Consecutive vertices in the
large-projection order are adjacent in the projection graph. -/
theorem bbf_graph_adj_of_consecutive
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z Y₀ Y₁ : V}
    (hY₀ : Y₀ ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hY₁ : Y₁ ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hY₀Y₁ : Y₀ ≠ Y₁)
    (hbefore : 5 * P.ξ < P.bbfProjDist Y₀ X Y₁)
    (hconsecutive : ∀ W,
      W ∈ (ProjectionPerturbation.bbf P).blockers K X Z →
      W ≠ Y₀ → W ≠ Y₁ →
      ¬ (5 * P.ξ < P.bbfProjDist Y₀ X W ∧
        5 * P.ξ < P.bbfProjDist W X Y₁)) :
    ((ProjectionPerturbation.bbf P).graph K).Adj Y₀ Y₁ := by
  change Y₀ ≠ X ∧ Y₀ ≠ Z ∧ K < P.bbfProjDist Y₀ X Z at hY₀
  change Y₁ ≠ X ∧ Y₁ ≠ Z ∧ K < P.bbfProjDist Y₁ X Z at hY₁
  rw [ProjectionPerturbation.graph_adj_iff_blockers_eq_empty]
  refine ⟨hY₀Y₁, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro W hW
  change W ≠ Y₀ ∧ W ≠ Y₁ ∧ K < P.bbfProjDist W Y₀ Y₁ at hW
  have hWlarge := P.bbf_blocker_of_ordered_pair_mem hK hY₀ hY₁
    hY₀Y₁ hbefore hW
  change W ≠ X ∧ W ≠ Z ∧ K < P.bbfProjDist W X Z at hWlarge
  have hY₀W : Y₀ ≠ W := hW.1.symm
  have hWY₁ : W ≠ Y₁ := hW.2.1
  have hleft := P.bbf_before_total_on_large hK hY₀.1 hY₀.2.1
    hWlarge.1 hWlarge.2.1 hY₀W hY₀.2.2 hWlarge.2.2
  have hright := P.bbf_before_total_on_large hK hWlarge.1 hWlarge.2.1
    hY₁.1 hY₁.2.1 hWY₁ hWlarge.2.2 hY₁.2.2
  rcases hleft with hY₀Wbefore | hWY₀before
  · rcases hright with hWY₁before | hY₁Wbefore
    · exact hconsecutive W hWlarge hY₀W.symm hWY₁
        ⟨hY₀Wbefore, hWY₁before⟩
    · have hsmall := P.bbf_projDist_lt_of_before_before hK hY₀ hY₁
        hWlarge hY₀Y₁ hWY₁.symm hY₀W hbefore hY₁Wbefore
      linarith [hW.2.2, hsmall, hK, P.ξ_pos]
  · have hsmall := P.bbf_before_before_projDist_lt hK hWlarge hY₀ hY₁
      hY₀W.symm hY₀Y₁ hWY₁ hWY₀before hbefore
    linarith [hW.2.2, hsmall, hK, P.ξ_pos]

/-- The first vertex of the ordered large-projection set is adjacent to the
left endpoint.  This supplies the initial edge of the standard path in BBF
Proposition 3.7. -/
theorem bbf_graph_adj_left_endpoint_of_minimal
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z Y : V}
    (hY : Y ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hminimal : ∀ W,
      W ∈ (ProjectionPerturbation.bbf P).blockers K X Z →
      W ≠ Y → ¬ 5 * P.ξ < P.bbfProjDist W X Y) :
    ((ProjectionPerturbation.bbf P).graph K).Adj X Y := by
  change Y ≠ X ∧ Y ≠ Z ∧ K < P.bbfProjDist Y X Z at hY
  rw [ProjectionPerturbation.graph_adj_iff_blockers_eq_empty]
  refine ⟨hY.1.symm, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro W hW
  change W ≠ X ∧ W ≠ Y ∧ K < P.bbfProjDist W X Y at hW
  have hKfour : 4 * P.ξ ≤ K := by linarith [hK, P.ξ_pos]
  have hWlarge := P.bbf_blockers_left_subset hKfour hY hW
  change W ≠ X ∧ W ≠ Z ∧ K < P.bbfProjDist W X Z at hWlarge
  have hWY : W ≠ Y := hW.2.1
  apply hminimal W hWlarge hWY
  linarith [hW.2.2, hK, P.ξ_pos]

/-- The last vertex of the ordered large-projection set is adjacent to the
right endpoint.  This supplies the final edge of the standard path in BBF
Proposition 3.7. -/
theorem bbf_graph_adj_right_endpoint_of_maximal
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z Y : V}
    (hY : Y ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hmaximal : ∀ W,
      W ∈ (ProjectionPerturbation.bbf P).blockers K X Z →
      W ≠ Y → ¬ 5 * P.ξ < P.bbfProjDist Y X W) :
    ((ProjectionPerturbation.bbf P).graph K).Adj Y Z := by
  change Y ≠ X ∧ Y ≠ Z ∧ K < P.bbfProjDist Y X Z at hY
  rw [ProjectionPerturbation.graph_adj_iff_blockers_eq_empty]
  refine ⟨hY.2.1, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro W hW
  change W ≠ Y ∧ W ≠ Z ∧ K < P.bbfProjDist W Y Z at hW
  have hKfour : 4 * P.ξ ≤ K := by linarith [hK, P.ξ_pos]
  have hWlarge := P.bbf_blockers_right_subset hKfour hY hW
  change W ≠ X ∧ W ≠ Z ∧ K < P.bbfProjDist W X Z at hWlarge
  have hWY : W ≠ Y := hW.1
  have htotal := P.bbf_before_total_on_large hK hY.1 hY.2.1
    hWlarge.1 hWlarge.2.1 hWY.symm hY.2.2 hWlarge.2.2
  rcases htotal with hYWbefore | hWYbefore
  · exact hmaximal W hWlarge hWY hYWbefore
  · have hsmall :=
      (P.bbf_before_consequences hK hWlarge hY hWY hWYbefore).2.2
    linarith [hW.2.2, hsmall, hK, P.ξ_pos]

end ProjectionSystem
end GGT
end GroupApproximation
