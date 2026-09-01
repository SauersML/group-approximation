import GroupApproximation.GGT.DGOTheorem442BBFStandardWalk

/-!
# Moving across one BBF projection-graph edge

This file proves the quantitative core of Bestvina--Bromberg--Fujiwara's
move-bound lemma preceding their nested-guards argument.  If `X₀` and `X₁`
are adjacent while `W` is not adjacent to `X₀`, then

`d_W(X₀,X₁) ≤ 4ξ`.

The bound is independent of the graph threshold `K`.  A blocker `Y` for the
non-edge `(X₀,W)` would, by monotonicity, also block `(X₀,X₁)` if the
displayed projection were larger.  The exceptional possibility `Y = X₁`
is excluded by the strengthened Behrstock estimate.

The coarse triangle inequality then shows that projection to `W` changes by
at most `8ξ` across the edge, uniformly in `K`.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

universe u

variable {V : Type u}

/-- **BBF move bound.**  An edge viewed from a vertex at graph distance at
least two has modified projection at most `4ξ`.  The distance hypothesis is
written as distinctness plus non-adjacency, which is exactly its graph-theoretic
content. -/
theorem bbfProjDist_le_four_mul_of_adj_of_not_adj
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X₀ X₁ W : V}
    (h01 : ((ProjectionPerturbation.bbf P).graph K).Adj X₀ X₁)
    (h0W : X₀ ≠ W)
    (hnot : ¬ ((ProjectionPerturbation.bbf P).graph K).Adj X₀ W) :
    P.bbfProjDist W X₀ X₁ ≤ 4 * P.ξ := by
  by_contra hbound
  have hlarge : 4 * P.ξ < P.bbfProjDist W X₀ X₁ :=
    lt_of_not_ge hbound
  have hWX₀ : W ≠ X₀ := h0W.symm
  have hWX₁ : W ≠ X₁ := by
    intro hWX₁
    subst W
    exact hnot h01
  have hblockers :
      (ProjectionPerturbation.bbf P).blockers K X₀ W ≠ ∅ := by
    intro hempty
    apply hnot
    exact (ProjectionPerturbation.graph_adj_iff_blockers_eq_empty
      (ProjectionPerturbation.bbf P) K X₀ W).mpr ⟨h0W, hempty⟩
  obtain ⟨Y, hY⟩ :
      ((ProjectionPerturbation.bbf P).blockers K X₀ W).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hblockers
  have hend := P.bbfProjDist_endpoints_lt hWX₀ hWX₁ h01.ne (by
    linarith [hlarge, P.ξ_pos])
  have hYX₁ : Y ≠ X₁ := by
    intro hYX₁
    subst Y
    linarith [hY.2.2, hend.2, hK, P.ξ_pos]
  have hmono := P.bbfProjDist_left_mono hY.1 hY.2.1 hYX₁
    hWX₀ hWX₁ h01.ne hlarge
  have hadjBound : P.bbfProjDist Y X₀ X₁ ≤ K := by
    have h01' := (ProjectionPerturbation.graph_adj_iff _ K X₀ X₁).mp h01
    exact h01'.2 Y hY.1 hYX₁
  linarith [hY.2.2, hmono, hadjBound]

/-- Projection to `W` changes by at most `8ξ` across an edge which stays at
graph distance at least two from `W`.  This is the second assertion of BBF's
move-bound lemma with an explicit constant. -/
theorem abs_bbfProjDist_sub_le_eight_mul_of_adj_of_not_adj
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X₀ X₁ W Z : V}
    (h01 : ((ProjectionPerturbation.bbf P).graph K).Adj X₀ X₁)
    (h0W : X₀ ≠ W)
    (hnot : ¬ ((ProjectionPerturbation.bbf P).graph K).Adj X₀ W)
    (hWZ : W ≠ Z) (h0Z : X₀ ≠ Z) (h1Z : X₁ ≠ Z) :
    |P.bbfProjDist W X₀ Z - P.bbfProjDist W X₁ Z| ≤ 8 * P.ξ := by
  have hWX₀ : W ≠ X₀ := h0W.symm
  have hWX₁ : W ≠ X₁ := by
    intro hWX₁
    subst W
    exact hnot h01
  have hstep := P.bbfProjDist_le_four_mul_of_adj_of_not_adj
    hK h01 h0W hnot
  have htri₀ := P.bbfProjDist_triangle hWX₀ hWX₁ hWZ
    h01.ne h1Z h0Z
  have htri₁ := P.bbfProjDist_triangle hWX₁ hWX₀ hWZ
    h01.ne.symm h0Z h1Z
  rw [P.bbfProjDist_comm W X₁ X₀] at htri₁
  rw [abs_le]
  constructor <;> linarith [hstep, htri₀, htri₁]

end ProjectionSystem
end GGT
end GroupApproximation
