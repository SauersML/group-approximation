import GroupApproximation.GGT.DGOTheorem442BBFMonotonicity

/-!
# The order core for large BBF projections

This file proves the combinatorial part of BBF Theorem 3.3(G).  On the set of
vertices whose projection of `(X,Z)` is larger than a threshold `T ≥ 12ξ`, use

`W < U  ↔  5ξ < d_W(X,U)`.

Distinct large vertices are comparable, the relation is asymmetric, and it is
transitive.  These are the three facts used to sort the finite large-projection
set into the standard path of BBF Proposition 3.7.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

universe u

variable {V : Type u}

/-- The modified distances satisfy the coarse triangle inequality with error
`4ξ`.  This is BBF Theorem 3.3(C), obtained from Proposition 2.2 and the exact
triangle inequality for the original distances. -/
theorem bbfProjDist_triangle
    (P : ProjectionSystem V) {Y A B C : V}
    (hYA : Y ≠ A) (hYB : Y ≠ B) (hYC : Y ≠ C)
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) :
    P.bbfProjDist Y A C ≤
      P.bbfProjDist Y A B + P.bbfProjDist Y B C + 4 * P.ξ := by
  have hleft := P.projDist_sub_bbfProjDist_le_two_mul hYA hYB hAB
  have hright := P.projDist_sub_bbfProjDist_le_two_mul hYB hYC hBC
  have htop := P.bbfProjDist_le hYA hYC hAC
  have htri := P.triangle Y A B C hYA hYB hYC
  linarith

/-- A `5ξ` comparison has the opposite endpoint projection below `ξ`, so the
reverse comparison is impossible. -/
theorem bbf_before_asymm
    (P : ProjectionSystem V) {X W U : V}
    (hWX : W ≠ X) (hWU : W ≠ U) (hUX : U ≠ X)
    (hbefore : 5 * P.ξ < P.bbfProjDist W X U) :
    ¬ 5 * P.ξ < P.bbfProjDist U X W := by
  intro hreverse
  have hend := P.bbfProjDist_endpoints_lt hWX hWU hUX.symm (by
    linarith [P.ξ_pos])
  linarith [hend.2, P.ξ_pos]

/-- Distinct vertices with projection of `(X,Z)` larger than `T ≥ 12ξ` are
comparable by the `5ξ` relation.  This is the totality step in BBF Theorem
3.3(G). -/
theorem bbf_before_total_on_large
    (P : ProjectionSystem V) {T : ℝ} (hT : 12 * P.ξ ≤ T)
    {X Z W U : V}
    (hWX : W ≠ X) (hWZ : W ≠ Z)
    (hUX : U ≠ X) (hUZ : U ≠ Z) (hWU : W ≠ U)
    (hWlarge : T < P.bbfProjDist W X Z)
    (hUlarge : T < P.bbfProjDist U X Z) :
    5 * P.ξ < P.bbfProjDist W X U ∨
      5 * P.ξ < P.bbfProjDist U X W := by
  have hXZ : X ≠ Z := by
    intro hXZ'
    subst Z
    have hzero : P.bbfProjDist W X X = 0 := by
      rw [bbfProjDist, bbfRawProjDist,
        if_pos (Or.inr (Or.inr (Or.inl rfl)))]
    rw [hzero] at hWlarge
    linarith [P.ξ_pos]
  by_cases hbefore : 5 * P.ξ < P.bbfProjDist W X U
  · exact Or.inl hbefore
  · right
    have hWXU : P.bbfProjDist W X U ≤ 5 * P.ξ := le_of_not_gt hbefore
    have htriW := P.bbfProjDist_triangle hWX hWU hWZ hUX.symm hUZ hXZ
    have hWUZ : 2 * P.ξ < P.bbfProjDist W U Z := by
      linarith [hWlarge, P.ξ_pos]
    have hend := P.bbfProjDist_endpoints_lt hWU hWZ hUZ hWUZ
    have hUWZ : P.bbfProjDist U W Z < P.ξ := hend.1
    by_contra hnot
    have hUXW : P.bbfProjDist U X W ≤ 5 * P.ξ := le_of_not_gt hnot
    have htriU := P.bbfProjDist_triangle hUX hWU.symm hUZ hWX.symm hWZ hXZ
    linarith [hUlarge, hUWZ, P.ξ_pos]

/-- The `5ξ` relation is transitive.  The second comparison is already above
the `4ξ` monotonicity threshold, so monotonicity enlarges the first projection
from `(X,U)` to `(X,V)`. -/
theorem bbf_before_trans
    (P : ProjectionSystem V) {X W U T : V}
    (hWX : W ≠ X) (hWU : W ≠ U) (hWT : W ≠ T)
    (hUX : U ≠ X) (hUT : U ≠ T) (hTX : T ≠ X)
    (hWUbefore : 5 * P.ξ < P.bbfProjDist W X U)
    (hUTbefore : 5 * P.ξ < P.bbfProjDist U X T) :
    5 * P.ξ < P.bbfProjDist W X T := by
  have hlarge : 4 * P.ξ < P.bbfProjDist U X T := by
    linarith [hUTbefore, P.ξ_pos]
  have hmono := P.bbfProjDist_left_mono hWX hWU hWT
    hUX hUT hTX.symm hlarge
  linarith [hWUbefore]

/-- A vertex between two others in the `5ξ` order sees their pair with
projection at most the original projection of `(X,Z)`.  This is the upper
inequality in BBF Theorem 3.3(G). -/
theorem bbf_between_projDist_le
    (P : ProjectionSystem V) {X Z W U T : V}
    (hWX : W ≠ X) (hWU : W ≠ U) (hWT : W ≠ T) (_hWZ : W ≠ Z)
    (hUX : U ≠ X) (hUT : U ≠ T) (hUZ : U ≠ Z)
    (hTX : T ≠ X) (hTZ : T ≠ Z)
    (hXZ : X ≠ Z)
    (hWUbefore : 5 * P.ξ < P.bbfProjDist W X U)
    (hUTbefore : 5 * P.ξ < P.bbfProjDist U X T)
    (hTlarge : 4 * P.ξ < P.bbfProjDist T X Z) :
    P.bbfProjDist U W T ≤ P.bbfProjDist U X Z := by
  have hWTbefore := P.bbf_before_trans hWX hWU hWT hUX hUT hTX
    hWUbefore hUTbefore
  have hWTlarge : 4 * P.ξ < P.bbfProjDist W X T := by
    linarith [hWTbefore, P.ξ_pos]
  have hmono₁ := P.bbfProjDist_right_mono hUX hWU.symm hUT
    hWX hWT hTX.symm hWTlarge
  rw [P.bbfProjDist_comm U T W] at hmono₁
  have hmono₂ := P.bbfProjDist_left_mono hUX hUT hUZ
    hTX hTZ hXZ hTlarge
  exact hmono₁.trans hmono₂

end ProjectionSystem
end GGT
end GroupApproximation
