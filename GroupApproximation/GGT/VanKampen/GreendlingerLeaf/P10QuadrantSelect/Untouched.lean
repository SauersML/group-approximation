import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantSelect.Switch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.Keep
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSidesDisjoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The kept walk of a quadrant move for an untouched lobe is closed

Lane gl-p10-93.  Helper lemmas for `P10FilterMoveExists.p10FM_QuadrantMoveStatement`.

Let `c` be the boundary cycle of `F` (a closed dart walk) in a planar map, and `B ⊆ c` a simple
closed walk.  `B` is *untouched away from `v0`* (`p10QS_Untouched`) when every dart of `c` off
`B` meets a vertex of `B` (`p10QS_OnB`) only at `v0`.  This is the mixed-side case of the
quadrant move: the darts of `c` off `B` may lie on both sides of `B`.

* `p10QS_side_iff_of_not_onB`: at a vertex off `B`, all faces are on the same side of `B`
  (rotating around the vertex never crosses `B`).
* `p10QS_movePred_off`, `p10QS_movePred_on`: for any quadrant `p q`, a dart of `c` off `B` is
  kept iff its face is on the side exactly when `p = false`; a dart of `B` is kept iff
  `q = true ↔ p = false` (Jordan fact `IsSimpleClosedWalk.isBoundaryDart_sideFaces_iff`).
* `p10QS_closed_untouched`: hence the keep predicate of any quadrant move switches only at
  `v0`, and the kept walk is closed as soon as some dart is kept
  (`p10QS_closed_filter_of_switch`).

All PROVED.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists

section Untouched

variable (M : CombMap.{v})

/-- The vertex `w` lies on `B`: some dart of `B` starts or ends at `w`. -/
def p10QS_OnB (B : List M.Dart) (w : M.Vertex) : Prop :=
  ∃ x ∈ B, M.vertexOf x = w ∨ M.vertexOf (M.alpha x) = w

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_OnB

/-- **`B` is untouched in `c` away from `v0`**: a dart of `c` off `B` meets a vertex of `B` only
at `v0`. -/
def p10QS_Untouched (c B : List M.Dart) (v0 : M.Vertex) : Prop :=
  ∀ d ∈ c, d ∉ B → (p10QS_OnB M B (M.vertexOf d) → M.vertexOf d = v0) ∧
    (p10QS_OnB M B (M.vertexOf (M.alpha d)) → M.vertexOf (M.alpha d) = v0)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_Untouched

/-- A dart at a vertex off `B` is not retained by `B`. -/
theorem p10QS_not_walkKeep (B : List M.Dart) {z : M.Dart}
    (hz : ¬p10QS_OnB M B (M.vertexOf z)) : ¬walkKeep M B z := by
  rintro (h | h)
  · exact hz ⟨z, h, Or.inl rfl⟩
  · exact hz ⟨M.alpha z, h, Or.inr (congrArg M.vertexOf (M.alpha_involutive z))⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_not_walkKeep

/-- Rotating around a vertex off `B` stays in one face class of `B`. -/
theorem p10QS_eqvGen_sigma_pow (B : List M.Dart) {W : M.Vertex} (hW : ¬p10QS_OnB M B W)
    (m : ℕ) : ∀ z : M.Dart, M.vertexOf z = W →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M B)) z ((M.sigma ^ m) z) := by
  induction m with
  | zero =>
    intro z _
    exact Relation.EqvGen.refl _
  | succ m ih =>
    intro z hz
    rw [pow_succ, Equiv.Perm.mul_apply]
    have hk : ¬walkKeep M B z := p10QS_not_walkKeep M B (by rw [hz]; exact hW)
    have h₁ : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M B)) z (M.alpha z) :=
      Relation.EqvGen.rel _ _ (Or.inr ⟨hk, rfl⟩)
    have h₂ : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M B)) (M.alpha z) (M.sigma z) :=
      Relation.EqvGen.rel _ _ (Or.inl (congrArg M.sigma (M.alpha_involutive z)).symm)
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ h₁ h₂)
      (ih (M.sigma z) ((M.vertexOf_sigma z).trans hz))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_eqvGen_sigma_pow

/-- **At a vertex off `B`, all faces are on the same side of `B`.** -/
theorem p10QS_side_iff_of_not_onB (B : List M.Dart) {x y : M.Dart}
    (hxy : M.vertexOf x = M.vertexOf y) (hW : ¬p10QS_OnB M B (M.vertexOf x)) :
    M.faceOf x ∈ sideFaces M B ↔ M.faceOf y ∈ sideFaces M B := by
  obtain ⟨n, hn⟩ := ((M.vertexOf_eq_iff x y).mp hxy).exists_nat_pow_eq
  have h := p10QS_eqvGen_sigma_pow M B hW n x rfl
  rw [hn] at h
  exact mem_sideFaces_iff_of_eqvGen B h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_side_iff_of_not_onB
