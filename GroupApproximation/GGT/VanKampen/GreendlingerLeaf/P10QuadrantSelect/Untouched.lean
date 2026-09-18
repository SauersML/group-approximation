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

/-- **A dart of `c` off `B`** is kept by the quadrant move `p q` iff its face is on the side of
`B` exactly when `p = false`. -/
theorem p10QS_movePred_off {F : Finset M.Face} (c : BoundaryCycle M F) {B : List M.Dart}
    (hBc : ∀ e ∈ B, e ∈ c.cycle) (p q : Bool) {d : M.Dart} (hd : d ∈ c.cycle) (hdB : d ∉ B) :
    movePred M (p10FM_z M F B p q) d = true ↔ (M.faceOf d ∈ sideFaces M B ↔ p = false) := by
  have hs : M.faceOf d ∈ sideFaces M B ↔ M.faceOf (M.alpha d) ∈ sideFaces M B :=
    p10QM_side_alpha_iff M B hdB fun h => p10QM_alpha_not_mem M c hd (hBc _ h)
  cases p <;> cases q
  · rw [p10QM_movePred_FF M c B hd, ← hs]
    simp
  · rw [p10QM_movePred_FT M c B hd]
    simp
  · rw [p10QM_movePred_TF M c B hd, ← hs]
    simp
  · rw [p10QM_movePred_TT M c B hd]
    simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_movePred_off

/-- **A dart of `B`** is kept by the quadrant move `p q` iff `q = true ↔ p = false` (Jordan: its
face is on the side of `B` and the face across it is not). -/
theorem p10QS_movePred_on (hM : M.IsPlanar) {F : Finset M.Face} (c : BoundaryCycle M F)
    {B : List M.Dart} (hB : IsSimpleClosedWalk M B) (hBc : ∀ e ∈ B, e ∈ c.cycle) (p q : Bool)
    {d : M.Dart} (hd : d ∈ B) :
    movePred M (p10FM_z M F B p q) d = true ↔ (q = true ↔ p = false) := by
  have hJ := (hB.isBoundaryDart_sideFaces_iff hM d).mpr hd
  have hin : M.faceOf d ∈ sideFaces M B := And.left hJ
  have hout : M.faceOf (M.alpha d) ∉ sideFaces M B := And.right hJ
  have hdc : d ∈ c.cycle := hBc d hd
  cases p <;> cases q
  · rw [p10QM_movePred_FF M c B hdc]
    simp [hout]
  · rw [p10QM_movePred_FT M c B hdc]
    simp [hin]
  · rw [p10QM_movePred_TF M c B hdc]
    simp [hout]
  · rw [p10QM_movePred_TT M c B hdc]
    simp [hin]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_movePred_on

/-- **The kept walk of a quadrant move for an untouched `B` is closed.**  If `B ⊆ c` is a simple
closed walk untouched in `c` away from `v0`, then for every quadrant `p q` keeping some dart,
the kept darts of `c` form a closed dart walk. -/
theorem p10QS_closed_untouched (hM : M.IsPlanar) {F : Finset M.Face} (c : BoundaryCycle M F)
    (hc : IsClosedDartWalk M c.cycle) {B : List M.Dart} (hB : IsSimpleClosedWalk M B)
    (hBc : ∀ e ∈ B, e ∈ c.cycle) {v0 : M.Vertex} (hU : p10QS_Untouched M c.cycle B v0)
    (p q : Bool) (hkept : ∃ d ∈ c.cycle, movePred M (p10FM_z M F B p q) d = true) :
    IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
  refine p10QS_closed_filter_of_switch _ v0 hc ?_ hkept
  intro d hd e he hde hne
  by_cases hdB : d ∈ B <;> by_cases heB : e ∈ B
  · exact absurd (Bool.eq_iff_iff.mpr ((p10QS_movePred_on M hM c hB hBc p q hdB).trans
      (p10QS_movePred_on M hM c hB hBc p q heB).symm)) hne
  · exact (hU e he heB).1 ⟨d, hdB, Or.inr hde⟩
  · exact hde.symm.trans ((hU d hd hdB).2 ⟨e, heB, Or.inl hde.symm⟩)
  · by_cases hW : p10QS_OnB M B (M.vertexOf e)
    · exact (hU e he heB).1 hW
    · have hadB : M.alpha d ∉ B := fun h => p10QM_alpha_not_mem M c hd (hBc _ h)
      have hW' : ¬p10QS_OnB M B (M.vertexOf (M.alpha d)) := by
        rw [hde]
        exact hW
      have hchain : M.faceOf d ∈ sideFaces M B ↔ M.faceOf e ∈ sideFaces M B :=
        (p10QM_side_alpha_iff M B hdB hadB).trans (p10QS_side_iff_of_not_onB M B hde hW')
      exact absurd (Bool.eq_iff_iff.mpr ((p10QS_movePred_off M c hBc p q hd hdB).trans
        ((iff_congr hchain Iff.rfl).trans (p10QS_movePred_off M c hBc p q he heB).symm))) hne

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_closed_untouched

end Untouched

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
