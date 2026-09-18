import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.Residual
import GroupApproximation.Meta.AxiomGuard

/-!
# Which boundary darts a quadrant move keeps

Lane gl-p10-92.  Helper lemmas for `P10FilterMoveExists.p10FM_QuadrantMoveStatement`.

Let `c` be the boundary cycle of a face set `F`, `B` a list of darts and `p q` two Booleans.  For a
dart `d ∈ c` the face of `d` is in `F` and the face of `alpha d` is not, so the quadrant colouring
`p10FM_z M F B p q` can colour at most one of `d`, `alpha d`, and which one depends only on `q`.
The four lemmas `p10QM_movePred_FF`, `_TF`, `_TT`, `_FT` say exactly when the move keeps a dart
of `c`:

* `q = false`: `d` is kept iff the face of `alpha d` is (`p = false`) or is not (`p = true`) on
  the side `sideFaces M B`;
* `q = true`: `d` is kept iff the face of `d` is not (`p = true`) or is (`p = false`) on that side.

Also: `p10QM_alpha_not_mem` (no edge of `c` is used twice) and `p10QM_side_alpha_iff` (across an
edge off `B`, both faces are on the same side of `B`).  All PROVED; no Jordan input here.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists

section Keep

variable (M : CombMap.{v})

/-- The reverse of a dart of a boundary cycle is not on the cycle. -/
theorem p10QM_alpha_not_mem {F : Finset M.Face} (c : BoundaryCycle M F) {d : M.Dart}
    (hd : d ∈ c.cycle) : M.alpha d ∉ c.cycle := by
  intro had
  obtain ⟨hin, -⟩ := (c.cycle_mem_iff d).mp hd
  obtain ⟨-, hout⟩ := (c.cycle_mem_iff (M.alpha d)).mp had
  rw [M.alpha_involutive d] at hout
  exact hout hin

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_alpha_not_mem

/-- Across an edge that is not on `B`, both faces are on the same side of `B`. -/
theorem p10QM_side_alpha_iff (B : List M.Dart) {d : M.Dart} (h₁ : d ∉ B) (h₂ : M.alpha d ∉ B) :
    M.faceOf d ∈ sideFaces M B ↔ M.faceOf (M.alpha d) ∈ sideFaces M B := by
  have hkB : ¬walkKeep M B d := fun h => Or.elim h h₁ h₂
  have hstep : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M B)) d (M.alpha d) :=
    Relation.EqvGen.rel _ _ (Or.inr ⟨hkB, rfl⟩)
  rw [mem_sideFaces_iff M B d, mem_sideFaces_iff M B (M.alpha d)]
  constructor
  · rintro ⟨e, he, hed⟩
    exact ⟨e, he, Relation.EqvGen.trans _ _ _ hed hstep⟩
  · rintro ⟨e, he, hed⟩
    exact ⟨e, he, Relation.EqvGen.trans _ _ _ hed (Relation.EqvGen.symm _ _ hstep)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_side_alpha_iff

/-- A dart is kept by a quadrant move iff neither of its faces is in the quadrant. -/
theorem p10QM_movePred_iff (F : Finset M.Face) (B : List M.Dart) (p q : Bool) (d : M.Dart) :
    movePred M (p10FM_z M F B p q) d = true ↔
      ¬p10FM_InZ M F B p q (M.faceOf d) ∧ ¬p10FM_InZ M F B p q (M.faceOf (M.alpha d)) := by
  rw [movePred_eq_true_iff, p10FM_z_eq_false_iff, p10FM_z_eq_false_iff]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_movePred_iff

/-- Quadrant `p = false, q = false`: a dart of `c` is kept iff its outer face is on the side. -/
theorem p10QM_movePred_FF {F : Finset M.Face} (c : BoundaryCycle M F) (B : List M.Dart)
    {d : M.Dart} (hd : d ∈ c.cycle) :
    movePred M (p10FM_z M F B false false) d = true ↔
      M.faceOf (M.alpha d) ∈ sideFaces M B := by
  obtain ⟨hin, hout⟩ := (c.cycle_mem_iff d).mp hd
  rw [p10QM_movePred_iff]
  constructor
  · rintro ⟨-, h⟩
    by_contra hs
    exact h (And.intro (iff_of_false hs Bool.false_ne_true)
      (iff_of_false hout Bool.false_ne_true))
  · intro hs
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨-, hF⟩ := h
      exact Bool.false_ne_true (hF.mp hin)
    · obtain ⟨hS, -⟩ := h
      exact Bool.false_ne_true (hS.mp hs)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_movePred_FF

/-- Quadrant `p = true, q = false`: a dart of `c` is kept iff its outer face is off the side. -/
theorem p10QM_movePred_TF {F : Finset M.Face} (c : BoundaryCycle M F) (B : List M.Dart)
    {d : M.Dart} (hd : d ∈ c.cycle) :
    movePred M (p10FM_z M F B true false) d = true ↔
      M.faceOf (M.alpha d) ∉ sideFaces M B := by
  obtain ⟨hin, hout⟩ := (c.cycle_mem_iff d).mp hd
  rw [p10QM_movePred_iff]
  constructor
  · rintro ⟨-, h⟩ hs
    exact h (And.intro (iff_of_true hs rfl) (iff_of_false hout Bool.false_ne_true))
  · intro hs
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨-, hF⟩ := h
      exact Bool.false_ne_true (hF.mp hin)
    · obtain ⟨hS, -⟩ := h
      exact hs (hS.mpr rfl)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_movePred_TF

/-- Quadrant `p = true, q = true`: a dart of `c` is kept iff its own face is off the side. -/
theorem p10QM_movePred_TT {F : Finset M.Face} (c : BoundaryCycle M F) (B : List M.Dart)
    {d : M.Dart} (hd : d ∈ c.cycle) :
    movePred M (p10FM_z M F B true true) d = true ↔ M.faceOf d ∉ sideFaces M B := by
  obtain ⟨hin, hout⟩ := (c.cycle_mem_iff d).mp hd
  rw [p10QM_movePred_iff]
  constructor
  · rintro ⟨h, -⟩ hs
    exact h (And.intro (iff_of_true hs rfl) (iff_of_true hin rfl))
  · intro hs
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨hS, -⟩ := h
      exact hs (hS.mpr rfl)
    · obtain ⟨-, hF⟩ := h
      exact hout (hF.mpr rfl)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_movePred_TT

/-- Quadrant `p = false, q = true`: a dart of `c` is kept iff its own face is on the side. -/
theorem p10QM_movePred_FT {F : Finset M.Face} (c : BoundaryCycle M F) (B : List M.Dart)
    {d : M.Dart} (hd : d ∈ c.cycle) :
    movePred M (p10FM_z M F B false true) d = true ↔ M.faceOf d ∈ sideFaces M B := by
  obtain ⟨hin, hout⟩ := (c.cycle_mem_iff d).mp hd
  rw [p10QM_movePred_iff]
  constructor
  · rintro ⟨h, -⟩
    by_contra hs
    exact h (And.intro (iff_of_false hs Bool.false_ne_true) (iff_of_true hin rfl))
  · intro hs
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨hS, -⟩ := h
      exact Bool.false_ne_true (hS.mp hs)
    · obtain ⟨-, hF⟩ := h
      exact hout (hF.mpr rfl)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_movePred_FT

end Keep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
