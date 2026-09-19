import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.FilterMove
import GroupApproximation.Meta.AxiomGuard

/-!
# Quadrant colourings of a boundary cycle

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-91.

Fix a combinatorial map `M`, a face set `F`, a list `c` of darts that is exactly the list of
boundary darts of `F` (`d ∈ c ↔ IsBoundaryDart M F d`), a sublist of darts `B ⊆ c` and two
Booleans `p q`.  The **quadrant** `p10FM_InZ M F B p q` is the set of faces `f` with
`f ∈ sideFaces M B ↔ p` and `f ∈ F ↔ q`; the **quadrant colouring** `p10FM_z M F B p q` colours
a dart `true` exactly when its face lies in the quadrant.

Proof of the two colour clauses of `P10RegionSubArc.subArc_FilterMove` (all PROVED here):

* `p10FM_z_step` (region constancy).  A step `x → facePerm x` keeps the face.  A step
  `x → alpha x` with `x, alpha x ∉ c` is also a step of the face classes of `B` (because
  `B ⊆ c`), so `faceOf x` and `faceOf (alpha x)` are on the same side of `B`
  (`mem_sideFaces_iff`); neither `x` nor `alpha x` is a boundary dart of `F`, so `faceOf x ∈ F`
  iff `faceOf (alpha x) ∈ F`.  Hence both faces are in the quadrant or both are not.
* `p10FM_z_indep` (independence).  For `d ∈ c`, `faceOf d ∈ F` and `faceOf (alpha d) ∉ F`, so the
  two faces cannot both satisfy `f ∈ F ↔ q`.
* `p10FM_not_mem_flip`, `p10FM_mem_flip`: a face off the quadrant keeps its membership in the
  moved face set `flipFaces M F z` (`P10Rose.FilterMove.not_mem_flipFaces`, `mem_flipFaces`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists

universe v

open SimpleClosedWalkSides P10Rose.FilterMove

section Colour

variable (M : CombMap.{v})

/-- **The quadrant** of the faces cut by the side of `B` and by the face set `F`. -/
def p10FM_InZ (F : Finset M.Face) (B : List M.Dart) (p q : Bool) (f : M.Face) : Prop :=
  (f ∈ sideFaces M B ↔ p = true) ∧ (f ∈ F ↔ q = true)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_InZ

/-- **The quadrant colouring**: a dart is coloured `true` when its face is in the quadrant. -/
noncomputable def p10FM_z (F : Finset M.Face) (B : List M.Dart) (p q : Bool) (d : M.Dart) :
    Bool := by
  classical
  exact decide (p10FM_InZ M F B p q (M.faceOf d))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_z

theorem p10FM_z_eq_true_iff (F : Finset M.Face) (B : List M.Dart) (p q : Bool) (d : M.Dart) :
    p10FM_z M F B p q d = true ↔ p10FM_InZ M F B p q (M.faceOf d) := by
  unfold p10FM_z
  classical
  exact decide_eq_true_iff

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_z_eq_true_iff

theorem p10FM_z_eq_false_iff (F : Finset M.Face) (B : List M.Dart) (p q : Bool) (d : M.Dart) :
    p10FM_z M F B p q d = false ↔ ¬p10FM_InZ M F B p q (M.faceOf d) := by
  rw [← p10FM_z_eq_true_iff M F B p q d, Bool.not_eq_true]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_z_eq_false_iff

/-- Two darts whose faces are together in or out of the quadrant have the same colour. -/
theorem p10FM_z_congr {F : Finset M.Face} {B : List M.Dart} {p q : Bool} {x y : M.Dart}
    (h : p10FM_InZ M F B p q (M.faceOf x) ↔ p10FM_InZ M F B p q (M.faceOf y)) :
    p10FM_z M F B p q x = p10FM_z M F B p q y := by
  by_cases hx : p10FM_InZ M F B p q (M.faceOf x)
  · rw [(p10FM_z_eq_true_iff M F B p q x).mpr hx,
      (p10FM_z_eq_true_iff M F B p q y).mpr (h.mp hx)]
  · rw [(p10FM_z_eq_false_iff M F B p q x).mpr hx,
      (p10FM_z_eq_false_iff M F B p q y).mpr (fun hy => hx (h.mpr hy))]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_z_congr

/-- Across an edge off `c`, the two faces are on the same side of `B ⊆ c` and both in or both
out of `F`. -/
theorem p10FM_inZ_alpha_iff (F : Finset M.Face) {B c : List M.Dart} (hB : ∀ d ∈ B, d ∈ c)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) (p q : Bool) {x : M.Dart}
    (hk : ¬walkKeep M c x) :
    p10FM_InZ M F B p q (M.faceOf x) ↔ p10FM_InZ M F B p q (M.faceOf (M.alpha x)) := by
  have hkB : ¬walkKeep M B x := fun h => hk (Or.imp (hB x) (hB (M.alpha x)) h)
  have hstep : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M B)) x (M.alpha x) :=
    Relation.EqvGen.rel _ _ (Or.inr ⟨hkB, rfl⟩)
  have hside : M.faceOf x ∈ sideFaces M B ↔ M.faceOf (M.alpha x) ∈ sideFaces M B := by
    rw [mem_sideFaces_iff M B x, mem_sideFaces_iff M B (M.alpha x)]
    constructor
    · rintro ⟨d, hd, hdx⟩
      exact ⟨d, hd, Relation.EqvGen.trans _ _ _ hdx hstep⟩
    · rintro ⟨d, hd, hdx⟩
      exact ⟨d, hd, Relation.EqvGen.trans _ _ _ hdx (Relation.EqvGen.symm _ _ hstep)⟩
  have hx : x ∉ c := fun h => hk (Or.inl h)
  have hax : M.alpha x ∉ c := fun h => hk (Or.inr h)
  have h₁ : ¬(M.faceOf x ∈ F ∧ M.faceOf (M.alpha x) ∉ F) := fun h => hx ((hc x).mpr h)
  have h₂ : ¬(M.faceOf (M.alpha x) ∈ F ∧ M.faceOf x ∉ F) := by
    intro h
    apply hax
    refine (hc (M.alpha x)).mpr (And.intro h.1 ?_)
    rw [M.alpha_involutive x]
    exact h.2
  have hF : M.faceOf x ∈ F ↔ M.faceOf (M.alpha x) ∈ F :=
    ⟨fun ha => Classical.byContradiction fun hb => h₁ ⟨ha, hb⟩,
      fun hb => Classical.byContradiction fun ha => h₂ ⟨hb, ha⟩⟩
  exact and_congr (iff_congr hside Iff.rfl) (iff_congr hF Iff.rfl)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_inZ_alpha_iff

/-- **Region constancy** of a quadrant colouring along the face classes of `c`. -/
theorem p10FM_z_step (F : Finset M.Face) {B c : List M.Dart} (hB : ∀ d ∈ B, d ∈ c)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) (p q : Bool) :
    ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y →
      p10FM_z M F B p q x = p10FM_z M F B p q y := by
  intro x y hxy
  rcases hxy with rfl | ⟨hk, rfl⟩
  · exact p10FM_z_congr M (by rw [M.faceOf_facePerm x])
  · exact p10FM_z_congr M (p10FM_inZ_alpha_iff M F hB hc p q hk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_z_step

/-- **Independence**: no boundary dart of `F` has both faces in one quadrant. -/
theorem p10FM_z_indep (F : Finset M.Face) {B c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) (p q : Bool) :
    ∀ d ∈ c, p10FM_z M F B p q d = false ∨ p10FM_z M F B p q (M.alpha d) = false := by
  intro d hd
  obtain ⟨hin, hout⟩ := (hc d).mp hd
  by_cases hq : q = true
  · right
    rw [p10FM_z_eq_false_iff M F B p q (M.alpha d)]
    rintro ⟨-, hF⟩
    exact hout (hF.mpr hq)
  · left
    rw [p10FM_z_eq_false_iff M F B p q d]
    rintro ⟨-, hF⟩
    exact hq (hF.mp hin)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_z_indep

/-- A face outside `F` and off the quadrant stays outside the moved face set. -/
theorem p10FM_not_mem_flip {F : Finset M.Face} {B c : List M.Dart} (hB : ∀ d ∈ B, d ∈ c)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) {p q : Bool} {f : M.Face}
    (hf : f ∉ F) (hnz : ¬p10FM_InZ M F B p q f) : f ∉ flipFaces M F (p10FM_z M F B p q) :=
  not_mem_flipFaces (p10FM_z_step M F hB hc p q) hf fun x hx =>
    (p10FM_z_eq_false_iff M F B p q x).mpr (by rw [hx]; exact hnz)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_not_mem_flip

/-- A face of `F` off the quadrant stays inside the moved face set. -/
theorem p10FM_mem_flip {F : Finset M.Face} {B c : List M.Dart} (hB : ∀ d ∈ B, d ∈ c)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) {p q : Bool} {f : M.Face}
    (hf : f ∈ F) (hnz : ¬p10FM_InZ M F B p q f) : f ∈ flipFaces M F (p10FM_z M F B p q) :=
  mem_flipFaces (p10FM_z_step M F hB hc p q) hf fun x hx =>
    (p10FM_z_eq_false_iff M F B p q x).mpr (by rw [hx]; exact hnz)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_mem_flip

end Colour

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists
