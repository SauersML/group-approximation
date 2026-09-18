import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalGFace
import GroupApproximation.Meta.AxiomGuard

/-!
# Face-set colourings of a boundary cycle

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-49.

Route: a colouring `z` of the walk regions of a boundary cycle `c` of `F` is the same datum as
the face set `F' = flipFaces M F z`.  This module gives the dictionary in both directions, for a
generic combinatorial map `M`:

* `extremalGFaceProve_colour M F F'` colours a dart `true` when its face is in exactly one of
  `F`, `F'`.
* `extremalGFaceProve_colour_step`: the colour is constant along the walk regions of `c` as soon
  as `F'` does not separate the two sides of any dart off the walk.
* `extremalGFaceProve_colour_indep`: no side pair of a walk dart is coloured twice as soon as
  every boundary dart of `F'` lies on `c`.
* `extremalGFaceProve_flipFaces_colour`: flipping `F` at the colour gives `F'`; and
  `extremalGFaceProve_colour_flipFaces` is the converse.
* `extremalGFaceProve_touch`: in a connected map, some walk dart is touched when `F' ≠ F`.
* `extremalGFaceProve_movePred_colour_of_mem`: on `c`, the kept darts of the colour are the
  boundary darts of `F'` (`extremalGFaceProve_bd`).
* `extremalGFaceProve_flip_union`, `extremalGFaceProve_flip_boundary`,
  `extremalGFaceProve_flip_ne`, `extremalGFaceProve_movePred_flip`: the converse facts for the
  face set `flipFaces M F z` of a colouring `z`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- The colour of a face: `true` when it lies in exactly one of `F`, `F'`. -/
noncomputable def extremalGFaceProve_colourFace (M : CombMap.{v}) (F F' : Finset M.Face)
    (f : M.Face) : Bool :=
  @decide (¬(f ∈ F ↔ f ∈ F')) (Classical.propDecidable _)

/-- The colour of a dart: the colour of its face. -/
noncomputable def extremalGFaceProve_colour (M : CombMap.{v}) (F F' : Finset M.Face)
    (x : M.Dart) : Bool :=
  extremalGFaceProve_colourFace M F F' (M.faceOf x)

/-- The boundary darts of a face set, as a Boolean predicate. -/
noncomputable def extremalGFaceProve_bd (M : CombMap.{v}) (F' : Finset M.Face)
    (d : M.Dart) : Bool :=
  @decide (M.faceOf d ∈ F' ∧ M.faceOf (M.alpha d) ∉ F') (Classical.propDecidable _)

theorem extremalGFaceProve_colour_eq_false_iff (M : CombMap.{v}) (F F' : Finset M.Face)
    (x : M.Dart) :
    extremalGFaceProve_colour M F F' x = false ↔ (M.faceOf x ∈ F ↔ M.faceOf x ∈ F') := by
  unfold extremalGFaceProve_colour extremalGFaceProve_colourFace
  exact (@decide_eq_false_iff_not _ (Classical.propDecidable _)).trans Classical.not_not

theorem extremalGFaceProve_bd_eq_true_iff (M : CombMap.{v}) (F' : Finset M.Face)
    (d : M.Dart) :
    extremalGFaceProve_bd M F' d = true ↔
      M.faceOf d ∈ F' ∧ M.faceOf (M.alpha d) ∉ F' := by
  unfold extremalGFaceProve_bd
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem extremalGFaceProve_bool_eq_of_false_iff {a b : Bool} (h : a = false ↔ b = false) :
    a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd (h.mp rfl) (by decide)
  · exact absurd (h.mpr rfl) (by decide)
  · rfl

theorem extremalGFaceProve_bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) :
    a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd (h.mpr rfl) (by decide)
  · exact absurd (h.mp rfl) (by decide)
  · rfl

theorem extremalGFaceProve_colour_eq_of_iff (M : CombMap.{v}) (F F' : Finset M.Face)
    {x y : M.Dart} (h1 : M.faceOf x ∈ F ↔ M.faceOf y ∈ F)
    (h2 : M.faceOf x ∈ F' ↔ M.faceOf y ∈ F') :
    extremalGFaceProve_colour M F F' x = extremalGFaceProve_colour M F F' y := by
  apply extremalGFaceProve_bool_eq_of_false_iff
  rw [extremalGFaceProve_colour_eq_false_iff M F F' x,
    extremalGFaceProve_colour_eq_false_iff M F F' y]
  exact ⟨fun h => h1.symm.trans (h.trans h2), fun h => h1.trans (h.trans h2.symm)⟩

/-- Off the walk, the two sides of a dart are on the same side of `F`. -/
theorem extremalGFaceProve_mem_iff_alpha_of_not_walkKeep {M : CombMap.{v}} {F : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    {x : M.Dart} (hx : ¬ walkKeep M c x) :
    M.faceOf x ∈ F ↔ M.faceOf (M.alpha x) ∈ F := by
  constructor
  · intro h
    by_contra h'
    exact hx (Or.inl ((hc x).mpr ⟨h, h'⟩))
  · intro h
    by_contra h'
    refine hx (Or.inr ((hc (M.alpha x)).mpr ⟨h, ?_⟩))
    rwa [M.alpha_involutive x]

/-- **The colour is constant along the walk regions** when `F'` separates no dart off the walk. -/
theorem extremalGFaceProve_colour_step (M : CombMap.{v}) (F F' : Finset M.Face)
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    (hU : ∀ x, ¬ walkKeep M c x → (M.faceOf x ∈ F' ↔ M.faceOf (M.alpha x) ∈ F')) :
    ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y →
      extremalGFaceProve_colour M F F' x = extremalGFaceProve_colour M F F' y := by
  intro x y hxy
  rcases (show y = M.facePerm x ∨ (¬ walkKeep M c x ∧ y = M.alpha x) from hxy) with
    rfl | ⟨hk, rfl⟩
  · exact congrArg (extremalGFaceProve_colourFace M F F')
      ((M.faceOf_eq_iff x (M.facePerm x)).mpr
        (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)))
  · exact extremalGFaceProve_colour_eq_of_iff M F F'
      (extremalGFaceProve_mem_iff_alpha_of_not_walkKeep hc hk) (hU x hk)

/-- **No side pair of a walk dart is coloured twice** when every boundary dart of `F'` is on the
walk. -/
theorem extremalGFaceProve_colour_indep {M : CombMap.{v}} {F F' : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    (hB : ∀ d, M.faceOf d ∈ F' → M.faceOf (M.alpha d) ∉ F' → d ∈ c) :
    ∀ d ∈ c, extremalGFaceProve_colour M F F' d = false ∨
      extremalGFaceProve_colour M F F' (M.alpha d) = false := by
  intro d hd
  obtain ⟨hin, hout⟩ := (hc d).mp hd
  by_cases h : M.faceOf d ∈ F'
  · exact Or.inl ((extremalGFaceProve_colour_eq_false_iff M F F' d).mpr (iff_of_true hin h))
  · refine Or.inr ((extremalGFaceProve_colour_eq_false_iff M F F' (M.alpha d)).mpr
      (iff_of_false hout fun h' => ?_))
    have hα : M.alpha d ∈ c := hB (M.alpha d) h' (by rwa [M.alpha_involutive d])
    obtain ⟨hin', -⟩ := (hc (M.alpha d)).mp hα
    exact hout hin'
