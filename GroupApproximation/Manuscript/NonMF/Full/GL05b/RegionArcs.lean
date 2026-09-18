import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# One region of a pocket boundary cycle on the two carrier arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Item 1 of "Part (b)" in the docstring of
`GreendlingerLeaf/P10RoseExtremalTrim/Reduction.lean` reads: an extremal region meets the arcs in
a prefix, a suffix or a whole arc.  This file supplies the combinatorial part of that item.

Let `K` be a pocket face set with boundary cycle `c`, and let `z = regionColour r` be the colouring
that is `true` exactly on the face class of `r` for `FaceClassStep (walkKeep c)`.  The move keeps a
dart `d` when `movePred z d = true`, that is when neither side of `d` is coloured.

* `faceOf_mem_iff_of_walkEqvGen`: the walls of a face class are exactly the boundary darts, so a
  face class lies entirely inside or entirely outside `K.faces`.
* Arc facts: every dart of `t_2` (`K.targetArc.darts`) and of `t_1⁻¹`
  (`invDarts X K.sourceArc.darts`) lies on `c`, with the exterior face, respectively the source
  cell, across it.
* `IsEndBlock p l`: the filter of `l` by `p` is a prefix `l.take i` or a suffix `l.drop i`.
* The lake case (`isEndBlock_arcs_of_lake`): if the class of `r` lies outside `K.faces` and meets
  neither the exterior face nor the source cell, the move keeps both arcs whole.
* The case of a `K`-region (`filter_movePred_eq_filter_not`): on each arc the move keeps exactly the
  darts outside the class of `r`, so the filter is an end block as soon as the class meets the arc
  in a prefix or a suffix (`isEndBlock_of_split_true_false`,
  `isEndBlock_of_split_false_true`, `filter_targetArc_of_mem`, `filter_invSourceArc_of_mem`).

## The per-region form is false

Work order WO-GL05-2 asked for an end block on both arcs for *every* dart `r`.  That form fails,
which is why the lemmas above take the prefix/suffix split as a hypothesis.

* Middle region.  Take three components `A`, `B`, `C` of `K.faces` in this order along `t_2`, with
  lakes between them that reach the source cell.  The class of any dart of `B` is `B`, and the move
  keeps the `A`-darts and the `C`-darts of `t_2`.  That is `take ++ drop` with both parts nonempty,
  which is neither a prefix nor a suffix of `t_2`.
* Pendant component.  A disc of faces of `K` attached at one vertex between two stretches of
  another component along `t_2` gives the pattern `F G G F` on `t_2`, and neither class is an end
  block.  This configuration has an uncrossed turn at the attaching vertex, so the rose hypothesis
  `P10ChordLift.AllNonFirstTurnsCrossed` is essential for any existential version.

The planar argument that some extremal region (for instance `A` above) meets both arcs in end
blocks under the rose hypotheses is not part of this file.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`, Hull's small cancellation theorem,
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL05b

universe u w v

open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-! ## End blocks of a list -/

/-- **An end block**: filtering `l` by `p` gives a prefix `l.take i` or a suffix `l.drop i`. -/
def IsEndBlock {α : Type*} (p : α → Bool) (l : List α) : Prop :=
  ∃ i, l.filter p = l.take i ∨ l.filter p = l.drop i

/-- A predicate true on a first part and false on the rest filters to the first part. -/
theorem filter_append_eq_take {α : Type*} (p : α → Bool) {A B : List α}
    (hA : ∀ a ∈ A, p a = true) (hB : ∀ b ∈ B, p b = false) :
    (A ++ B).filter p = (A ++ B).take A.length := by
  have h1 : A.filter p = A := List.filter_eq_self.mpr hA
  have h2 : B.filter p = [] := List.filter_eq_nil_iff.mpr fun b hb h => by
    rw [hB b hb] at h
    exact absurd h (by decide)
  rw [List.filter_append, h1, h2, List.append_nil, List.take_left]

/-- A predicate false on a first part and true on the rest filters to the rest. -/
theorem filter_append_eq_drop {α : Type*} (p : α → Bool) {A B : List α}
    (hA : ∀ a ∈ A, p a = false) (hB : ∀ b ∈ B, p b = true) :
    (A ++ B).filter p = (A ++ B).drop A.length := by
  have h1 : A.filter p = [] := List.filter_eq_nil_iff.mpr fun a ha h => by
    rw [hA a ha] at h
    exact absurd h (by decide)
  have h2 : B.filter p = B := List.filter_eq_self.mpr hB
  rw [List.filter_append, h1, h2, List.nil_append, List.drop_left]

/-- A predicate true on the whole list gives the whole list, an end block. -/
theorem isEndBlock_of_forall_true {α : Type*} {p : α → Bool} {l : List α}
    (h : ∀ a ∈ l, p a = true) : IsEndBlock p l :=
  ⟨l.length, Or.inl (by rw [List.filter_eq_self.mpr h, List.take_length])⟩

/-- True on a first part and false on the rest: an end block. -/
theorem isEndBlock_append_true_false {α : Type*} {p : α → Bool} {A B : List α}
    (hA : ∀ a ∈ A, p a = true) (hB : ∀ b ∈ B, p b = false) : IsEndBlock p (A ++ B) :=
  ⟨A.length, Or.inl (filter_append_eq_take p hA hB)⟩

/-- False on a first part and true on the rest: an end block. -/
theorem isEndBlock_append_false_true {α : Type*} {p : α → Bool} {A B : List α}
    (hA : ∀ a ∈ A, p a = false) (hB : ∀ b ∈ B, p b = true) : IsEndBlock p (A ++ B) :=
  ⟨A.length, Or.inr (filter_append_eq_drop p hA hB)⟩

/-! ## The move predicate and the colouring of one region

Restated from `GreendlingerLeaf/P10Rose/Live/Move.lean` (`FilterMove.movePred`) and
`GreendlingerLeaf/P10RoseEndpoint/SingleRegion.lean` (`SubArcMove.regionColour`), with the same
bodies, since those modules are not wired. -/

/-- **The kept darts of a move**: neither side is flipped.  Restated from
`GreendlingerLeaf/P10Rose/Live/Move.lean` (`FilterMove.movePred`). -/
def movePred (M : CombMap.{v}) (z : M.Dart → Bool) (d : M.Dart) : Bool :=
  !z d && !z (M.alpha d)

/-- A dart is kept exactly when neither of its sides is flipped. -/
theorem movePred_eq_true_iff (M : CombMap.{v}) (z : M.Dart → Bool) (d : M.Dart) :
    movePred M z d = true ↔ z d = false ∧ z (M.alpha d) = false := by
  cases hd : z d <;> cases ha : z (M.alpha d) <;> simp [movePred, hd, ha]

/-- With the far side unflipped, a dart is kept exactly when it is unflipped. -/
theorem movePred_eq_not_of_alpha_eq_false (M : CombMap.{v}) (z : M.Dart → Bool) {d : M.Dart}
    (h : z (M.alpha d) = false) : movePred M z d = !z d := by
  rw [movePred, h, Bool.not_false, Bool.and_true]

/-- **The colouring of one region**: `true` exactly on the face class of `r`.  Restated from
`GreendlingerLeaf/P10RoseEndpoint/SingleRegion.lean` (`SubArcMove.regionColour`). -/
noncomputable def regionColour (M : CombMap.{v}) (keep : M.Dart → Prop) (r x : M.Dart) : Bool :=
  @ite Bool (Relation.EqvGen (CombMap.FaceClassStep M keep) r x) (Classical.propDecidable _)
    true false

/-- The colouring is `true` exactly on the face class of `r`. -/
theorem regionColour_eq_true_iff (M : CombMap.{v}) (keep : M.Dart → Prop) (r x : M.Dart) :
    regionColour M keep r x = true ↔ Relation.EqvGen (CombMap.FaceClassStep M keep) r x := by
  unfold regionColour
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

/-- A dart outside the class of `r` is not coloured. -/
theorem regionColour_eq_false (M : CombMap.{v}) (keep : M.Dart → Prop) {r x : M.Dart}
    (hx : ¬Relation.EqvGen (CombMap.FaceClassStep M keep) r x) :
    regionColour M keep r x = false := by
  cases h : regionColour M keep r x with
  | false => rfl
  | true => exact absurd ((regionColour_eq_true_iff M keep r x).mp h) hx

/-! ## Face classes of a boundary cycle have uniform membership -/

/-- **A face-class chain of a boundary cycle keeps membership in the face set.**  Restated from
`GreendlingerLeaf/P10Rose/Lobe.lean` (`faceOf_mem_iff_of_walkEqvGen`), proved directly: a face
step keeps the face, and an edge step crosses an edge off the cycle, which is not a wall. -/
theorem faceOf_mem_iff_of_walkEqvGen {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) {x y : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) x y) :
    M.faceOf x ∈ faces ↔ M.faceOf y ∈ faces := by
  induction h with
  | rel x₁ x₂ hx =>
      rcases hx with rfl | ⟨hoff, rfl⟩
      · rw [M.faceOf_facePerm]
      · constructor
        · intro hin
          by_contra hout
          have hb : IsBoundaryDart M faces x₁ :=
            show M.faceOf x₁ ∈ faces ∧ M.faceOf (M.alpha x₁) ∉ faces from ⟨hin, hout⟩
          exact hoff (show x₁ ∈ c ∨ M.alpha x₁ ∈ c from Or.inl ((hc x₁).mpr hb))
        · intro hin
          by_contra hout
          have hout' : M.faceOf (M.alpha (M.alpha x₁)) ∉ faces := by
            rw [M.alpha_involutive x₁]
            exact hout
          have hb : IsBoundaryDart M faces (M.alpha x₁) :=
            show M.faceOf (M.alpha x₁) ∈ faces ∧ M.faceOf (M.alpha (M.alpha x₁)) ∉ faces from
              ⟨hin, hout'⟩
          exact hoff (show x₁ ∈ c ∨ M.alpha x₁ ∈ c from Or.inr ((hc (M.alpha x₁)).mpr hb))
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The class of a dart inside the face set colours no dart based outside it. -/
theorem regionColour_eq_false_of_not_mem {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) {r x : M.Dart}
    (hr : M.faceOf r ∈ faces) (hx : M.faceOf x ∉ faces) :
    regionColour M (walkKeep M c) r x = false :=
  regionColour_eq_false M _ fun h => hx ((faceOf_mem_iff_of_walkEqvGen hc h).mp hr)

/-- The class of a dart outside the face set colours no dart based inside it. -/
theorem regionColour_eq_false_of_mem {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) {r x : M.Dart}
    (hr : M.faceOf r ∉ faces) (hx : M.faceOf x ∈ faces) :
    regionColour M (walkKeep M c) r x = false :=
  regionColour_eq_false M _ fun h => hr ((faceOf_mem_iff_of_walkEqvGen hc h).mpr hx)

/-- **The move of a region inside the face set, on darts with the far side outside.**  It keeps
exactly the darts outside the class of `r`. -/
theorem filter_movePred_eq_filter_not {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) {r : M.Dart}
    (hr : M.faceOf r ∈ faces) {l : List M.Dart} (hl : ∀ d ∈ l, M.faceOf (M.alpha d) ∉ faces) :
    l.filter (movePred M (regionColour M (walkKeep M c) r)) =
      l.filter fun d => !regionColour M (walkKeep M c) r d :=
  List.filter_congr fun d hd =>
    movePred_eq_not_of_alpha_eq_false M _ (regionColour_eq_false_of_not_mem hc hr (hl d hd))

/-- A region inside the face set meeting `l = A ++ B` exactly in `A` gives the suffix `B`. -/
theorem isEndBlock_of_split_true_false {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) {r : M.Dart}
    (hr : M.faceOf r ∈ faces) {A B : List M.Dart}
    (hl : ∀ d ∈ A ++ B, M.faceOf (M.alpha d) ∉ faces)
    (hA : ∀ a ∈ A, regionColour M (walkKeep M c) r a = true)
    (hB : ∀ b ∈ B, regionColour M (walkKeep M c) r b = false) :
    IsEndBlock (movePred M (regionColour M (walkKeep M c) r)) (A ++ B) := by
  refine ⟨A.length, Or.inr ?_⟩
  rw [filter_movePred_eq_filter_not hc hr hl]
  exact filter_append_eq_drop _ (fun a ha => by rw [hA a ha, Bool.not_true])
    (fun b hb => by rw [hB b hb, Bool.not_false])

/-- A region inside the face set meeting `l = A ++ B` exactly in `B` gives the prefix `A`. -/
theorem isEndBlock_of_split_false_true {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) {r : M.Dart}
    (hr : M.faceOf r ∈ faces) {A B : List M.Dart}
    (hl : ∀ d ∈ A ++ B, M.faceOf (M.alpha d) ∉ faces)
    (hA : ∀ a ∈ A, regionColour M (walkKeep M c) r a = false)
    (hB : ∀ b ∈ B, regionColour M (walkKeep M c) r b = true) :
    IsEndBlock (movePred M (regionColour M (walkKeep M c) r)) (A ++ B) := by
  refine ⟨A.length, Or.inl ?_⟩
  rw [filter_movePred_eq_filter_not hc hr hl]
  exact filter_append_eq_take _ (fun a ha => by rw [hA a ha, Bool.not_false])
    (fun b hb => by rw [hB b hb, Bool.not_true])

/-! ## The carrier arcs of a pocket face set -/

section Arcs

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {D : GGT.RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The darts of the target arc `t_2` lie on the boundary cycle. -/
theorem mem_cycle_of_mem_targetArc (K : PocketFaceSet D eps X lo hi) {d : X.toCombMap.Dart}
    (hd : d ∈ K.targetArc.darts) : d ∈ K.boundary.cycle := by
  rw [K.decomposition]
  exact List.mem_append_right _ hd

/-- The darts of the reversed source arc `t_1⁻¹` lie on the boundary cycle. -/
theorem mem_cycle_of_mem_invSourceArc (K : PocketFaceSet D eps X lo hi) {d : X.toCombMap.Dart}
    (hd : d ∈ invDarts X K.sourceArc.darts) : d ∈ K.boundary.cycle := by
  rw [K.decomposition]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hd))

/-- Across a dart of the target arc lies the exterior face.  Restated from
`GreendlingerLeaf/P10Rose/Live/Move.lean` (`FilterMove.faceOf_alpha_of_mem_targetArc`). -/
theorem faceOf_alpha_of_mem_targetArc (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.targetArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace := by
  have hmem : d ∈ outerDarts X := K.targetArc.mem_cycle_of_mem_darts hd
  simp only [outerDarts, List.mem_map, List.mem_reverse] at hmem
  obtain ⟨e, he, rfl⟩ := hmem
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary X.outerFace).mem_iff e).mp he

/-- Across a dart of the reversed source arc lies the source cell.  Restated from
`GreendlingerLeaf/P10Rose/Live/Move.lean` (`FilterMove.faceOf_alpha_of_mem_invSourceArc`). -/
theorem faceOf_alpha_of_mem_invSourceArc (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ invDarts X K.sourceArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X K.source).face := by
  simp only [invDarts, List.mem_map, List.mem_reverse] at hd
  obtain ⟨e, he, rfl⟩ := hd
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary (cell X K.source).face).mem_iff e).mp
    (K.sourceArc.mem_cycle_of_mem_darts he)

/-- Across the target arc lies a face outside the face set. -/
theorem alpha_not_mem_of_mem_targetArc (K : PocketFaceSet D eps X lo hi) :
    ∀ d ∈ K.targetArc.darts, X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ K.faces := by
  intro d hd
  rw [faceOf_alpha_of_mem_targetArc K hd]
  exact K.outerFace_not_mem

/-- Across the reversed source arc lies a face outside the face set. -/
theorem alpha_not_mem_of_mem_invSourceArc (K : PocketFaceSet D eps X lo hi) :
    ∀ d ∈ invDarts X K.sourceArc.darts,
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ K.faces := by
  intro d hd
  rw [faceOf_alpha_of_mem_invSourceArc K hd]
  exact K.source_not_mem

/-- **The lake case on the target arc.**  A region outside the face set that avoids the exterior
face keeps the whole target arc. -/
theorem isEndBlock_targetArc_of_lake (K : PocketFaceSet D eps X lo hi) {r : X.toCombMap.Dart}
    (hr : X.toCombMap.faceOf r ∉ K.faces)
    (hout : ∀ x, Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x →
        X.toCombMap.faceOf x ≠ X.outerFace) :
    IsEndBlock (movePred X.toCombMap
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)) K.targetArc.darts := by
  refine isEndBlock_of_forall_true fun d hd => ?_
  rw [movePred_eq_true_iff]
  exact ⟨regionColour_eq_false_of_mem K.boundary.cycle_mem_iff hr
      ((K.boundary.cycle_mem_iff d).mp (mem_cycle_of_mem_targetArc K hd)).1,
    regionColour_eq_false _ _ fun h => hout _ h (faceOf_alpha_of_mem_targetArc K hd)⟩

/-- **The lake case on the source arc.**  A region outside the face set that avoids the source
cell keeps the whole reversed source arc. -/
theorem isEndBlock_invSourceArc_of_lake (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} (hr : X.toCombMap.faceOf r ∉ K.faces)
    (hsrc : ∀ x, Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x →
        X.toCombMap.faceOf x ≠ (cell X K.source).face) :
    IsEndBlock (movePred X.toCombMap
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
      (invDarts X K.sourceArc.darts) := by
  refine isEndBlock_of_forall_true fun d hd => ?_
  rw [movePred_eq_true_iff]
  exact ⟨regionColour_eq_false_of_mem K.boundary.cycle_mem_iff hr
      ((K.boundary.cycle_mem_iff d).mp (mem_cycle_of_mem_invSourceArc K hd)).1,
    regionColour_eq_false _ _ fun h => hsrc _ h (faceOf_alpha_of_mem_invSourceArc K hd)⟩

/-- **The lake case on both arcs.** -/
theorem isEndBlock_arcs_of_lake (K : PocketFaceSet D eps X lo hi) {r : X.toCombMap.Dart}
    (hr : X.toCombMap.faceOf r ∉ K.faces)
    (hout : ∀ x, Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x →
        X.toCombMap.faceOf x ≠ X.outerFace)
    (hsrc : ∀ x, Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x →
        X.toCombMap.faceOf x ≠ (cell X K.source).face) :
    IsEndBlock (movePred X.toCombMap
        (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
        K.targetArc.darts ∧
      IsEndBlock (movePred X.toCombMap
        (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
        (invDarts X K.sourceArc.darts) :=
  ⟨isEndBlock_targetArc_of_lake K hr hout, isEndBlock_invSourceArc_of_lake K hr hsrc⟩

/-- **A region inside the face set on the target arc**: the move keeps exactly the target darts
outside the class of `r`. -/
theorem filter_targetArc_of_mem (K : PocketFaceSet D eps X lo hi) {r : X.toCombMap.Dart}
    (hr : X.toCombMap.faceOf r ∈ K.faces) :
    K.targetArc.darts.filter (movePred X.toCombMap
        (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)) =
      K.targetArc.darts.filter fun d =>
        !regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r d :=
  filter_movePred_eq_filter_not K.boundary.cycle_mem_iff hr (alpha_not_mem_of_mem_targetArc K)

/-- **A region inside the face set on the source arc**: the move keeps exactly the darts of
`t_1⁻¹` outside the class of `r`. -/
theorem filter_invSourceArc_of_mem (K : PocketFaceSet D eps X lo hi) {r : X.toCombMap.Dart}
    (hr : X.toCombMap.faceOf r ∈ K.faces) :
    (invDarts X K.sourceArc.darts).filter (movePred X.toCombMap
        (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)) =
      (invDarts X K.sourceArc.darts).filter fun d =>
        !regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r d :=
  filter_movePred_eq_filter_not K.boundary.cycle_mem_iff hr (alpha_not_mem_of_mem_invSourceArc K)

end Arcs

end GroupApproximation.Full.GL05b

#audit_axioms GroupApproximation.Full.GL05b.filter_append_eq_take
#audit_axioms GroupApproximation.Full.GL05b.filter_append_eq_drop
#audit_axioms GroupApproximation.Full.GL05b.isEndBlock_append_true_false
#audit_axioms GroupApproximation.Full.GL05b.isEndBlock_append_false_true
#audit_axioms GroupApproximation.Full.GL05b.movePred_eq_not_of_alpha_eq_false
#audit_axioms GroupApproximation.Full.GL05b.faceOf_mem_iff_of_walkEqvGen
#audit_axioms GroupApproximation.Full.GL05b.filter_movePred_eq_filter_not
#audit_axioms GroupApproximation.Full.GL05b.isEndBlock_of_split_true_false
#audit_axioms GroupApproximation.Full.GL05b.isEndBlock_of_split_false_true
#audit_axioms GroupApproximation.Full.GL05b.isEndBlock_arcs_of_lake
#audit_axioms GroupApproximation.Full.GL05b.filter_targetArc_of_mem
#audit_axioms GroupApproximation.Full.GL05b.filter_invSourceArc_of_mem
