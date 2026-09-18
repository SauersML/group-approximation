import GroupApproximation.Manuscript.NonMF.Full.GL05b.RegionArcs
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleaving
import GroupApproximation.Meta.AxiomGuard

/-!
# The extremal end-block statement of work order WO-GL05-2'

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, through Lemma 4.4.  This is item 1 of "Part (b)" in the docstring of
`GreendlingerLeaf/P10RoseExtremalTrim/Reduction.lean`: an extremal region meets both carrier arcs
in end blocks.

* `ExtremalEndBlockStatement`: the work order as stated.  It takes the hypotheses of
  `P10RoseExtremalTrim.RoseExtremalJunctionStatement` and asks for one dart `r` with
  `ExtremalEndBlockConclusion K r`.  That conclusion says the face class of `r` meets the boundary
  cycle and avoids the exterior face, the move leaves the source cell out and keeps the kept cell,
  and on `t_2` and on `t_1⁻¹` the kept darts form an end block.
* `extremalEndBlock_of_lake` (corrected form, proved): the conclusion holds for any dart `r`
  outside the face set whose class meets the cycle and avoids the exterior face and the source cell.
* `extremalEndBlock_of_region` (corrected form, proved): the conclusion holds for a dart `r` inside
  the face set whose class meets the cycle, misses a dart of the kept cell, and splits each arc
  into a coloured part and an uncoloured part (`IsSplit`).

## Why the existential form fails

The predicates `FirstTurn`, `PocketFaceSet.FirstTurns`, `Unpinched`, `TurnCrossed`,
`NonFirstTurn`, `AllNonFirstTurnsCrossed` and `flipFaces` are restated here with the same bodies.
Their modules are not wired, and `P10Rose/Live/Move.lean` is a WIP snapshot.

Counterexample (16 darts; lane GL05c status file):
* Vertices `w`, `u`, `z`.
* Loops `p` and `e` at `w`, `q1` at `u` and `q2` at `z`.
* Double edges `R1a : w → u`, `R1b : u → w` and `R2a : w → z`, `R2b : z → w`.
* `K.faces = {P, R1, Q1, R2, Q2}`.
* The source cell `S` has boundary `[αR2b, αq2, αR2a, e2]`.
* The exterior has boundary `[αp, αR1b, αq1, αR1a, e1]`.
* The cycle is `[] ++ [R2a, q2, R2b] ++ [p] ++ [R1a, q1, R1b]`.

In that model:
* The three passages at `w` pairwise cross, and the other turns are first turns.
* The face classes are `O ∪ S`, `P`, `R1`, `Q1`, `R2` and `Q2`, so there is no lake.
* Every region fails at least one conjunct.
  * `O ∪ S` meets the exterior.
  * `P` flips the kept cell.
  * `R1` leaves `[q1]` on `t_2`, which is not an end block.
  * `Q1` leaves `[R1a, R1b]`.
  * `R2` and `Q2` fail in the same way on `t_1⁻¹`.

Flipping `R1` and `Q1` together does give a valid listing, so this refutes only the single-region
form, not the multi-region move.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`, tex 2121, Hull's small cancellation
theorem, through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL05c

universe u w v

open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-! ## Local restatements (same bodies as on origin/main) -/

/-- **A first turn** from `x` to `y` along the edges of `c`.  Restated from
`Estimating/OsinPocketFirstTurnWalk.lean` (`FirstTurn`). -/
def FirstTurn (M : CombMap.{v}) (c : List M.Dart) (x y : M.Dart) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (M.sigma ^ k) (M.alpha x) = y ∧
    ∀ t, 0 < t → t < k → ¬ walkKeep M c ((M.sigma ^ t) (M.alpha x))

/-- **An unpinched face set**: no vertex carries two boundary darts.  Restated from
`Estimating/OsinPocketRegionUnpinched.lean` (`Surgery.MapCollapse.Unpinched`). -/
def Unpinched (M : CombMap.{v}) (faces : Finset M.Face) : Prop :=
  ∀ x y : M.Dart, Surgery.MapCollapse.IsBoundaryDart M faces x →
    Surgery.MapCollapse.IsBoundaryDart M faces y → M.vertexOf x = M.vertexOf y → x = y

/-- **The face set after a move**: the faces whose membership in `faces` agrees with `z = false`.
Restated from `GreendlingerLeaf/P10Rose/Live/Move.lean` (`FilterMove.flipFaces`). -/
noncomputable def flipFaces (M : CombMap.{v}) (faces : Finset M.Face) (z : M.Dart → Bool) :
    Finset M.Face := by
  classical
  exact Finset.univ.filter fun f => ∃ x, M.faceOf x = f ∧ (M.faceOf x ∈ faces ↔ z x = false)

/-- Membership in `flipFaces`. -/
theorem mem_flipFaces_iff {M : CombMap.{v}} {faces : Finset M.Face} {z : M.Dart → Bool}
    {f : M.Face} :
    f ∈ flipFaces M faces z ↔ ∃ x, M.faceOf x = f ∧ (M.faceOf x ∈ faces ↔ z x = false) := by
  rw [flipFaces, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ f)

/-- A dart whose membership agrees with `z = false` puts its face in `flipFaces`. -/
theorem faceOf_mem_flipFaces {M : CombMap.{v}} {faces : Finset M.Face} {z : M.Dart → Bool}
    {x : M.Dart} (hx : M.faceOf x ∈ faces ↔ z x = false) :
    M.faceOf x ∈ flipFaces M faces z :=
  mem_flipFaces_iff.mpr ⟨x, rfl, hx⟩

/-- A face none of whose darts has membership agreeing with `z = false` is not in `flipFaces`. -/
theorem not_mem_flipFaces {M : CombMap.{v}} {faces : Finset M.Face} {z : M.Dart → Bool}
    {f : M.Face} (h : ∀ x, M.faceOf x = f → ¬(M.faceOf x ∈ faces ↔ z x = false)) :
    f ∉ flipFaces M faces z := by
  rw [mem_flipFaces_iff]
  rintro ⟨x, hx, hiff⟩
  exact h x hx hiff

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {D : GGT.RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A pocket in first-turn order.**  Restated from `Estimating/OsinPocketPinchFirstTurn.lean`
(`PocketFaceSet.FirstTurns`). -/
def FirstTurns (K : PocketFaceSet D eps X lo hi) : Prop :=
  K.boundary.cycle.IsChain (fun d e => FirstTurn X.toCombMap
      (K.boundary.cycle.reverse.map X.toCombMap.alpha) (X.toCombMap.alpha e)
      (X.toCombMap.alpha d)) ∧
    FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha (K.boundary.cycle.head K.boundary.cycle_nonempty))
      (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))

open Classical in
/-- **A crossed turn.**  Restated from `GreendlingerLeaf/P10ChordLift/Predicate.lean`
(`P10ChordLift.TurnCrossed`). -/
def TurnCrossed (K : PocketFaceSet D eps X lo hi) (d₀ : X.toCombMap.Dart)
    (hd₀ : d₀ ∈ K.boundary.cycle) : Prop :=
  ∃ (d : X.toCombMap.Dart) (hd : d ∈ K.boundary.cycle), d ≠ d₀ ∧
    X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) ∧
    ¬ (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha d) ↔
        RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (K.boundary.cycle.next d hd))

open Classical in
/-- **A non-first turn.**  Restated from `GreendlingerLeaf/P10ChordLift/Predicate.lean`
(`P10ChordLift.NonFirstTurn`). -/
def NonFirstTurn (K : PocketFaceSet D eps X lo hi) (d₀ : X.toCombMap.Dart)
    (hd₀ : d₀ ∈ K.boundary.cycle) : Prop :=
  ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
    (X.toCombMap.alpha (K.boundary.cycle.next d₀ hd₀)) (X.toCombMap.alpha d₀)

/-- **The rose configuration.**  Restated from `GreendlingerLeaf/P10ChordLift/Predicate.lean`
(`P10ChordLift.AllNonFirstTurnsCrossed`). -/
def AllNonFirstTurnsCrossed (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle),
    NonFirstTurn K d₀ hd₀ → TurnCrossed K d₀ hd₀

/-- **The conclusion of WO-GL05-2' for one dart `r`**: the class of `r` meets the boundary cycle
and avoids the exterior face, the move leaves the source cell out and keeps the kept cell, and on
both carrier arcs the kept darts form an end block (Osin, Lemma 9.7(b), toward `thm:hull`). -/
def ExtremalEndBlockConclusion (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) : Prop :=
  (∃ y ∈ K.boundary.cycle, Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
        (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
    (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
    (cell X K.source).face ∉ flipFaces X.toCombMap K.faces
      (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
    (cell X K.kept).face ∈ flipFaces X.toCombMap K.faces
      (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
    GL05b.IsEndBlock (GL05b.movePred X.toCombMap
      (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
      K.targetArc.darts ∧
    GL05b.IsEndBlock (GL05b.movePred X.toCombMap
      (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
      (invDarts X K.sourceArc.darts)

/-! ## The corrected witnesses -/

/-- **The lake witness** (corrected form of WO-GL05-2', Osin Lemma 9.7(b), toward `thm:hull` in
`non_mf_groups_exist.tex`).  A dart outside the face set whose class meets the boundary cycle and
avoids the exterior face and the source cell satisfies the conclusion. -/
theorem extremalEndBlock_of_lake (K : PocketFaceSet D eps X lo hi) {r : X.toCombMap.Dart}
    (hr : X.toCombMap.faceOf r ∉ K.faces)
    (hy : ∃ y ∈ K.boundary.cycle, Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
        (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y))
    (hout : ∀ x, Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x →
        X.toCombMap.faceOf x ≠ X.outerFace)
    (hsrc : ∀ x, Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x →
        X.toCombMap.faceOf x ≠ (cell X K.source).face) :
    ExtremalEndBlockConclusion K r := by
  refine ⟨hy, fun x hx h => hout x h hx, ?_, ?_,
    GL05b.isEndBlock_arcs_of_lake K hr hout hsrc⟩
  · refine not_mem_flipFaces fun x hx hiff => ?_
    have hnot : X.toCombMap.faceOf x ∉ K.faces := by
      rw [hx]
      exact K.source_not_mem
    exact hnot (hiff.mpr (GL05b.regionColour_eq_false _ _ fun h => hsrc x h hx))
  · obtain ⟨x, hxmem⟩ :=
      List.exists_mem_of_ne_nil _ (X.faceBoundary (cell X K.kept).face).nonempty
    have hxf : X.toCombMap.faceOf x = (cell X K.kept).face :=
      ((X.faceBoundary (cell X K.kept).face).mem_iff x).mp hxmem
    have hin : X.toCombMap.faceOf x ∈ K.faces := by
      rw [hxf]
      exact K.kept_mem
    rw [← hxf]
    exact faceOf_mem_flipFaces
      ⟨fun _ => GL05b.regionColour_eq_false_of_mem K.boundary.cycle_mem_iff hr hin,
        fun _ => hin⟩

/-- **A split of a list by a colouring**: a coloured part followed by an uncoloured part, or the
other way round. -/
def IsSplit {α : Type*} (z : α → Bool) (l : List α) : Prop :=
  ∃ A B : List α, l = A ++ B ∧
    (((∀ a ∈ A, z a = true) ∧ ∀ b ∈ B, z b = false) ∨
      ((∀ a ∈ A, z a = false) ∧ ∀ b ∈ B, z b = true))

/-- A region inside the face set that splits a list with far sides outside gives an end block. -/
theorem isEndBlock_of_isSplit {M : CombMap.{v}} {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) {r : M.Dart}
    (hr : M.faceOf r ∈ faces) {l : List M.Dart}
    (hl : ∀ d ∈ l, M.faceOf (M.alpha d) ∉ faces)
    (hs : IsSplit (GL05b.regionColour M (walkKeep M c) r) l) :
    GL05b.IsEndBlock (GL05b.movePred M (GL05b.regionColour M (walkKeep M c) r)) l := by
  obtain ⟨A, B, rfl, ⟨hA, hB⟩ | ⟨hA, hB⟩⟩ := hs
  · exact GL05b.isEndBlock_of_split_true_false hc hr hl hA hB
  · exact GL05b.isEndBlock_of_split_false_true hc hr hl hA hB

/-- **The region witness** (corrected form of WO-GL05-2', Osin Lemma 9.7(b), toward `thm:hull`
in `non_mf_groups_exist.tex`).  A dart inside the face set whose class meets the boundary cycle,
misses some dart of the kept cell, and splits both carrier arcs satisfies the conclusion. -/
theorem extremalEndBlock_of_region (K : PocketFaceSet D eps X lo hi) {r : X.toCombMap.Dart}
    (hr : X.toCombMap.faceOf r ∈ K.faces)
    (hy : ∃ y ∈ K.boundary.cycle, Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
        (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y))
    (hkept : ∃ x, X.toCombMap.faceOf x = (cell X K.kept).face ∧ ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x)
    (htarget : IsSplit (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)
      K.targetArc.darts)
    (hsource : IsSplit (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)
      (invDarts X K.sourceArc.darts)) :
    ExtremalEndBlockConclusion K r := by
  refine ⟨hy, ?_, ?_, ?_,
    isEndBlock_of_isSplit K.boundary.cycle_mem_iff hr (GL05b.alpha_not_mem_of_mem_targetArc K)
      htarget,
    isEndBlock_of_isSplit K.boundary.cycle_mem_iff hr
      (GL05b.alpha_not_mem_of_mem_invSourceArc K) hsource⟩
  · intro x hx h
    have hmem := (GL05b.faceOf_mem_iff_of_walkEqvGen K.boundary.cycle_mem_iff h).mp hr
    rw [hx] at hmem
    exact K.outerFace_not_mem hmem
  · refine not_mem_flipFaces fun x hx hiff => ?_
    have hnot : X.toCombMap.faceOf x ∉ K.faces := by
      rw [hx]
      exact K.source_not_mem
    exact hnot (hiff.mpr (GL05b.regionColour_eq_false_of_not_mem K.boundary.cycle_mem_iff hr hnot))
  · obtain ⟨x, hxf, hnx⟩ := hkept
    have hin : X.toCombMap.faceOf x ∈ K.faces := by
      rw [hxf]
      exact K.kept_mem
    rw [← hxf]
    exact faceOf_mem_flipFaces ⟨fun _ => GL05b.regionColour_eq_false _ _ hnx, fun _ => hin⟩

end Pocket

/-- **Work order WO-GL05-2'** (item 1 of Part (b) of Osin's Lemma 9.7(b), toward `thm:hull` in
`non_mf_groups_exist.tex`): under the hypotheses of
`P10RoseExtremalTrim.RoseExtremalJunctionStatement`, some dart `r` satisfies
`ExtremalEndBlockConclusion`.  The module docstring describes a model where this fails;
`extremalEndBlock_of_lake` and `extremalEndBlock_of_region` are the corrected forms. -/
def ExtremalEndBlockStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ FirstTurns K →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, ExtremalEndBlockConclusion K r

end GroupApproximation.Full.GL05c

#audit_axioms GroupApproximation.Full.GL05c.mem_flipFaces_iff
#audit_axioms GroupApproximation.Full.GL05c.faceOf_mem_flipFaces
#audit_axioms GroupApproximation.Full.GL05c.not_mem_flipFaces
#audit_axioms GroupApproximation.Full.GL05c.extremalEndBlock_of_lake
#audit_axioms GroupApproximation.Full.GL05c.isEndBlock_of_isSplit
#audit_axioms GroupApproximation.Full.GL05c.extremalEndBlock_of_region
#audit_axioms GroupApproximation.Full.GL05c.ExtremalEndBlockStatement
