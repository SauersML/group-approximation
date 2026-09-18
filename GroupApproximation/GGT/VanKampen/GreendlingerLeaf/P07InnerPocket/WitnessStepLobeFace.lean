import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepOrderStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerFace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkOrder
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-64: the reverse of every curve entry is off the witness

Lane gl-p07-64.  Write `w = witnessSublistCurve a b G₁ G₂` and `F = witnessFaces a b K c`, with
`c ∉ a.1` and `c ∉ b.1`.  This module proves that **every** entry `e` of `w` has
`faceOf (alpha e) ∉ F` (`witnessStepLobe_faceOf_alpha_not_mem_of_mem_curve`).  This settles
clause 2 of `witnessStepOrder_CycleStatement` for the collapsed set `univ \ F`
(`witnessStepLobe_alpha_mem_rotate_of_mem_curve`).  It certifies no printed sentence on its own.
NOT COMPILED: authored without running Lean.

## Proof, by the four blocks of `w`

* `invDarts X G₁.darts` and `cellG2Word ⊆ invDarts X G₂.darts`: `alpha e` lies on the first or
  the second arc of `K`, so `e ∈ K.walk` (`CellPocketWalkOrder.mem_walk_iff`).  The reverse of a
  walk dart is off `sideFaces K.walk` (`faceOf_alpha_not_mem_sideFaces`), and `F ⊆ sideFaces`.
* `sideAWord`: `alpha e ∈ a.sideFrom j`, so `faceOf (alpha e) ∈ a.1`
  (`witnessStepCorner_faceOf_mem_of_mem_sideFrom`).  A witness face is off `a`
  (`not_mem_left_of_mem_witnessFaces`).
* `sideBWord`: the same, with `b.sideFrom i` and `not_mem_right_of_mem_witnessFaces`.

This is risk case (i) of the gl-p07-63 status: an `F`-faced entry `e` of `invDarts X G₁.darts`
is always a boundary dart of `univ \ F`, so it is on the outer walk.  It cannot lie off the lobe
boundary.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section LobeFace

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- An entry of the inverse first cell gap lies on the pocket walk. -/
theorem witnessStepLobe_mem_walk_of_mem_invG1 {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    {e : X.toCombMap.Dart} (he : e ∈ invDarts X G₁.darts) : e ∈ K.walk := by
  have h : X.toCombMap.alpha e ∈ K.firstArc.darts := by
    rw [hG₁]
    exact List.mem_append_left _
      (List.mem_append_right _ ((Embedded.mem_invDarts_iff _ _).mp he))
  exact (CellPocketWalkOrder.mem_walk_iff K e).mpr (Or.inr (Or.inl h))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_mem_walk_of_mem_invG1

/-- An entry of the inverse second cell gap lies on the pocket walk. -/
theorem witnessStepLobe_mem_walk_of_mem_invG2 {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₂ : CyclicArc (cellDarts X j)}
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {e : X.toCombMap.Dart} (he : e ∈ invDarts X G₂.darts) : e ∈ K.walk := by
  have h : X.toCombMap.alpha e ∈ K.secondArc.darts := by
    rw [hG₂]
    exact List.mem_append_left _
      (List.mem_append_right _ ((Embedded.mem_invDarts_iff _ _).mp he))
  exact (CellPocketWalkOrder.mem_walk_iff K e).mpr (Or.inr (Or.inr (Or.inr h)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_mem_walk_of_mem_invG2

/-- The reverse of a pocket walk dart is off the witness. -/
theorem witnessStepLobe_faceOf_alpha_not_mem_of_mem_walk {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) {e : X.toCombMap.Dart}
    (he : e ∈ K.walk) :
    X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ witnessFaces a b K c := fun h =>
  CellPocketWalkOrder.faceOf_alpha_not_mem_sideFaces X.planar hw he
    (witnessFaces_subset_sideFaces h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_faceOf_alpha_not_mem_of_mem_walk

/-- The reverse of an entry of the `A` block lies on `a.sideFrom j`. -/
theorem witnessStepLobe_alpha_mem_of_mem_sideAWord {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {e : X.toCombMap.Dart}
    (he : e ∈ FourBlock.sideAWord a b G₁ G₂) : X.toCombMap.alpha e ∈ a.sideFrom j := by
  unfold FourBlock.sideAWord at he
  exact (Embedded.mem_invDarts_iff _ _).mp (List.mem_filter.mp he).1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_alpha_mem_of_mem_sideAWord

/-- **The reverse of every curve entry is off the witness.** -/
theorem witnessStepLobe_faceOf_alpha_not_mem_of_mem_curve {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) (hca : c ∉ a.1) (hcb : c ∉ b.1)
    {G₁ : CyclicArc (cellDarts X i)}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    {G₂ : CyclicArc (cellDarts X j)}
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {e : X.toCombMap.Dart} (he : e ∈ witnessSublistCurve a b G₁ G₂) :
    X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ witnessFaces a b K c := by
  unfold witnessSublistCurve at he
  rcases List.mem_append.mp he with he | hB
  · rcases List.mem_append.mp he with he | hG
    · rcases List.mem_append.mp he with h1 | hA
      · exact witnessStepLobe_faceOf_alpha_not_mem_of_mem_walk hw
          (witnessStepLobe_mem_walk_of_mem_invG1 hG₁ h1)
      · intro hF
        exact not_mem_left_of_mem_witnessFaces hca hF
          (witnessStepCorner_faceOf_mem_of_mem_sideFrom a j
            (witnessStepLobe_alpha_mem_of_mem_sideAWord hA))
    · exact witnessStepLobe_faceOf_alpha_not_mem_of_mem_walk hw
        (witnessStepLobe_mem_walk_of_mem_invG2 hG₂ (FourBlock.mem_cellG2Word hG).2)
  · intro hF
    exact not_mem_right_of_mem_witnessFaces hcb hF
      (witnessStepCorner_faceOf_mem_of_mem_sideFrom b i (FourBlock.mem_sideBWord hB).2.2)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_faceOf_alpha_not_mem_of_mem_curve

/-- **Clause 2 of the Cycle statement for the collapsed set.**  A curve entry `e` with its face
in the witness has `alpha e` on every rotation of the outer walk: `faceOf (alpha e) ∉ F` and
`faceOf e ∈ F`, so `mem_iff` puts `alpha e` on the walk. -/
theorem witnessStepLobe_alpha_mem_rotate_of_mem_curve {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) (hca : c ∉ a.1) (hcb : c ∉ b.1)
    {G₁ : CyclicArc (cellDarts X i)}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    {G₂ : CyclicArc (cellDarts X j)}
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X (witnessFaces a b K c) ow)
    (r : ℕ) {e : X.toCombMap.Dart} (he : e ∈ witnessSublistCurve a b G₁ G₂)
    (hF : X.toCombMap.faceOf e ∈ witnessFaces a b K c) :
    X.toCombMap.alpha e ∈ ow.rotate r := by
  refine List.mem_rotate.mpr ((E.mem_iff (X.toCombMap.alpha e)).mpr
    ⟨witnessStepLobe_faceOf_alpha_not_mem_of_mem_curve hw hca hcb hG₁ hG₂ he, Or.inl ?_⟩)
  rw [X.toCombMap.alpha_involutive e]
  exact hF

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_alpha_mem_rotate_of_mem_curve

end LobeFace

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
