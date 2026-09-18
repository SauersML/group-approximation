import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsLemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-72: the lobe cut with `F = pinchAbs_set`

`pinchLobe_Cut a b K G₁ G₂ f` (`PinchLobeStatement.lean`) is
`∃ F comp, P₀ ⊆ F ∧ lobe ∧ touch ∧ SUB ∧ tail`.  With `F := pinchAbs_set a b K G₁ G₂ f` the first
two clauses are proved (`pinchAbs_keep_subset`, `pinchAbs_lobe`), so only
`∃ comp, touch ∧ SUB ∧ tail` is left: `pinchAbs_Cut`.

* `pinchAbs_lobeCut_of_cut`: `pinchAbs_Cut → pinchLobe_Cut`.
* `pinchAbs_cutOf`: `pinchAbs_Cut → pinchCut_Cut` (through `pinchLobe_cutOf`).
* `pinchAbs_cut_of_touch`: the touch clause may be given by one dart based in `P₀` whose reversal
  is based off `pinchAbs_set` (`pinchAbs_touch_of_dart`), for the circuit through its reversal.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The absorbed lobe cut.**  A boundary circuit `comp` of the complement of
`F = pinchAbs_set a b K G₁ G₂ f` touching `P₀`, whose reversal has its side on the side of
`K.walk` and satisfies the tail clauses. -/
def pinchAbs_Cut (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (f : X.toCombMap.Face) : Prop :=
  ∃ comp : FaceSetCircuits.Component X.toCombMap
      (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)),
    (∃ x ∈ FaceSetCircuits.circuit X.toCombMap
        (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)) comp,
      X.toCombMap.faceOf (X.toCombMap.alpha x) ∈ FourPieceWitness.keepClass a b K f) ∧
    sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp) ⊆
      sideFaces X.toCombMap K.walk ∧
    (EnclosedFaceSetSucc X
        (sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp))
        (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp)) →
      pinchCut_Tail b G₁ G₂ (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_Cut

/-- **An absorbed lobe cut is a lobe cut.**  `F := pinchAbs_set`, with `P₀ ⊆ F` and the lobe
condition proved. -/
theorem pinchAbs_lobeCut_of_cut {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (h : pinchAbs_Cut a b K G₁ G₂ f) : pinchLobe_Cut a b K G₁ G₂ f := by
  obtain ⟨comp, htouch, hsub, htail⟩ := h
  exact ⟨pinchAbs_set a b K G₁ G₂ f, comp, pinchAbs_keep_subset a b K G₁ G₂ f,
    pinchAbs_lobe a b K G₁ G₂ f, htouch, hsub, htail⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_lobeCut_of_cut

/-- **An absorbed lobe cut is a cut.** -/
theorem pinchAbs_cutOf {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (h : pinchAbs_Cut a b K G₁ G₂ f) : pinchCut_Cut a b K G₁ G₂ f :=
  pinchLobe_cutOf hG₁ hG₂ hout (pinchAbs_lobeCut_of_cut h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_cutOf

/-- **The absorbed lobe cut from one touching dart.**  A dart `y` based in `P₀` whose reversal is
based off `F = pinchAbs_set`, and `SUB` and the tail for the circuit through `alpha y`. -/
theorem pinchAbs_cut_of_touch {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hrest : ∀ comp : FaceSetCircuits.Component X.toCombMap
        (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)),
      (∃ x ∈ FaceSetCircuits.circuit X.toCombMap
          (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)) comp,
        X.toCombMap.faceOf (X.toCombMap.alpha x) ∈ FourPieceWitness.keepClass a b K f) →
      sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp) ⊆
        sideFaces X.toCombMap K.walk ∧
      (EnclosedFaceSetSucc X
          (sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp))
          (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp)) →
        pinchCut_Tail b G₁ G₂ (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp))))
    {y : X.toCombMap.Dart} (hy : X.toCombMap.faceOf y ∈ FourPieceWitness.keepClass a b K f)
    (hyF : X.toCombMap.faceOf (X.toCombMap.alpha y) ∉ pinchAbs_set a b K G₁ G₂ f) :
    pinchAbs_Cut a b K G₁ G₂ f := by
  obtain ⟨comp, htouch⟩ :=
    pinchAbs_touch_of_dart (pinchAbs_keep_subset a b K G₁ G₂ f) hy hyF
  exact ⟨comp, htouch, hrest comp htouch⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_cut_of_touch

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
