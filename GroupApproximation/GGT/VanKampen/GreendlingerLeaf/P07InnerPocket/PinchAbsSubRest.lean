import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsSubCut
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-73: what is left of `pinchAbs_Cut`

`pinchAbs_Cut = ∃ comp, touch ∧ SUB ∧ tail` (`PinchAbsCut.lean`).  `SUB` now follows for every
circuit from `pinchAbsSub_Outside X K.walk` (`pinchAbsSub_sub`), and touch from one dart
(`pinchAbs_cut_of_touch`).  What is left:
* `pinchAbsSub_TouchTail`: clause (a), one dart of `P₀` whose reversal is based off
  `pinchAbs_set`, and clause (c), the tail for every touching circuit;
* `pinchAbsSub_Rest`: `pinchAbsSub_Outside X K.walk ∧ pinchAbsSub_TouchTail`.
`pinchAbsSub_cut_of_rest`: `f ∈ side K → pinchAbsSub_Rest → pinchAbs_Cut`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Clauses (a) and (c).**  A dart of `P₀` whose reversal is based off `F = pinchAbs_set`, and
the tail for every boundary circuit of the complement of `F` touching `P₀`. -/
def pinchAbsSub_TouchTail (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (f : X.toCombMap.Face) : Prop :=
  (∃ y : X.toCombMap.Dart, X.toCombMap.faceOf y ∈ FourPieceWitness.keepClass a b K f ∧
      X.toCombMap.faceOf (X.toCombMap.alpha y) ∉ pinchAbs_set a b K G₁ G₂ f) ∧
    ∀ comp : FaceSetCircuits.Component X.toCombMap
        (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)),
      (∃ x ∈ FaceSetCircuits.circuit X.toCombMap
          (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)) comp,
        X.toCombMap.faceOf (X.toCombMap.alpha x) ∈ FourPieceWitness.keepClass a b K f) →
      EnclosedFaceSetSucc X
          (sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp))
          (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp)) →
        pinchCut_Tail b G₁ G₂ (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_TouchTail

/-- **What is left of the absorbed lobe cut**: an edge connected outside of `K.walk`, and
clauses (a) and (c). -/
def pinchAbsSub_Rest (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (f : X.toCombMap.Face) : Prop :=
  pinchAbsSub_Outside X.toCombMap K.walk ∧ pinchAbsSub_TouchTail a b K G₁ G₂ f

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_Rest

/-- **The absorbed lobe cut from the rest.** -/
theorem pinchAbsSub_cut_of_rest {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap K.walk) (h : pinchAbsSub_Rest a b K G₁ G₂ f) :
    pinchAbs_Cut a b K G₁ G₂ f := by
  obtain ⟨hO, ⟨y, hy, hyF⟩, htail⟩ := h
  exact pinchAbs_cut_of_touch (fun comp htouch => ⟨pinchAbsSub_sub hf hO comp, htail comp htouch⟩)
    hy hyF

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_cut_of_rest

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
