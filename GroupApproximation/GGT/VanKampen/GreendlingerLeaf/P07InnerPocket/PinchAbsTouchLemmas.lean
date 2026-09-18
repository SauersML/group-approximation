import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsSubStatement
import GroupApproximation.GGT.VanKampen.FaceSetDualReach
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-75: a complement circuit with a given face on its side

For a face set `F` and a boundary circuit `comp` of its complement, `w' = pinchLobe_walk F comp`
(the reversed circuit, a noncrossing walk of boundary darts of `F`, `pinchLobe_nc`, `pinchLobe_bd`).

* `pinchAbsTouch_not_keep`: an edge with BOTH faces in `F` is off `w'` (a dart of `w'` has its
  reversal based off `F`).
* `pinchAbsTouch_dual_iff`: so two faces of `F` joined by a chain of `F`-internal edges
  (`Embedded.DualAdjacency X F`) are on the same side of `w'` (`mem_sideFaces_iff_of_not_walkKeep`).
* `pinchAbsTouch_mem_side`: a dart of `w'` has its face on the side of `w'`
  (`isBoundaryDart_sideFaces_iff`).
* `pinchAbsTouch_side_of_mem`: hence every face of `F` dual connected inside `F` to the face
  across a dart of the circuit is on the side of `w'`.
* `pinchAbsTouch_exists_comp`: **for every `f ∈ F`, with the exterior face off `F`, some circuit
  of the complement has `f` on the side of its reversal.**  `Embedded.exists_boundaryDart_dualConnected`
  gives a boundary dart `q` of `F` whose face is dual connected to `f` inside `F`; the circuit is
  the one through `alpha q` (as in `pinchAbs_touch_of_dart`), and `q ∈ w'`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- **An edge inside `F` is off `w'`.** -/
theorem pinchAbsTouch_not_keep {F : Finset X.toCombMap.Face}
    {comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)}
    {d : X.toCombMap.Dart} (h₁ : X.toCombMap.faceOf d ∈ F)
    (h₂ : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F) :
    ¬ walkKeep X.toCombMap (pinchLobe_walk F comp) d := by
  intro hk
  unfold walkKeep at hk
  rcases hk with hk | hk
  · exact (pinchLobe_bd (comp := comp) hk).2 h₂
  · have hb := (pinchLobe_bd (comp := comp) hk).2
    rw [X.toCombMap.alpha_involutive d] at hb
    exact hb h₁

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_not_keep

/-- **Transfer along a chain inside `F`.** -/
theorem pinchAbsTouch_dual_iff {F : Finset X.toCombMap.Face}
    {comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)}
    {g h : X.toCombMap.Face} (hc : Relation.EqvGen (Embedded.DualAdjacency X F) g h) :
    g ∈ sideFaces X.toCombMap (pinchLobe_walk F comp) ↔
      h ∈ sideFaces X.toCombMap (pinchLobe_walk F comp) := by
  induction hc with
  | rel g' h' hgh =>
      obtain ⟨hg, hh, d, rfl, rfl⟩ := hgh
      exact mem_sideFaces_iff_of_not_walkKeep _ (pinchAbsTouch_not_keep hg hh)
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_dual_iff

/-- **A dart of `w'` has its face on the side of `w'`.** -/
theorem pinchAbsTouch_mem_side {F : Finset X.toCombMap.Face}
    {comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)}
    {e : X.toCombMap.Dart} (he : e ∈ pinchLobe_walk F comp) :
    X.toCombMap.faceOf e ∈ sideFaces X.toCombMap (pinchLobe_walk F comp) :=
  (((pinchLobe_nc X.planar comp).isBoundaryDart_sideFaces_iff X.planar e).mpr he).1

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_mem_side

/-- **A face dual connected inside `F` to the face across a circuit dart is on the side.** -/
theorem pinchAbsTouch_side_of_mem {F : Finset X.toCombMap.Face}
    {comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)}
    {x : X.toCombMap.Dart}
    (hx : x ∈ FaceSetCircuits.circuit X.toCombMap (pinchLobe_out X.toCombMap F) comp)
    {g : X.toCombMap.Face}
    (hc : Relation.EqvGen (Embedded.DualAdjacency X F) g
      (X.toCombMap.faceOf (X.toCombMap.alpha x))) :
    g ∈ sideFaces X.toCombMap (pinchLobe_walk F comp) := by
  have hmem : X.toCombMap.alpha x ∈ pinchLobe_walk F comp := by
    show X.toCombMap.alpha x ∈
      invDarts X (FaceSetCircuits.circuit X.toCombMap (pinchLobe_out X.toCombMap F) comp)
    rw [Embedded.mem_invDarts_iff, X.toCombMap.alpha_involutive x]
    exact hx
  exact (pinchAbsTouch_dual_iff hc).mpr (pinchAbsTouch_mem_side hmem)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_side_of_mem

/-- **Some complement circuit has `f` on the side of its reversal.** -/
theorem pinchAbsTouch_exists_comp {F : Finset X.toCombMap.Face}
    (houter : X.outerFace ∉ F) {f : X.toCombMap.Face} (hf : f ∈ F) :
    ∃ comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F),
      f ∈ sideFaces X.toCombMap (pinchLobe_walk F comp) := by
  obtain ⟨q, hq, hconn⟩ := Embedded.exists_boundaryDart_dualConnected houter hf
  have hbd : Surgery.MapCollapse.IsBoundaryDart X.toCombMap (pinchLobe_out X.toCombMap F)
      (X.toCombMap.alpha q) := by
    refine ⟨(pinchLobe_mem_out X.toCombMap F _).mpr hq.2, ?_⟩
    rw [X.toCombMap.alpha_involutive q, pinchLobe_mem_out X.toCombMap F]
    exact fun h => h hq.1
  have hx : X.toCombMap.alpha q ∈ FaceSetCircuits.circuit X.toCombMap
      (pinchLobe_out X.toCombMap F) (Quotient.mk'' ⟨X.toCombMap.alpha q, hbd⟩) :=
    (FaceSetCircuits.mem_circuit_iff X.toCombMap (pinchLobe_out X.toCombMap F) _ _).mpr
      ⟨hbd, rfl⟩
  have hc : Relation.EqvGen (Embedded.DualAdjacency X F) f
      (X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha q))) := by
    rw [X.toCombMap.alpha_involutive q]
    exact hconn
  exact ⟨Quotient.mk'' ⟨X.toCombMap.alpha q, hbd⟩, pinchAbsTouch_side_of_mem hx hc⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_exists_comp

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
