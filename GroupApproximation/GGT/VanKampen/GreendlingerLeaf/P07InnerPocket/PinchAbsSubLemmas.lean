import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsStatement
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-73: transfer lemmas for the side of `w'`

For a face set `F` and a boundary circuit `comp` of its complement, `w' = pinchLobe_walk F comp`.
* `pinchAbsSub_walk_mem`: every dart of `w'` is based in `F` (`pinchLobe_bd`).
* `pinchAbsSub_transfer`: an edge with both faces off `F` is off `w'`, so its two faces are on
  the same side of `w'` (`mem_sideFaces_iff_of_not_walkKeep`).
* `pinchAbsSub_circuit_not_mem`: the face of a circuit dart is off the side of `w'` (the reversal
  of a circuit dart is a dart of the noncrossing walk `w'`, `pinchLobe_nc`, and a walk keeps the
  face across each of its darts off its side, `isBoundaryDart_sideFaces_iff`).
* `pinchAbsSub_OutAdj`: two faces off the side of a walk `w` that share an edge.
  `pinchAbsSub_out_iff`: when `F ⊆ sideFaces w`, a chain of `pinchAbsSub_OutAdj` steps joins
  faces on the same side of `w'` (every step is an edge with both faces off `F`).
The `pinchAbs_set` specific lemmas (`pinchAbsSub_set_subset`, `pinchAbsSub_not_mem_set`,
`pinchAbsSub_reach_iff`) are in `PinchAbsSubSub.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- Every dart of `w'` is based in `F`. -/
theorem pinchAbsSub_walk_mem {F : Finset X.toCombMap.Face}
    {comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)}
    {e : X.toCombMap.Dart} (he : e ∈ pinchLobe_walk F comp) : X.toCombMap.faceOf e ∈ F :=
  (pinchLobe_bd (comp := comp) he).1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_walk_mem

/-- **Transfer across an edge off `F`.** -/
theorem pinchAbsSub_transfer {F : Finset X.toCombMap.Face}
    {comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)}
    {d : X.toCombMap.Dart} (h₁ : X.toCombMap.faceOf d ∉ F)
    (h₂ : X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ F) :
    X.toCombMap.faceOf d ∈ sideFaces X.toCombMap (pinchLobe_walk F comp) ↔
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
        sideFaces X.toCombMap (pinchLobe_walk F comp) := by
  refine mem_sideFaces_iff_of_not_walkKeep (pinchLobe_walk F comp) ?_
  intro hk
  unfold walkKeep at hk
  rcases hk with hk | hk
  · exact h₁ (pinchAbsSub_walk_mem hk)
  · exact h₂ (pinchAbsSub_walk_mem hk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_transfer

/-- **A circuit face is off the side of `w'`.** -/
theorem pinchAbsSub_circuit_not_mem {F : Finset X.toCombMap.Face}
    {comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)}
    {x : X.toCombMap.Dart}
    (hx : x ∈ FaceSetCircuits.circuit X.toCombMap (pinchLobe_out X.toCombMap F) comp) :
    X.toCombMap.faceOf x ∉ sideFaces X.toCombMap (pinchLobe_walk F comp) := by
  have hmem : X.toCombMap.alpha x ∈
      (FaceSetCircuits.circuit X.toCombMap (pinchLobe_out X.toCombMap F) comp).reverse.map
        X.toCombMap.alpha :=
    FirstTurnWalk.mem_reverse_map_alpha_iff.mpr (by rw [X.toCombMap.alpha_involutive x]; exact hx)
  have hb := (((pinchLobe_nc X.planar comp).isBoundaryDart_sideFaces_iff X.planar
    (X.toCombMap.alpha x)).mpr hmem).2
  rw [X.toCombMap.alpha_involutive x] at hb
  exact hb

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_circuit_not_mem

/-- Two faces off the side of `w` sharing an edge. -/
def pinchAbsSub_OutAdj (M : CombMap.{v}) (w : List M.Dart) (g h : M.Face) : Prop :=
  g ∉ sideFaces M w ∧ h ∉ sideFaces M w ∧ ∃ d : M.Dart, M.faceOf d = g ∧ M.faceOf (M.alpha d) = h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_OutAdj

/-- **Transfer along an outside chain.** -/
theorem pinchAbsSub_out_iff {F : Finset X.toCombMap.Face} {w₀ : List X.toCombMap.Dart}
    {comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)}
    (hF : ∀ g, g ∈ F → g ∈ sideFaces X.toCombMap w₀) {g h : X.toCombMap.Face}
    (hc : Relation.ReflTransGen (pinchAbsSub_OutAdj X.toCombMap w₀) g h) :
    g ∈ sideFaces X.toCombMap (pinchLobe_walk F comp) ↔
      h ∈ sideFaces X.toCombMap (pinchLobe_walk F comp) := by
  induction hc with
  | refl => exact Iff.rfl
  | tail _ hst ih =>
      unfold pinchAbsSub_OutAdj at hst
      obtain ⟨hb, hc', d, rfl, rfl⟩ := hst
      exact ih.trans (pinchAbsSub_transfer (fun h' => hb (hF _ h')) (fun h' => hc' (hF _ h')))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_out_iff

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
