import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCutStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchFollowTurn
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-71: the reversed boundary circuit of the complement

Let `F` be a face set and `H = pinchLobe_out M F` its complement.  For a boundary circuit `c` of
`H` (`FaceSetCircuits.circuit M H comp`), the walk `w' = c.reverse.map alpha` (that is,
`invDarts X c`) is read with `F` on its side.  This file proves the clauses of `pinchCut_Cut`
that hold for every such `w'`:

* `pinchLobe_nc`: `w'` is noncrossing.  `c` is a first-turn walk, because each boundary walk of
  `H` is a first turn along `c` (`FirstTurn.of_boundaryWalk`), so
  `FirstTurnWalk.isNoncrossingClosedWalk_reverse` applies.
* `pinchLobe_turn`: `w'` satisfies `pinchFollow_OuterTurn`, by
  `FirstTurnWalk.outerCycle_followsBoundary` and `pinchFollow_outer_follows_iff`.
* `pinchLobe_bd`: the darts of `w'` are boundary darts of `F`.
* `pinchLobe_keep_of_boundaryDart`: if `F ⊇ P₀ = keepClass a b K c` and the faces of `F` off `P₀`
  leave `F` only across `G₁`/`G₂` edges, every boundary dart of `F` is a `Q₀` dart.  A boundary
  dart based in `P₀` is a boundary dart of `P₀` (`pinchCut_keep_of_boundaryDart`), and any other
  one is the reversal of a `G₁`/`G₂` dart, hence a dart of `K.walk`.
* `pinchLobe_side`: a walk of boundary darts of such an `F`, one of them based in `P₀`, has `c` on
  its side.  This generalizes `pinchCut_side_of_boundary` from `F = P₀`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- The complement of a face set. -/
noncomputable def pinchLobe_out (M : CombMap.{v}) (F : Finset M.Face) : Finset M.Face := by
  classical
  exact Finset.univ.filter fun g => g ∉ F

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_out

/-- Membership in the complement of a face set. -/
theorem pinchLobe_mem_out (M : CombMap.{v}) (F : Finset M.Face) (g : M.Face) :
    g ∈ pinchLobe_out M F ↔ g ∉ F := by
  classical
  unfold pinchLobe_out
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ g, h⟩⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_mem_out

/-- The reversal of a boundary dart of the complement of `F` is a boundary dart of `F`. -/
theorem pinchLobe_isBoundaryDart_alpha {M : CombMap.{v}} {F : Finset M.Face} {d : M.Dart}
    (hd : Surgery.MapCollapse.IsBoundaryDart M (pinchLobe_out M F) d) :
    Surgery.MapCollapse.IsBoundaryDart M F (M.alpha d) := by
  refine ⟨?_, ?_⟩
  · show M.faceOf (M.alpha d) ∈ F
    by_contra h
    exact hd.2 ((pinchLobe_mem_out M F _).mpr h)
  · show M.faceOf (M.alpha (M.alpha d)) ∉ F
    rw [M.alpha_involutive d]
    exact (pinchLobe_mem_out M F _).mp hd.1

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_isBoundaryDart_alpha

/-- A boundary circuit uses no edge in both directions. -/
theorem pinchLobe_alpha_not_mem {M : CombMap.{v}} {faces : Finset M.Face}
    (comp : FaceSetCircuits.Component M faces) :
    ∀ x ∈ FaceSetCircuits.circuit M faces comp,
      M.alpha x ∉ FaceSetCircuits.circuit M faces comp :=
  fun _ hx h => (pinchCut_isBoundaryDart_of_mem hx).2 (pinchCut_isBoundaryDart_of_mem h).1

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_alpha_not_mem

/-- A boundary circuit is chained by first turns along itself. -/
theorem pinchLobe_chain {M : CombMap.{v}} {faces : Finset M.Face}
    (comp : FaceSetCircuits.Component M faces) :
    (FaceSetCircuits.circuit M faces comp).IsChain
      (FirstTurn M (FaceSetCircuits.circuit M faces comp)) :=
  (FaceSetCircuits.circuit_chain M faces comp).imp fun _ _ h =>
    FirstTurn.of_boundaryWalk (c := FaceSetCircuits.circuit M faces comp) (faces := faces)
      (fun _ hd => pinchCut_isBoundaryDart_of_mem hd) h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_chain

/-- A boundary circuit is closed by a first turn along itself. -/
theorem pinchLobe_close {M : CombMap.{v}} {faces : Finset M.Face}
    (comp : FaceSetCircuits.Component M faces) :
    FirstTurn M (FaceSetCircuits.circuit M faces comp)
      ((FaceSetCircuits.circuit M faces comp).getLast
        (FaceSetCircuits.circuit_nonempty M faces comp))
      ((FaceSetCircuits.circuit M faces comp).head
        (FaceSetCircuits.circuit_nonempty M faces comp)) :=
  FirstTurn.of_boundaryWalk (c := FaceSetCircuits.circuit M faces comp) (faces := faces)
    (fun _ hd => pinchCut_isBoundaryDart_of_mem hd) (FaceSetCircuits.circuit_closes M faces comp)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_close

/-- **The reversed boundary circuit is noncrossing.** -/
theorem pinchLobe_nc {M : CombMap.{v}} (hM : M.IsPlanar) {faces : Finset M.Face}
    (comp : FaceSetCircuits.Component M faces) :
    IsNoncrossingClosedWalk M ((FaceSetCircuits.circuit M faces comp).reverse.map M.alpha) :=
  FirstTurnWalk.isNoncrossingClosedWalk_reverse hM (FaceSetCircuits.circuit_nonempty M faces comp)
    (FaceSetCircuits.circuit_nodup M faces comp) (pinchLobe_alpha_not_mem comp)
    (pinchLobe_chain comp) (pinchLobe_close comp)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_nc

/-- **The reversed boundary circuit satisfies the outer turn condition.** -/
theorem pinchLobe_turn {M : CombMap.{v}} (hM : M.IsPlanar) {faces : Finset M.Face}
    (comp : FaceSetCircuits.Component M faces) :
    pinchFollow_OuterTurn M ((FaceSetCircuits.circuit M faces comp).reverse.map M.alpha) :=
  (pinchFollow_outer_follows_iff (pinchLobe_nc hM comp) hM).mp
    (FirstTurnWalk.outerCycle_followsBoundary hM (pinchLobe_chain comp)
      (FaceSetCircuits.circuit_nonempty M faces comp) (pinchLobe_close comp)
      (pinchLobe_nc hM comp))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_turn

/-- **The darts of the reversed boundary circuit of the complement are boundary darts of `F`.** -/
theorem pinchLobe_bd {M : CombMap.{v}} {F : Finset M.Face}
    {comp : FaceSetCircuits.Component M (pinchLobe_out M F)} {e : M.Dart}
    (he : e ∈ (FaceSetCircuits.circuit M (pinchLobe_out M F) comp).reverse.map M.alpha) :
    Surgery.MapCollapse.IsBoundaryDart M F e := by
  have h := pinchLobe_isBoundaryDart_alpha
    (pinchCut_isBoundaryDart_of_mem (FirstTurnWalk.mem_reverse_map_alpha_iff.mp he))
  rw [M.alpha_involutive e] at h
  exact h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_bd

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- The reversal of a `G₁` dart is a dart of `K.walk`. -/
theorem pinchLobe_mem_walk_one {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    {e : X.toCombMap.Dart} (he : X.toCombMap.alpha e ∈ G₁.darts) : e ∈ K.walk := by
  have h1 : X.toCombMap.alpha e ∈ K.firstArc.darts := by
    rw [hG₁]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr he)))
  have h2 : e ∈ invDarts X K.firstArc.darts :=
    (Embedded.mem_invDarts_iff K.firstArc.darts e).mpr h1
  show e ∈ K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++
    invDarts X K.secondArc.darts
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
    (List.mem_append.mpr (Or.inr h2)))))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_mem_walk_one

/-- The reversal of a `G₂` dart is a dart of `K.walk`. -/
theorem pinchLobe_mem_walk_two {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₂ : CyclicArc (cellDarts X j)}
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {e : X.toCombMap.Dart} (he : X.toCombMap.alpha e ∈ G₂.darts) : e ∈ K.walk := by
  have h1 : X.toCombMap.alpha e ∈ K.secondArc.darts := by
    rw [hG₂]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr he)))
  have h2 : e ∈ invDarts X K.secondArc.darts :=
    (Embedded.mem_invDarts_iff K.secondArc.darts e).mpr h1
  show e ∈ K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++
    invDarts X K.secondArc.darts
  exact List.mem_append.mpr (Or.inr h2)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_mem_walk_two

/-- **A boundary dart of a lobe-closed face set is a `Q₀` dart.**  `F ⊇ P₀ = keepClass a b K c`,
and a dart based in `F` off `P₀` leaving `F` is the reversal of a `G₁`/`G₂` dart. -/
theorem pinchLobe_keep_of_boundaryDart {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {c : X.toCombMap.Face} {F : Finset X.toCombMap.Face}
    (hsub : FourPieceWitness.keepClass a b K c ⊆ F)
    (hlobe : ∀ e : X.toCombMap.Dart, X.toCombMap.faceOf e ∈ F →
      X.toCombMap.faceOf e ∉ FourPieceWitness.keepClass a b K c →
      X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ F →
      X.toCombMap.alpha e ∈ G₁.darts ∨ X.toCombMap.alpha e ∈ G₂.darts)
    {e : X.toCombMap.Dart} (he : Surgery.MapCollapse.IsBoundaryDart X.toCombMap F e) :
    PocketClass.pocketKeep a b K e := by
  rcases Classical.em (X.toCombMap.faceOf e ∈ FourPieceWitness.keepClass a b K c) with hk | hk
  · exact pinchCut_keep_of_boundaryDart (c := c) ⟨hk, fun h => he.2 (hsub h)⟩
  · have hK : e ∈ K.walk := by
      rcases hlobe e he.1 hk he.2 with h | h
      · exact pinchLobe_mem_walk_one hG₁ h
      · exact pinchLobe_mem_walk_two hG₂ h
    exact Or.inl (Or.inl hK)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_keep_of_boundaryDart

/-- **`c` lies on the side of a walk of boundary darts of a lobe-closed face set**, provided one
of its darts is based in `P₀`.  Every edge of the walk is a `Q₀` edge, so the `Q₀`-class of `c`
refines the side classes of the walk. -/
theorem pinchLobe_side {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {c : X.toCombMap.Face} {F : Finset X.toCombMap.Face}
    (hsub : FourPieceWitness.keepClass a b K c ⊆ F)
    (hlobe : ∀ e : X.toCombMap.Dart, X.toCombMap.faceOf e ∈ F →
      X.toCombMap.faceOf e ∉ FourPieceWitness.keepClass a b K c →
      X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ F →
      X.toCombMap.alpha e ∈ G₁.darts ∨ X.toCombMap.alpha e ∈ G₂.darts)
    {w' : List X.toCombMap.Dart}
    (hbd : ∀ d ∈ w', Surgery.MapCollapse.IsBoundaryDart X.toCombMap F d)
    {e : X.toCombMap.Dart} (he : e ∈ w')
    (hec : X.toCombMap.faceOf e ∈ FourPieceWitness.keepClass a b K c) :
    c ∈ sideFaces X.toCombMap w' := by
  obtain ⟨y, hy, hye⟩ := (PocketNoncrossing.faceOf_mem_faceClass_iff X.toCombMap
    (PocketClass.pocketKeep a b K) c e).mp hec
  have hkk : ∀ x, ¬ PocketClass.pocketKeep a b K x → ¬ walkKeep X.toCombMap w' x := by
    intro x hx hk
    rcases (show x ∈ w' ∨ X.toCombMap.alpha x ∈ w' from hk) with h | h
    · exact hx (pinchLobe_keep_of_boundaryDart hG₁ hG₂ hsub hlobe (hbd x h))
    · exact hx ((pinchCut_pocketKeep_alpha a b K x).mp
        (pinchLobe_keep_of_boundaryDart hG₁ hG₂ hsub hlobe (hbd _ h)))
  have hs := (mem_sideFaces_iff X.toCombMap w' y).mpr
    ⟨e, he, Relation.EqvGen.symm _ _ (SimpleClosedWalkSides.faceClass_mono X.toCombMap
      (keep := PocketClass.pocketKeep a b K) (keep' := walkKeep X.toCombMap w') hkk hye)⟩
  rw [hy] at hs
  exact hs

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_side

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
