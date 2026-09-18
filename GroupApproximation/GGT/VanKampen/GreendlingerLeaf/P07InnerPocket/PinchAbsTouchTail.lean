import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchLemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-75: the tail of ONE circuit with `f` on its side

`F = pinchAbs_set a b K G₁ G₂ f`, and for a boundary circuit `comp` of the complement of `F`,
`w' = pinchLobe_walk F comp`.

* `pinchAbsTouch_Tail`: SOME circuit `comp` has `f` on the side of `w'`, and the tail clauses
  (`pinchCut_Tail`) for `w'` given that its side is enclosed by `invDarts X w'`.  There is no
  clause (a) and no touching condition.
* `pinchAbsTouch_exists_side`: such circuits exist (`pinchAbsTouch_exists_comp`, with
  `f ∈ P₀ ⊆ F` and the exterior face off `F ⊆ side K`), including in the SEALED case where no
  dart of `P₀` has its reversal based off `F`.  So the circuit is never vacuous.
* `pinchAbsTouch_follow_of_tail`: **given `pinchAbsSub_Outside X K.walk`, the tail of one
  circuit with `f` on its side gives `pinchFollow_Conclusion` directly**, sealed or not:
  `SUB` is `pinchAbsSub_sub`, `EnclosedFaceSetSucc` is `pinchFollow_enclosed_of_turn`
  (`pinchLobe_nc`, `pinchLobe_turn`, the exterior face is off `side w' ⊆ side K`), and the dart
  clause is `pinchCut_dart_of_lobe` for EVERY boundary dart of `F` (`pinchAbs_keep_subset`,
  `pinchAbs_lobe`); the sealed alternative `pinchAbsSub_sealed` is not even needed.
* `pinchAbsTouch_tail_of_touchTail`: **LOUD: `pinchAbsSub_TouchTail → pinchAbsTouch_Tail`**,
  so the new disjunct is formally WEAKER: clause (a) gives a touching circuit
  (`pinchAbs_touch_of_dart`), which has `f` on its side (`pinchLobe_side`), and clause (c) gives
  its tail.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The tail of one circuit with `f` on its side.** -/
def pinchAbsTouch_Tail (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (f : X.toCombMap.Face) : Prop :=
  ∃ comp : FaceSetCircuits.Component X.toCombMap
      (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)),
    f ∈ sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp) ∧
    (EnclosedFaceSetSucc X
        (sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp))
        (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp)) →
      pinchCut_Tail b G₁ G₂ (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_Tail

/-- The exterior face is off `pinchAbs_set`. -/
theorem pinchAbsTouch_outer_not_mem {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) :
    X.outerFace ∉ pinchAbs_set a b K G₁ G₂ f :=
  fun h => hout (pinchAbsSub_set_subset (a := a) (b := b) (G₁ := G₁) (G₂ := G₂) hf _ h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_outer_not_mem

/-- **Some circuit has `f` on its side**, sealed or not. -/
theorem pinchAbsTouch_exists_side {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) :
    ∃ comp : FaceSetCircuits.Component X.toCombMap
        (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)),
      f ∈ sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp) :=
  pinchAbsTouch_exists_comp (pinchAbsTouch_outer_not_mem hf hout)
    (pinchAbs_keep_subset a b K G₁ G₂ f (FourPieceWitness.self_mem_keepClass a b K f))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_exists_side

/-- **The conclusion from the tail of one circuit with `f` on its side.** -/
theorem pinchAbsTouch_follow_of_tail {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap K.walk) (hCa : f ∉ a.1) (hCb : f ∉ b.1)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hO : pinchAbsSub_Outside X.toCombMap K.walk) (h : pinchAbsTouch_Tail a b K G₁ G₂ f) :
    pinchFollow_Conclusion a b K G₁ G₂ f := by
  obtain ⟨comp, hfs, htail⟩ := h
  have hsub := pinchAbsSub_sub (a := a) (b := b) (G₁ := G₁) (G₂ := G₂) hf hO comp
  have henc : EnclosedFaceSetSucc X
      (sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp))
      (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp)) :=
    pinchFollow_enclosed_of_turn (walk := pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp)
      (pinchLobe_nc X.planar comp) (fun ho => hout (hsub ho)) (pinchLobe_turn X.planar comp)
  unfold pinchFollow_Conclusion
  refine Or.inl ⟨sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp),
    invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp), henc, hfs, hsub,
    fun d hd => ?_, htail henc⟩
  exact pinchCut_dart_of_lobe hf hCa hCb (pinchAbs_keep_subset a b K G₁ G₂ f)
    (pinchAbs_lobe a b K G₁ G₂ f)
    (pinchLobe_bd (comp := comp) ((Embedded.mem_invDarts_iff _ d).mp hd))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_follow_of_tail

/-- **LOUD: clauses (a), (c) give the new disjunct.** -/
theorem pinchAbsTouch_tail_of_touchTail {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (h : pinchAbsSub_TouchTail a b K G₁ G₂ f) : pinchAbsTouch_Tail a b K G₁ G₂ f := by
  obtain ⟨⟨y, hy, hyF⟩, htail⟩ := h
  obtain ⟨comp, x, hx, hxf⟩ :=
    pinchAbs_touch_of_dart (pinchAbs_keep_subset a b K G₁ G₂ f) hy hyF
  have hmem : X.toCombMap.alpha x ∈ pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp := by
    show X.toCombMap.alpha x ∈ invDarts X (FaceSetCircuits.circuit X.toCombMap
      (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)) comp)
    rw [Embedded.mem_invDarts_iff, X.toCombMap.alpha_involutive x]
    exact hx
  have hbd : ∀ e ∈ pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp,
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap (pinchAbs_set a b K G₁ G₂ f) e :=
    fun _ he => pinchLobe_bd (comp := comp) he
  exact ⟨comp, pinchLobe_side hG₁ hG₂ (pinchAbs_keep_subset a b K G₁ G₂ f)
    (pinchAbs_lobe a b K G₁ G₂ f) hbd hmem hxf, htail comp ⟨x, hx, hxf⟩⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_tail_of_touchTail

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
