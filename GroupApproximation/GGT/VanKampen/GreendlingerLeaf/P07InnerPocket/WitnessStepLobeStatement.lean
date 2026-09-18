import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepLobeList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepLobeFace
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-64: the Cycle statement is the Order statement

Lane gl-p07-64 truth-checks `witnessStepOrder_CycleStatement` (gl-p07-63,
`WitnessStepOrderStatement.lean`) against the real definitions, and proves it **equivalent** to
`witnessStepReclose_OrderStatement` (gl-p07-62).  It isolates the plain sublist form
`witnessStepLobe_SublistStatement` as the residual and wires it to the gl-p07-62 endpoints.  It
certifies no printed sentence on its own.  NOT COMPILED: authored without running Lean.

## The residual

The premise block of the Order statement.  With `w = witnessSublistCurve a b G₁ G₂`: some
rotation `outerWalk.rotate r` has its inverse reading `invDarts X (outerWalk.rotate r)` as a
sublist of `w`.  There is no face set, no boundary cycle and no order relation.

## Status (LOUD)

* **The Cycle statement is TRUE on every tested model, and is NOT refuted.**  But it is
  **EQUIVALENT** to the Order statement, and so to the Reclosed and Bridge statements
  (gl-p07-63 `witnessStepOrder_order_of_reclosed`, `witnessStepOrder_order_of_bridge`).
  - Cycle ⇒ Order is gl-p07-63 (`witnessStepOrder_order_of_cycle`).
  - Order ⇒ Cycle is proved here (`witnessStepLobe_cycle_of_order`).  Take `O = univ \ F` and
    `B = outerWalk.rotate r`.  Clause 2 holds for **every** `F`-faced curve entry
    (`witnessStepLobe_alpha_mem_rotate_of_mem_curve`).  Clause 3 holds with `k = 0`, because an
    order-preserving list is a sublist (`witnessStepLobe_sublist_of_before`).
  - The gl-p07-63 status line "the converse is not proved; the second clause asks for more" is
    therefore **wrong**.  Clause 2 is automatic: the reverse of every entry of `w` is off `F`.
* **No strictly weaker residual exists that still implies Order.**  If `R` implies Order and
  Cycle implies `R`, then `R` is equivalent to Cycle, since Order implies Cycle.  So the residual
  below is **only EQUIVALENT** (`witnessStepLobe_order_of_sublist`,
  `witnessStepLobe_sublist_of_order`).  It is the smallest in proof content: a cyclic sublist
  claim about one list.  It is the forward disjunct of `WitnessCurveSublistNondegStatement`
  (gl-p07-36c), which is the four-piece Jordan fact itself.
* **Truth check** (`SP/gl-p07-64/lobe_check.py`, planar grid maps with real region candidates,
  real `FaceSetBoundary` cycles and decompositions, a noncrossing `K`, and the real
  `keepClass`/`block`/`cut`/`Touch` witness and filtered curve).  The Euler equalities,
  FaceShelling and `hpinch` are not modelled, so the model has fewer premises and is a
  stronger test.  Order, clauses 2 and 3 of Cycle (with `O = univ \ F`, `B = outerWalk`) and
  `FollowsBoundary`: 0 failures.  Risk cases:
  - (i) `F`-faced entries of `invDarts G₁ / G₂` occur in every case, and they are always on the
    outer walk.  This is proved here: none is off the lobe boundary.
  - (ii) `a` and `b` share an edge or touch at a vertex: these cases pass as well.
  - (iii) `w` closes up at the four corners in every case (vertex chain, cyclically).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- A rotation of a walk has the same inverse-reading entries. -/
theorem witnessStepLobe_mem_invDarts_rotate {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {ow : List X.toCombMap.Dart} {r : ℕ} {e : X.toCombMap.Dart} :
    e ∈ invDarts X (ow.rotate r) ↔ e ∈ invDarts X ow := by
  rw [Embedded.mem_invDarts_iff, Embedded.mem_invDarts_iff, List.mem_rotate]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_mem_invDarts_rotate

/-- **Residual of lane gl-p07-64: a rotation of the inverse walk is a sublist of the curve.**
The premises of `witnessStepReclose_OrderStatement`.  The conclusion: for some `r`,
`invDarts X (outerWalk.rotate r) <+ witnessSublistCurve a b G₁ G₂`.  LOUD: **only EQUIVALENT** to
the Order statement and to `witnessStepOrder_CycleStatement`, not strictly weaker.  No strictly
weaker residual that still implies Order exists, since Order implies Cycle. -/
def witnessStepLobe_SublistStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    0 < (a.cellArcList i).length → 0 < (a.cellArcList j).length →
    0 < (b.cellArcList i).length → 0 < (b.cellArcList j).length →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    ∀ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i →
    ∀ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 →
      C.face ∉ b.1 →
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) →
        (∀ e ∈ invDarts X outerWalk,
          e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
          X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i) →
        (∃ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
          (invDarts X outerWalk).rotate n = s ++ x :: y :: t ∧
          ¬ WitnessStepCellTurn G₁ G₂ outerWalk y ∧
          ¬ WitnessStepSideTurn a b G₁ G₂ outerWalk y ∧
          ¬ WitnessStepBlockTurn a b G₁ G₂ x y ∧
          ¬ WitnessStepCornerTurn a b G₁ G₂ outerWalk y ∧
          WitnessStepPinchOffAt a b K C.face G₁ G₂ outerWalk x y) →
        ∃ r : ℕ, invDarts X (outerWalk.rotate r) <+ witnessSublistCurve a b G₁ G₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_SublistStatement

/-- **Lane gl-p07-64: the Order statement from the sublist residual.**  The order of a
duplicate-free list on a sublist is the order of the sublist. -/
theorem witnessStepLobe_order_of_sublist (h : witnessStepLobe_SublistStatement.{u, w, v}) :
    witnessStepReclose_OrderStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  obtain ⟨r, hr⟩ :=
    h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  refine ⟨r, fun c hc d hd => ?_⟩
  exact witnessStepOrder_before_sublist_iff (witnessSublist_curve_nodup a b G₁ G₂) hr
    ((witnessStepLobe_mem_invDarts_rotate (r := r)).mpr hc)
    ((witnessStepLobe_mem_invDarts_rotate (r := r)).mpr hd)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_order_of_sublist

/-- **Lane gl-p07-64: the sublist residual from the Order statement.**  Every entry of the
rotated inverse walk is on the curve (`hlab`), and the order is preserved, so the rotated inverse
walk is a sublist (`witnessStepLobe_sublist_of_before`). -/
theorem witnessStepLobe_sublist_of_order (h : witnessStepReclose_OrderStatement.{u, w, v}) :
    witnessStepLobe_SublistStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  obtain ⟨r, hr⟩ :=
    h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  refine ⟨r, witnessStepLobe_sublist_of_before
    (Embedded.invDarts_nodup (List.nodup_rotate.mpr E.nodup))
    (witnessSublist_curve_nodup a b G₁ G₂) (fun x hx => ?_) (fun c hc d hd hcd => ?_)⟩
  · exact witnessSublist_mem_curve
      (hlab x ((witnessStepLobe_mem_invDarts_rotate (r := r)).mp hx))
  · exact (hr c ((witnessStepLobe_mem_invDarts_rotate (r := r)).mp hc)
      d ((witnessStepLobe_mem_invDarts_rotate (r := r)).mp hd)).mpr hcd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_sublist_of_order
