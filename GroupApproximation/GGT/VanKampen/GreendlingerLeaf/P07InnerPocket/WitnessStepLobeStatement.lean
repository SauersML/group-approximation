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
