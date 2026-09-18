import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchFan
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerFace
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-52: region and cell steps at the junctions of the curve

Lane gl-p07-52.  Certifies no printed sentence on its own.  NOT COMPILED.

A region `c` joining `Π_i` to `Π_j` has a rotation of its boundary cycle equal to
`c̄_i · c.sideFrom i · c̄_j · c.sideFrom j`, where `c̄_k = invDarts X (c.cellArcList k)`
(`RegionCandidate.boundary_cycle_rotate_of_joinsCells`).  That rotation is a `BoundaryStep` chain,
and it closes up.  Read off at the joints, this gives four fans (`WitnessStepPinchFan`):
* `witnessStepPinch_fan_sideI_end`: from the end `d` of `c.sideFrom i` to `α z`, `z` the last
  dart of `c.cellArcList j`;
* `witnessStepPinch_fan_sideJ_start`: from `z'`, the first dart of `c.cellArcList j`, to the first
  dart of `c.sideFrom j`;
* `witnessStepPinch_fan_sideJ_end`: from the end `d` of `c.sideFrom j` to `α z''`, `z''` the last
  dart of `c.cellArcList i` (the closing step of the cycle);
* `witnessStepPinch_fan_cellJ_cellI`: when `c.sideFrom j = []`, from `z'` to `α z''`.
Consecutive darts of a cell arc are face steps (`witnessStepPinch_facePerm_of_arc`).  The darts of
a region's cell arc on a cell with face off `F` have both faces off `F`
(`witnessStepPinch_arc_mid_faces`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section PinchRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- The inverse of `p ++ [z]` starts with `α z`. -/
theorem witnessStepPinch_invDarts_concat (p : List X.toCombMap.Dart) (z : X.toCombMap.Dart) :
    invDarts X (p ++ [z]) = X.toCombMap.alpha z :: invDarts X p := by
  simp [Embedded.invDarts]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_invDarts_concat

/-- The inverse of `z :: p` ends with `α z`. -/
theorem witnessStepPinch_invDarts_cons (z : X.toCombMap.Dart) (p : List X.toCombMap.Dart) :
    invDarts X (z :: p) = invDarts X p ++ [X.toCombMap.alpha z] := by
  simp [Embedded.invDarts]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_invDarts_cons

/-- **Consecutive darts of a rotation of a region boundary form a boundary step.** -/
theorem witnessStepPinch_boundaryStep_mid (c : RegionCandidate D eps X) {n : ℕ}
    {p r : List X.toCombMap.Dart} {d e : X.toCombMap.Dart}
    (h : c.2.boundary.cycle.rotate n = p ++ d :: e :: r) : Embedded.BoundaryStep X c.1 d e :=
  List.isChain_iff_forall_rel_of_append_cons_cons.mp
    (isChain_rotate_of_isChain_closes c.2.boundary.cycle_nonempty c.2.boundary.cycle_chain
      c.2.boundary.cycle_closes n) h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_boundaryStep_mid

/-- **The closing step of a rotation of a region boundary.**  If the rotation is `P ++ Q`, the
last dart `d` of `Q` steps to the first dart `e` of `P`. -/
theorem witnessStepPinch_boundaryStep_close (c : RegionCandidate D eps X) {n : ℕ}
    {P Q p r : List X.toCombMap.Dart} {d e : X.toCombMap.Dart}
    (h : c.2.boundary.cycle.rotate n = P ++ Q) (hQ : Q = p ++ [d]) (hP : P = e :: r) :
    Embedded.BoundaryStep X c.1 d e := by
  have heq : c.2.boundary.cycle.rotate (n + P.length) = p ++ d :: e :: r := by
    rw [← List.rotate_rotate, h, List.rotate_append_length_eq, hQ, hP]
    simp
  exact witnessStepPinch_boundaryStep_mid c heq

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_boundaryStep_close

/-- **Consecutive darts of a cell arc are a face step.** -/
theorem witnessStepPinch_facePerm_of_arc {k : Fin X.rCellCount} (Γ : CyclicArc (cellDarts X k))
    {p q : List X.toCombMap.Dart} {d g : X.toCombMap.Dart} (h : Γ.darts = p ++ d :: g :: q) :
    X.toCombMap.facePerm d = g :=
  List.isChain_iff_forall_rel_of_append_cons_cons.mp
    (PocketRun.arcDarts_isChain (X.faceBoundary (cell X k).face) Γ) h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_facePerm_of_arc

/-- **A dart of a region's cell arc has both faces off `F`**, when `F` is off the region and off
the cell. -/
theorem witnessStepPinch_arc_mid_faces {c : RegionCandidate D eps X}
    {F : Finset X.toCombMap.Face} (hR : ∀ f ∈ F, f ∉ c.1) (hc : c.JoinsCells i j)
    {k : Fin X.rCellCount} (hFk : (cell X k).face ∉ F) (Γ : CyclicArc (cellDarts X k))
    {z : X.toCombMap.Dart} (hzΓ : z ∈ Γ.darts) (hz : z ∈ c.cellArcList k) :
    X.toCombMap.faceOf z ∉ F ∧ X.toCombMap.faceOf (X.toCombMap.alpha z) ∉ F := by
  refine ⟨?_, fun hf => hR _ hf (RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hc hz)⟩
  rw [faceOf_of_mem_cellDarts (Γ.mem_cycle_of_mem_darts hzΓ)]
  exact hFk

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_arc_mid_faces

/-- The reverse of a region's cell-arc dart has both faces off `F` as well. -/
theorem witnessStepPinch_arc_mid_faces_alpha {c : RegionCandidate D eps X}
    {F : Finset X.toCombMap.Face} (hR : ∀ f ∈ F, f ∉ c.1) (hc : c.JoinsCells i j)
    {k : Fin X.rCellCount} (hFk : (cell X k).face ∉ F) (Γ : CyclicArc (cellDarts X k))
    {z : X.toCombMap.Dart} (hzΓ : z ∈ Γ.darts) (hz : z ∈ c.cellArcList k) :
    X.toCombMap.faceOf (X.toCombMap.alpha z) ∉ F ∧
      X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha z)) ∉ F := by
  have hm := witnessStepPinch_arc_mid_faces hR hc hFk Γ hzΓ hz
  rw [X.toCombMap.alpha_involutive z]
  exact ⟨hm.2, hm.1⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_arc_mid_faces_alpha
