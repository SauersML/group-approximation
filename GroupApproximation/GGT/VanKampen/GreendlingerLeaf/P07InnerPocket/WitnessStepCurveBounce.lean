import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCurveRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-66: corner darts bounce, and the unfiltered curve

Lane gl-p07-66.  Certifies no printed sentence on its own.  NOT COMPILED: authored without
running Lean.

Let the region `c` join the distinct cells `Π_i`, `Π_j`, and let `z` be a dart of the arc of `c`
on `Π_k` (`k ∈ {i, j}`).
* `z` is based in the face of `Π_k`, which is off `c`; so `z` is on no side of `c`, nor of a
  region `c'` avoiding that face (side darts are based in their region).
* `α z` is based in `c` (`faceOf_alpha_mem_of_mem_cellArcList`).  So `α z` is on no side of a
  region disjoint from `c`, and on no arc of `Π_i` or `Π_j` (their faces are off `c`).
* `α z` lies in the block `invDarts (c.cellArcList k)` of the duplicate-free rotation
  `Ā_i · S_i · Ā_j · S_j` of the boundary of `c`, hence on neither side `S_i`, `S_j`.
* `z` is on no arc of the other cell (the faces of `Π_i`, `Π_j` differ).
These are the bounce facts of the four corners (`witnessStepCurve_bounce`).

The curve.  When the faces of `Π_i`, `Π_j` are off `a` and `b` and `a`, `b` are disjoint,
the three priority filters of `witnessSublistCurve` remove nothing (each kept entry is checked
by the `witnessStepCorner_*` lemmas), so the curve is
`invDarts (b.sideFrom i ++ G₂ ++ a.sideFrom j ++ G₁)` (`witnessStepCurve_curve_eq`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- A nonempty list ends in some entry. -/
theorem witnessStepCurve_exists_concat {β : Type*} {l : List β} (h : 0 < l.length) :
    ∃ p z, l = p ++ [z] :=
  ⟨l.dropLast, l.getLast (List.ne_nil_of_length_pos h),
    (List.dropLast_append_getLast (List.ne_nil_of_length_pos h)).symm⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_exists_concat

section Bounce

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- A dart of the arc of a region on a cell is based in the face of that cell. -/
theorem witnessStepCurve_arc_face (c : RegionCandidate D eps X) {k : Fin X.rCellCount}
    (hk : c.2.source = k ∨ c.2.target = some k) {z : X.toCombMap.Dart}
    (hz : z ∈ c.cellArcList k) : X.toCombMap.faceOf z = (cell X k).face := by
  obtain ⟨A, hA⟩ := RegionCandidate.exists_cellArc c hk
  exact faceOf_of_mem_cellDarts (A.mem_cycle_of_mem_darts (by rw [hA]; exact hz))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_arc_face

/-- A dart of the arc of a region on one cell is on no arc of another cell. -/
theorem witnessStepCurve_not_mem_other_arc (c : RegionCandidate D eps X) {k m : Fin X.rCellCount}
    (hkm : k ≠ m) (hck : c.2.source = k ∨ c.2.target = some k) (A : CyclicArc (cellDarts X m))
    {z : X.toCombMap.Dart} (hz : z ∈ c.cellArcList k) : z ∉ A.darts := fun h =>
  hkm (cell_face_injective X ((witnessStepCurve_arc_face c hck hz).symm.trans
    (faceOf_of_mem_cellDarts (A.mem_cycle_of_mem_darts h))))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_not_mem_other_arc

/-- **The reverse of an arc dart is on neither side of its region.** -/
theorem witnessStepCurve_alpha_not_mem_sides (hij : i ≠ j) {c : RegionCandidate D eps X}
    (hc : c.JoinsCells i j) {k : Fin X.rCellCount} (hk : k = i ∨ k = j)
    {z : X.toCombMap.Dart} (hz : z ∈ c.cellArcList k) :
    X.toCombMap.alpha z ∉ c.sideFrom i ∧ X.toCombMap.alpha z ∉ c.sideFrom j := by
  obtain ⟨n, hn⟩ := RegionCandidate.boundary_cycle_rotate_of_joinsCells hij hc
  have hnd : (invDarts X (c.cellArcList i) ++ c.sideFrom i ++ invDarts X (c.cellArcList j) ++
      c.sideFrom j).Nodup := by
    rw [← hn]
    exact List.nodup_rotate.mpr c.2.boundary.cycle_nodup
  have hα : X.toCombMap.alpha z ∈ invDarts X (c.cellArcList k) :=
    witnessStepCorner_mem_invDarts_of_alpha_mem (by rw [X.toCombMap.alpha_involutive z]; exact hz)
  rcases hk with hk | hk
  · rw [hk] at hα
    exact witnessStepCurve_nodup_four hnd (Or.inl hα)
  · rw [hk] at hα
    exact witnessStepCurve_nodup_four hnd (Or.inr hα)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_alpha_not_mem_sides

/-- **A corner dart bounces.**  It and its reverse are off a side of `c`, a side of a region
`c'` disjoint from `c`, and the arcs `G₁`, `G₂`. -/
theorem witnessStepCurve_bounce (hij : i ≠ j) {c c' : RegionCandidate D eps X}
    (hc : c.JoinsCells i j) (hcc : Disjoint c.1 c'.1) {k k₁ : Fin X.rCellCount}
    (k₂ : Fin X.rCellCount) (hk : k = i ∨ k = j) (hck : c.2.source = k ∨ c.2.target = some k)
    (hk₁ : k₁ = i ∨ k₁ = j) (hci : (cell X i).face ∉ c.1) (hcj : (cell X j).face ∉ c.1)
    (hc'k : (cell X k).face ∉ c'.1) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) {z : X.toCombMap.Dart} (hz : z ∈ c.cellArcList k)
    (hz₁ : z ∉ G₁.darts) (hz₂ : z ∉ G₂.darts) :
    (z ∉ c.sideFrom k₁ ∧ z ∉ c'.sideFrom k₂ ∧ z ∉ G₁.darts ∧ z ∉ G₂.darts) ∧
      (X.toCombMap.alpha z ∉ c.sideFrom k₁ ∧ X.toCombMap.alpha z ∉ c'.sideFrom k₂ ∧
        X.toCombMap.alpha z ∉ G₁.darts ∧ X.toCombMap.alpha z ∉ G₂.darts) := by
  have hf := witnessStepCurve_arc_face c hck hz
  have hαf := RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hc hz
  have hck' : (cell X k).face ∉ c.1 := by
    rcases hk with hk | hk
    · rw [hk]
      exact hci
    · rw [hk]
      exact hcj
  have hs := witnessStepCurve_alpha_not_mem_sides hij hc hk hz
  refine ⟨⟨fun h => hck' ?_, fun h => hc'k ?_, hz₁, hz₂⟩,
    ⟨?_, fun h => ?_, fun h => hci ?_, fun h => hcj ?_⟩⟩
  · rw [← hf]
    exact witnessStepCorner_faceOf_mem_of_mem_sideFrom c k₁ h
  · rw [← hf]
    exact witnessStepCorner_faceOf_mem_of_mem_sideFrom c' k₂ h
  · rcases hk₁ with hk₁ | hk₁
    · rw [hk₁]
      exact hs.1
    · rw [hk₁]
      exact hs.2
  · exact Finset.disjoint_left.mp hcc hαf (witnessStepCorner_faceOf_mem_of_mem_sideFrom c' k₂ h)
  · rw [← faceOf_of_mem_cellDarts (G₁.mem_cycle_of_mem_darts h)]
    exact hαf
  · rw [← faceOf_of_mem_cellDarts (G₂.mem_cycle_of_mem_darts h)]
    exact hαf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_bounce

end Bounce

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
