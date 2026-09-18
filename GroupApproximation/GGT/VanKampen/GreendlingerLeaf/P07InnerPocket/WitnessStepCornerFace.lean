import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerStatement
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkColour
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhi
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-50: the curve filters are no-ops at corners

Lane gl-p07-50.  Certifies no printed sentence on its own.

The words `sideAWord`, `cellG2Word` and `sideBWord` (`FourBlockCurve.lean`) filter the inverse
sides and the inverse arc `Ḡ₂` by priority classes.  Here we show the filters keep every dart that
the corner turns of `WitnessStepCornerStatement.lean` produce.

* `witnessStepCorner_cell_face_not_mem`: a region with a nonempty arc on `Π_k` does not contain
  the face of `Π_k`.  The arc dart `d` has `α d` on the boundary cycle of the region, so
  `faceOf (α (α d)) = faceOf d` is off the region.  The proof follows
  `CellPocketWalkColour.cell_face_not_mem`, with the nonempty arc as a hypothesis.
* `witnessStepCorner_not_mem_cellDarts_of_mem_sideFrom`: a side dart is based in its region, so it
  is not a dart of a cell whose face is off the region.
* `witnessStepCorner_not_mem_sideFrom_of_disjoint`: disjoint regions have no common side dart.
* `witnessStepCorner_mem_sideBWord`, `witnessStepCorner_mem_sideAWord`: `α y` on the side puts `y`
  in its block.
* `witnessStepCorner_not_mem_invG₁_of_mem_G₂`: for `i ≠ j`, `α y ∈ G₂` forces `y ∉ Ḡ₁`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section CornerFace

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

/-- A dart of an inverse list is the reverse of a dart of the list. -/
theorem witnessStepCorner_alpha_mem_of_mem_invDarts {L : List X.toCombMap.Dart}
    {y : X.toCombMap.Dart} (hy : y ∈ invDarts X L) : X.toCombMap.alpha y ∈ L := by
  unfold invDarts at hy
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
  rw [X.toCombMap.alpha_involutive e]
  exact List.mem_reverse.mp he

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_alpha_mem_of_mem_invDarts

/-- The reverse of a dart of a list is a dart of the inverse list. -/
theorem witnessStepCorner_mem_invDarts_of_alpha_mem {L : List X.toCombMap.Dart}
    {y : X.toCombMap.Dart} (hy : X.toCombMap.alpha y ∈ L) : y ∈ invDarts X L := by
  unfold invDarts
  exact List.mem_map.mpr
    ⟨X.toCombMap.alpha y, List.mem_reverse.mpr hy, X.toCombMap.alpha_involutive y⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_mem_invDarts_of_alpha_mem

/-- **A region with a nonempty arc on a cell at one of its ends does not contain the face of that
cell.** -/
theorem witnessStepCorner_cell_face_not_mem (a : RegionCandidate D eps X) {k : Fin X.rCellCount}
    (hk : a.2.source = k ∨ a.2.target = some k) (hpos : 0 < (a.cellArcList k).length) :
    (cell X k).face ∉ a.1 := by
  obtain ⟨A, hA⟩ := RegionCandidate.exists_cellArc a hk
  obtain ⟨d, r, hdr⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hpos)
  have hd : d ∈ a.cellArcList k := by
    rw [hdr]
    simp
  have hdface : X.toCombMap.faceOf d = (cell X k).face :=
    faceOf_of_mem_cellDarts (A.mem_cycle_of_mem_darts (by rw [hA]; exact hd))
  have hcycle : X.toCombMap.alpha d ∈ a.2.boundary.cycle := by
    rw [a.2.boundary_decomposition]
    simp only [List.mem_append]
    by_cases hs : a.2.source = k
    · rw [RegionCandidate.cellArcList, if_pos hs] at hd
      exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩)))
    · rw [RegionCandidate.cellArcList, if_neg hs] at hd
      refine Or.inl (Or.inr ?_)
      rw [targetBoundaryDarts_eq_invDarts (hk.resolve_left hs)]
      exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
  have h := ((a.2.boundary.cycle_mem_iff _).mp hcycle).2
  rw [X.toCombMap.alpha_involutive d, hdface] at h
  exact h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_cell_face_not_mem

/-- A side dart of a region is based in the region. -/
theorem witnessStepCorner_faceOf_mem_of_mem_sideFrom (c : RegionCandidate D eps X)
    (k : Fin X.rCellCount) {d : X.toCombMap.Dart} (hd : d ∈ c.sideFrom k) :
    X.toCombMap.faceOf d ∈ c.1 :=
  ((c.2.boundary.cycle_mem_iff d).mp
    (CellPocketWalkColour.mem_boundary_of_mem_sideFrom c k hd)).1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_faceOf_mem_of_mem_sideFrom

/-- A side dart of a region is not a dart of a cell whose face is off the region. -/
theorem witnessStepCorner_not_mem_cellDarts_of_mem_sideFrom (c : RegionCandidate D eps X)
    (k : Fin X.rCellCount) {m : Fin X.rCellCount} (hm : (cell X m).face ∉ c.1)
    {d : X.toCombMap.Dart} (hd : d ∈ c.sideFrom k) : d ∉ cellDarts X m := by
  intro hdm
  have hf := witnessStepCorner_faceOf_mem_of_mem_sideFrom c k hd
  rw [faceOf_of_mem_cellDarts hdm] at hf
  exact hm hf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_not_mem_cellDarts_of_mem_sideFrom

/-- If `α y` is a side dart of a region, then `y` is not in the inverse of an arc of a cell whose
face is off the region. -/
theorem witnessStepCorner_not_mem_invArc_of_mem_sideFrom (c : RegionCandidate D eps X)
    (k : Fin X.rCellCount) {m : Fin X.rCellCount} (hm : (cell X m).face ∉ c.1)
    (A : CyclicArc (cellDarts X m)) {y : X.toCombMap.Dart}
    (hy : X.toCombMap.alpha y ∈ c.sideFrom k) : y ∉ invDarts X A.darts := fun h =>
  witnessStepCorner_not_mem_cellDarts_of_mem_sideFrom c k hm hy
    (A.mem_cycle_of_mem_darts (witnessStepCorner_alpha_mem_of_mem_invDarts h))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_not_mem_invArc_of_mem_sideFrom

/-- Disjoint regions have no common side dart. -/
theorem witnessStepCorner_not_mem_sideFrom_of_disjoint {a b : RegionCandidate D eps X}
    (hab : Disjoint a.1 b.1) (k k' : Fin X.rCellCount) {d : X.toCombMap.Dart}
    (ha : d ∈ a.sideFrom k) : d ∉ b.sideFrom k' := fun hb =>
  Finset.disjoint_left.mp hab (witnessStepCorner_faceOf_mem_of_mem_sideFrom a k ha)
    (witnessStepCorner_faceOf_mem_of_mem_sideFrom b k' hb)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_not_mem_sideFrom_of_disjoint

end CornerFace

section CornerFilter

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **`α y` on `b.sideFrom i` puts `y` in the block `B̄`**, when the faces of `Π_i` and `Π_j`
are off `b`. -/
theorem witnessStepCorner_mem_sideBWord {b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {y : X.toCombMap.Dart}
    (hy : X.toCombMap.alpha y ∈ b.sideFrom i) (hbi : (cell X i).face ∉ b.1)
    (hbj : (cell X j).face ∉ b.1) : y ∈ FourBlock.sideBWord b G₁ G₂ := by
  unfold FourBlock.sideBWord
  exact List.mem_filter.mpr ⟨witnessStepCorner_mem_invDarts_of_alpha_mem hy,
    @decide_eq_true _ (_) ⟨witnessStepCorner_not_mem_invArc_of_mem_sideFrom b i hbi G₁ hy,
      witnessStepCorner_not_mem_invArc_of_mem_sideFrom b i hbj G₂ hy, hy⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_mem_sideBWord

/-- **`α y` on `a.sideFrom j` puts `y` in the block `Ā`**, when the faces of `Π_i` and `Π_j`
are off `a` and the regions are disjoint. -/
theorem witnessStepCorner_mem_sideAWord {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {y : X.toCombMap.Dart}
    (hab : Disjoint a.1 b.1) (hy : X.toCombMap.alpha y ∈ a.sideFrom j)
    (hai : (cell X i).face ∉ a.1) (haj : (cell X j).face ∉ a.1) :
    y ∈ FourBlock.sideAWord a b G₁ G₂ := by
  unfold FourBlock.sideAWord
  exact List.mem_filter.mpr ⟨witnessStepCorner_mem_invDarts_of_alpha_mem hy,
    @decide_eq_true _ (_) ⟨witnessStepCorner_not_mem_invArc_of_mem_sideFrom a j hai G₁ hy,
      witnessStepCorner_not_mem_invArc_of_mem_sideFrom a j haj G₂ hy,
      witnessStepCorner_not_mem_sideFrom_of_disjoint hab j i hy⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_mem_sideAWord

/-- A side dart `g` of `a.sideFrom j` has `α g ∉ Ḡ₂` when the face of `Π_j` is off `a`. -/
theorem witnessStepCorner_alpha_not_mem_invG₂ {a : RegionCandidate D eps X}
    {G₂ : CyclicArc (cellDarts X j)} {g : X.toCombMap.Dart} (hg : g ∈ a.sideFrom j)
    (haj : (cell X j).face ∉ a.1) : X.toCombMap.alpha g ∉ invDarts X G₂.darts := by
  intro h
  have hg2 := witnessStepCorner_alpha_mem_of_mem_invDarts h
  rw [X.toCombMap.alpha_involutive g] at hg2
  exact witnessStepCorner_not_mem_cellDarts_of_mem_sideFrom a j haj hg
    (G₂.mem_cycle_of_mem_darts hg2)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_alpha_not_mem_invG₂

/-- **For distinct cells, `α y ∈ G₂` forces `y ∉ Ḡ₁`.**  The faces of `Π_i` and `Π_j` differ. -/
theorem witnessStepCorner_not_mem_invG₁_of_mem_G₂ (hij : i ≠ j)
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {y : X.toCombMap.Dart}
    (hy : X.toCombMap.alpha y ∈ G₂.darts) : y ∉ invDarts X G₁.darts := by
  intro h
  have h1 := witnessStepCorner_alpha_mem_of_mem_invDarts h
  have hf1 : X.toCombMap.faceOf (X.toCombMap.alpha y) = (cell X i).face :=
    faceOf_of_mem_cellDarts (G₁.mem_cycle_of_mem_darts h1)
  have hf2 : X.toCombMap.faceOf (X.toCombMap.alpha y) = (cell X j).face :=
    faceOf_of_mem_cellDarts (G₂.mem_cycle_of_mem_darts hy)
  exact hij (cell_face_injective X (hf1.symm.trans hf2))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_not_mem_invG₁_of_mem_G₂

end CornerFilter

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
