import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenCaseStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-46: Base from the lake-filled witness

Write `F₀ = witnessFaces a b K c` and `o = X.outerFace`.  `AbsorbFaceSetStatement` assumes (`hno`)
that `F₀` has no bridge-free enclosed successor walk.  So Base cannot use the witness walk.  The
candidate used here is the **lake-filled witness**
`F₁ = absorbBaseFaces a b K c = ExteriorComponent.absorbed X.toCombMap F₀ o`.

## Proved here

1. `absorbBase_outer_not_mem`: `o ∉ F₀`, because `F₀ ⊆ sideFaces K.walk` and `o ∉ sideFaces K.walk`.
2. `absorbBase_witness_subset`, `absorbBase_mem_faces`: `F₀ ⊆ F₁` (`subset_absorbed`), so `c ∈ F₁`.
3. `absorbBase_dart_clause`: the third disjunct of the dart clause, for every bridge-free enclosed
   successor walk `ow` of `F₁`.  Take `d ∈ ow`.  By `mem_iff`, `faceOf d ∉ F₁`, and by the
   bridge-free hypothesis `faceOf (α d) ∈ F₁`.  So `α d` is a boundary dart of `F₁`.  By
   `isBoundaryDart_absorbed_iff`, `α d` is then a boundary dart of `F₀`, so `faceOf (α d) ∈ F₀` and
   `faceOf d ∉ F₀`.  Finish with `pocketKeep_alpha_of_boundary`,
   `not_mem_left/right_of_mem_witnessFaces` and `witnessFaces_subset_sideFaces`.
4. `absorbBase_basic_of_case`: in the case `AbsorbBaseCase`, `(F₁, ow)` is a basic pair.
   `AbsorbBaseCase` says: `F₁ ⊆ sideFaces K.walk`, and some bridge-free enclosed successor walk `ow`
   of `F₁` satisfies the four noninterleave clauses.

## Not proved (left in the case condition)

* `F₁ ⊆ sideFaces K.walk`.  This fails when a lake of `F₀` is not inside the pocket, for example
  when `Π_j` is inside a `G₁`-loop.
* The existence of an enclosed walk for `F₁`.  The planar orbit route needs connectivity of the
  keep map.
* The four noninterleave clauses.  They fail in the model M9-with-hole of
  `NoPlanarDegenStepStatement.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The lake-filled witness**: every face outside the piece of the outer face, taking the piece
off the boundary of `witnessFaces a b K c`. -/
noncomputable abbrev absorbBaseFaces (a b : RegionCandidate D eps X)
    (K : CellPocketWalk D eps X i j) (c : X.toCombMap.Face) : Finset X.toCombMap.Face :=
  ExteriorComponent.absorbed X.toCombMap (witnessFaces a b K c) X.outerFace

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbBaseFaces

/-- The outer face is off the witness. -/
theorem absorbBase_outer_not_mem {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) :
    X.outerFace ∉ witnessFaces a b K c :=
  fun h => hout (witnessFaces_subset_sideFaces h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbBase_outer_not_mem

/-- Filling the lakes keeps the witness. -/
theorem absorbBase_witness_subset {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) :
    witnessFaces a b K c ⊆ absorbBaseFaces a b K c :=
  ExteriorComponent.subset_absorbed (absorbBase_outer_not_mem (a := a) (b := b) (c := c) hout)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbBase_witness_subset

/-- The lake-filled witness holds `c`. -/
theorem absorbBase_mem_faces {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hc : c ∈ sideFaces X.toCombMap K.walk) : c ∈ absorbBaseFaces a b K c :=
  absorbBase_witness_subset (a := a) (b := b) (c := c) hout (mem_witnessFaces_self hc)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbBase_mem_faces

/-- **The dart clause for the lake-filled witness**, third disjunct, for a bridge-free enclosed
successor walk. -/
theorem absorbBase_dart_clause {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) (hca : c ∉ a.1) (hcb : c ∉ b.1)
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X (absorbBaseFaces a b K c) ow)
    (hnb : ∀ d ∈ ow,
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ absorbBaseFaces a b K c) :
    ∀ d ∈ ow,
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk ∧
        X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
        X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1 ∧
        (walkKeep X.toCombMap K.walk (X.toCombMap.alpha d) ∨
          walkKeep X.toCombMap a.2.boundary.cycle (X.toCombMap.alpha d) ∨
          walkKeep X.toCombMap b.2.boundary.cycle (X.toCombMap.alpha d)) := by
  intro d hd
  have ho : X.outerFace ∉ witnessFaces a b K c := absorbBase_outer_not_mem hout
  have hf : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ absorbBaseFaces a b K c := hnb d hd
  have hg : X.toCombMap.faceOf d ∉ absorbBaseFaces a b K c := ((E.mem_iff d).mp hd).1
  have hg' : X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d)) ∉
      absorbBaseFaces a b K c := by
    rw [X.toCombMap.alpha_involutive d]
    exact hg
  obtain ⟨hb, -⟩ :=
    (ExteriorComponent.isBoundaryDart_absorbed_iff ho (X.toCombMap.alpha d)).mp
      (show X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ absorbBaseFaces a b K c ∧
          X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d)) ∉
            absorbBaseFaces a b K c from ⟨hf, hg'⟩)
  have hb' : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K c ∧
      X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d)) ∉
        witnessFaces a b K c := hb
  have hgw : X.toCombMap.faceOf d ∉ witnessFaces a b K c := by
    have h2 := hb'.2
    rw [X.toCombMap.alpha_involutive d] at h2
    exact h2
  exact ⟨witnessFaces_subset_sideFaces hb'.1, not_mem_left_of_mem_witnessFaces hca hb'.1,
    not_mem_right_of_mem_witnessFaces hcb hb'.1, pocketKeep_alpha_of_boundary hw hgw hb'.1⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbBase_dart_clause

/-- **The lake-filled case**: the lake-filled witness stays inside the pocket and has a bridge-free
enclosed successor walk satisfying the four noninterleave clauses. -/
abbrev AbsorbBaseCase (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) (c : X.toCombMap.Face) : Prop :=
  absorbBaseFaces a b K c ⊆ sideFaces X.toCombMap K.walk ∧
    ∃ ow : List X.toCombMap.Dart, EnclosedFaceSetSucc X (absorbBaseFaces a b K c) ow ∧
      (∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ absorbBaseFaces a b K c) ∧
      PinchCase.WalkDegenCaseNoninterleave b G₁ G₂ ow

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.AbsorbBaseCase

/-- **In the lake-filled case the lake-filled witness is a basic pair.** -/
theorem absorbBase_basic_of_case {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {c : X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hc : c ∈ sideFaces X.toCombMap K.walk) (hca : c ∉ a.1) (hcb : c ∉ b.1)
    (h : AbsorbBaseCase a b K G₁ G₂ c) :
    ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
      AbsorbFaceSetBasic a b K G₁ G₂ c faces outerWalk := by
  obtain ⟨hsub, ow, E, hnb, hN⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := hN
  exact ⟨absorbBaseFaces a b K c, ow, E, absorbBase_mem_faces hout hc, hsub,
    fun d hd => Or.inr (Or.inr (absorbBase_dart_clause hw hout hca hcb E hnb d hd)),
    h1, h2, h3, h4⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbBase_basic_of_case

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
