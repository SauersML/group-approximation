import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceOffStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-16: reducing the four-piece off statement to the lake reading

This file proves `pocketFourPieceOff_of_lakeRead : PocketFourPieceLakeReadStatement →
PocketFourPieceOffStatement`.  The context is Osin, arXiv:math/0411039v3, §9, Lemma 9.7(b).

## Proof

Fix the premise block of the target, and take the residual's walk `L`.  Write `P = sideFaces L`.
The residual gives:
* `C ∈ P`;
* `P ⊆ sideFaces K`, with `P` off `a`, `b`, `Π_i` and `Π_j`.

The proof then runs in five steps.
1. `o ∉ P`, because `P ⊆ sideFaces K` and `o ∉ sideFaces K`.
2. `exists_lakeFill_of_noncrossing` (lane gl-p07-06) gives an outer walk `W` and a proof
   `E : EnclosedFaceSetSucc (absorbed P o) W`, with `C ∈ absorbed P o`.  The darts of `W` are the
   reverses of `L`-darts facing the exterior piece.
3. The residual, applied to `W`, `E` and that membership, gives the rotation, chunks and arcs.
4. For the off-cell clause, assume both arcs are empty and split on the contact arcs of `a` and
   `b` on `Π_i`.
   * If both are nonempty, `pocketCellOff_nondegenerate` (lane gl-p07-07) puts `Π_i` or `Π_j` in
     `component P o`.  That cell is then not in `absorbed P o` (`mem_absorbed_iff`).
   * Otherwise, the residual's weakened clause applies.
5. The witness face set is `absorbed P o`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent

namespace FourPieceOff

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **With nonempty contact arcs on `Π_i`, some cell is not absorbed by a face set inside the
pocket and off the regions and the two cells.** -/
theorem exists_cell_not_mem_absorbed_of_contact {a b : RegionCandidate D eps X}
    (K : CellPocketWalk D eps X i j) (hij : i ≠ j) (hai : a.JoinsCells i j)
    (hbi : b.JoinsCells i j) (hfirst : K.firstSide = b.sideFrom j)
    (hsecond : K.secondSide = a.sideFrom i) (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) {P : Finset X.toCombMap.Face}
    (hP : ∀ f ∈ P, f ∈ sideFaces X.toCombMap K.walk ∧ f ∉ a.1 ∧ f ∉ b.1 ∧
      f ≠ (cell X i).face ∧ f ≠ (cell X j).face)
    (hapos : 0 < (a.cellArcList i).length) (hbpos : 0 < (b.cellArcList i).length) :
    ∃ k₀ : Fin X.rCellCount, (cell X k₀).face ∉ absorbed X.toCombMap P X.outerFace := by
  rcases pocketCellOff_nondegenerate K hij hai hbi hfirst hsecond hw hout hP hapos hbpos with
    hc | hc
  · exact ⟨i, fun hab => mem_absorbed_iff.mp hab hc⟩
  · exact ⟨j, fun hab => mem_absorbed_iff.mp hab hc⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceOff.exists_cell_not_mem_absorbed_of_contact

end FourPieceOff

/-- **The labelled four-piece reading with an off cell, from the lake-walk reading of a chosen
pocket walk.**  Lane gl-p07-16's reduction.  It proves the enclosed face set (lane gl-p07-06), the
outer face exclusion, and the off cell for nonempty contact arcs (lane gl-p07-07). -/
theorem pocketFourPieceOff_of_lakeRead (h : PocketFourPieceLakeReadStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨L, hL, hCL, hP, hread⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  have hLout : X.outerFace ∉ sideFaces X.toCombMap L := fun ho => hoff (hP _ ho).1
  obtain ⟨outerWalk, E, hCF, hmem⟩ := exists_lakeFill_of_noncrossing X hL hLout hCL
  obtain ⟨n, R₁, R₂, A₁, A₂, hdec, hcase, hk₀⟩ := hread outerWalk E hmem
  refine ⟨absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace, outerWalk, n, R₁, R₂, A₁,
    A₂, E, hCF, hdec, hcase, fun hA₁ hA₂ => ?_⟩
  by_cases hpos : 0 < (a.cellArcList i).length ∧ 0 < (b.cellArcList i).length
  · exact FourPieceOff.exists_cell_not_mem_absorbed_of_contact K hij hai hbi hfirst hsecond hw
      hoff hP hpos.1 hpos.2
  · exact hk₀ hpos hA₁ hA₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketFourPieceOff_of_lakeRead

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
