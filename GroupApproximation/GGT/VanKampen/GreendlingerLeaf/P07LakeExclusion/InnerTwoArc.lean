import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.Route3
import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedSubdiagramLoopCutSuccProof
import GroupApproximation.Meta.AxiomGuard

/-!
# The inner two-arc pocket, for relator words of length more than one

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The target is
`CellPocketWalkProperArcsBelowSectionStatement`.  `Route3.lean` reduces it to
`CellPocketInnerTwoArcStatement`.

## Why this file weakens the Route 3 residual

`Piece06.LakeFillTwoArcExit` asks for an O-equivalent copy in which both cycles of the pocket region
follow their boundary.  When the boundary of the filled region `F` of the kept cell is pinched, the
walk passes twice through a vertex and does not follow.  So the copy has to be unpinched.  The corpus
has doubling and unpinching (`enclosedBridgeDoublingSideArcSucc`, `enclosedLoopPocketUnpinchSucc`)
only for one-arc decompositions and only under `∀ word ∈ W, 1 < word.length`.  A monogon relator
face cannot be doubled, and the short-relator case is open elsewhere too (`Piece03/Proof.lean`).
`CellPocketInnerTwoArcStatement` has no such hypothesis.  The residual below adds it.  The target
still follows, because `OsinCCondition` at `2 ≤ ρ` gives it (`one_lt_length_of_two_le_rho`).

## Why the weakened residual is true

Let `Π` be the kept relator cell in `sideFaces K` and off `a ∪ b`.
* **The region.**  Take the whole inner pocket, not the edge class of `Π`: every face of `sideFaces K`
  off `a ∪ b`, with its lakes filled.  This matters because an edge class can read a gap `G_1` in
  non-contiguous pieces, when `∂Π_i` revisits a vertex around a subdiagram edge-adjacent only to
  `Π_i`.  The whole pocket reads each gap as one contiguous piece.
* **Its boundary.**  The pocket meets the walk only along `Ḡ_1`, `Ḡ_2`.  It meets `a` and `b` only
  across their far sides `a.sideFrom j` and `b.sideFrom i`.  So its boundary reads
  `s_1 Ā_1 s_2 Ā_2`, with `s_1` the far side of `b`, `A_1 = G_1`, `s_2` the far side of `a` and
  `A_2 = G_2`.  Each side has length at most `ε`, hence norm at most `ε`.  The cells `Π_i`, `Π_j`
  lie in `sideOutside K`, so they are off the pocket.
* **The copy.**  The pinch vertices of this walk are split by a two-arc version of the one-arc
  doubling and unpinching.  That step needs relator words longer than one letter, which is exactly
  the added hypothesis.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The inner two-arc pocket, for relator words longer than one letter.**  This is
`CellPocketInnerTwoArcStatement` with the extra hypothesis `∀ word ∈ W, 1 < word.length`.
* **Why it is true.**  The region is the inner pocket `sideFaces K \ (a ∪ b)` with its lakes filled.
  Its boundary is the far side of `b`, then `Ḡ_1`, then the far side of `a`, then `Ḡ_2`.  Each side
  has length `≤ ε`, and `Π_i`, `Π_j` lie outside the pocket.  A two-arc doubling and unpinching gives
  the O-equivalent copy whose cycles follow their boundary.  The one-arc version of that step is
  closed under the same length hypothesis.  See the module docstring.
* **Why it is strictly weaker.**  It adds a hypothesis to the Route 3 residual
  (`innerTwoArcLong_of_innerTwoArc`). -/
def CellPocketInnerTwoArcLongStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        Piece06.LakeFillTwoArcExit D eps X

/-- The Route 3 residual implies the long-word residual: the added hypothesis is discarded. -/
theorem innerTwoArcLong_of_innerTwoArc (h : CellPocketInnerTwoArcStatement.{u, w, v}) :
    CellPocketInnerTwoArcLongStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel _ hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  exact h D eps X a b K hij hai hbi hab hlabel hfirst hsecond h₁ h₂ hw hoff hinner houter C hC
    hCf hCa hCb

/-- **The lake exclusion from the long-word inner two-arc pocket.**  The proof is the Route 3
script.  The added length hypothesis comes from `OsinCCondition` at `2 ≤ ρ`. -/
theorem proof_of_innerTwoArcLong (h : CellPocketInnerTwoArcLongStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max 2 rho1, by omega, fun rho hrho W hcondition => ?_⟩
  have hlarge := hrho1 rho (le_of_max_le_right hrho)
  have hrho2 : 2 ≤ rho := le_of_max_le_left hrho
  intro Delta _ hlea hbelow S i j a b ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
  exfalso
  have hlea' : S.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S.equiv hlea
  obtain ⟨hinner, houter⟩ :=
    cellPocketWalkEuler hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
  obtain ⟨kept, hkept⟩ := S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K
    hfirst hsecond h₁ hlea' (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter) rfl
  rw [PocketRegion.ofNoncrossingClosedWalkEuler_faces] at hkept
  have hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1 :=
    fun C hC => DiscDiagram.leastArea_listVal_word_ne_one hlea' C hC
  have hcell : ∀ z : RegionCandidate D eps S.diagram, (cell S.diagram kept).face ∉ z.1 := by
    intro z hkz
    have hz := (z.2.boundary.all_gCells _ hkz).2
    rw [DiscDiagram.faceWord, ← S.diagram.relatorCell_word _ (cell_mem S.diagram kept)] at hz
    exact hvalue _ (cell_mem S.diagram kept) hz
  have hbelow' : OsinLemma97Below.{u, w, v} D lambda c mu eps W S.diagram.rCellCount := by
    rw [S.equiv.rCellCount_eq]
    exact hbelow
  exact Piece06.false_of_lakeFillTwoArcExit hcondition hlambda hlambda1 hc hmu hmu1 hrho2 hlarge
    hlea' hbelow'
    (h D eps S.diagram a b K hij hai hbi (S.pairwise a ha b hb hab) S.label_admissible
      (one_lt_length_of_two_le_rho hcondition hrho2) hfirst hsecond h₁ h₂ hw hoff hinner houter _
      (cell_mem S.diagram kept) hkept (hcell a) (hcell b))

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcLongStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.innerTwoArcLong_of_innerTwoArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.proof_of_innerTwoArcLong
