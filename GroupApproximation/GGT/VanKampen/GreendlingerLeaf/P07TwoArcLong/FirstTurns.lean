import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLongUnpinch
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellGoodCorners
import GroupApproximation.Meta.AxiomGuard

/-!
# The long-word inner two-arc pocket, from a first-turn cell pocket in a copy

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `gl-p07-88`.  The target is
`P07LakeExclusion.CellPocketInnerTwoArcLongStatement`.

## Proof plan

* **The residual** `CellPocketInnerTwoArcFirstTurnsStatement`: under the hypotheses of the target,
  some O-equivalent copy with letter labels carries a cell pocket face set in first-turn order
  (`CellPocketFaceSet.FirstTurns`).
* **The reduction** `innerTwoArcLong_of_firstTurns`.  `CellPocketFaceSet.copyRegion_of_firstTurns`
  unpinches that pocket (it is proved, over relator words longer than one letter), giving the exit
  on a second copy.  `P07LakeExclusion.lakeFillTwoArcExit_of_oEquivalent` pulls it back to `X`.

## Why the residual is strictly smaller

The target asks for the pinch-free pocket region itself.  The residual only asks for first-turn
order; the unpinch from first-turn order to a simple pocket and then to a pocket region whose
cycles follow their boundaries is `copyRegion_of_firstTurns`.  It is not an equivalent restatement:
its conclusion needs both arcs nonempty and both sides of length `≤ ε`, which the exit does not.

## Why the residual is true

* The inner pocket `sideFaces K \ (a ∪ b)`, with its lakes filled, has the boundary cycle
  `s_1 Ḡ_1 s_2 Ḡ_2` described in `P07LakeExclusion/InnerTwoArc.lean`.  The gaps are nonempty arcs
  and the sides are the far sides of `b` and `a`, of length `≤ ε`.
* Its cycle is in walk order but may be pinched.  The two-arc doubling of the target's docstring
  gives an O-equivalent copy in which the pocket is simple.
* A simple closed walk is in first-turn order.  At each vertex `v` it has one incoming dart `d`
  and one outgoing dart `e`, so rotating from `e` reaches `alpha d` before any other dart on an edge
  of the walk.
* **Model check** (48-dart map, `V = 18`, `ε = 1`, `gl-p07-88/ft_search.py`).  No face set of `X`
  itself is a cell pocket in first-turn order: the natural pocket `{C, H_1, H_2}` splits at the
  pinches `p_0`, `q_0` into three first-turn cycles.  This is why the in-place
  `InnerPocketEnclosedTwoArcStatement` fails.  The residual allows a copy, and one exists over the
  trivial group, the group of the target's own model check.  Glue `C` along three edges to `Π_i`
  and along three to `Π_j`.  Fill the rest with one `G`-face inside the exterior bigon.  Then
  `{C}` is a simple cell pocket with empty sides.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcLong

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **A first-turn cell pocket in a copy, for the inner two-arc pocket.**  Under the hypotheses of
`P07LakeExclusion.CellPocketInnerTwoArcLongStatement`, some O-equivalent copy with letter labels
carries a cell pocket face set in first-turn order.
* **Why it is true.**  The two-arc doubling makes the inner pocket simple in a copy, and a simple
  cell pocket is in first-turn order.  See the module docstring.
* **Why it is strictly smaller.**  The unpinch from first-turn order to the exit is
  `CellPocketFaceSet.copyRegion_of_firstTurns` (`innerTwoArcLong_of_firstTurns`). -/
def CellPocketInnerTwoArcFirstTurnsStatement : Prop :=
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
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.FirstTurns

/-- **The long-word inner two-arc pocket from a first-turn cell pocket in a copy.**
`copyRegion_of_firstTurns` unpinches the pocket into the exit on a second copy, and
`lakeFillTwoArcExit_of_oEquivalent` pulls the exit back along the first. -/
theorem innerTwoArcLong_of_firstTurns (h : CellPocketInnerTwoArcFirstTurnsStatement.{u, w, v}) :
    P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨X', i', j', K', ⟨e⟩, hlabel', hK'⟩ := h D eps X a b K hij hai hbi hab hlabel hW hfirst
    hsecond h₁ h₂ hw hoff hinner houter C hC hCf hCa hCb
  obtain ⟨X'', hE, hlabel'', P, C', i'', j'', s₁, s₂, A₁, A₂, hC', hCf', hi, hj, hdec, hn₁, hn₂,
      hin, hout⟩ := K'.copyRegion_of_firstTurns hW hlabel' hK'
  exact P07LakeExclusion.lakeFillTwoArcExit_of_oEquivalent e
    ⟨X'', P, C', i'', j'', A₁, A₂, s₁, s₂, hE, hlabel'', hin, hout, hC', hCf', hi, hj, hdec, hn₁,
      hn₂⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcLong

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcLong.CellPocketInnerTwoArcFirstTurnsStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcLong.innerTwoArcLong_of_firstTurns
