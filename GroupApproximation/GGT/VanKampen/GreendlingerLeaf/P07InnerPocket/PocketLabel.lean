import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabelDart
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: labels of pocket-orbit darts

Lane `gl-p07-08` (`lanes/carto-gl-p07.md`), infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`, Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  Certifies no printed sentence on its own.

## Statement

`PocketOrbitLabelStatement`.  Take the pocket walk `K` between cells `Π_i`, `Π_j`, with regions `a`,
`b` joining them, sides `K.firstSide = b.sideFrom j`, `K.secondSide = a.sideFrom i` and gaps
`G₁`, `G₂`.  Take a kept relator cell `C` on the side of `K` and off `a`, `b`, and set
`Q₀ = walkKeep K ∨ walkKeep ∂a ∨ walkKeep ∂b`.  Let `L` be a duplicate-free list of `Q₀`-darts based
in the `Q₀`-face class of `C.face`.  Then every dart of `L`
* is on `invDarts G₁` or `invDarts G₂`, or
* reverses a dart of `a.sideFrom j` or of `b.sideFrom i`.
At most `ε` darts of `L` reverse a dart of `a.sideFrom j`, and the same holds for `b.sideFrom i`.

## Why no upstream interface is assumed

* **Lane 03** (the class stays off `a`, `b` and inside `sideFaces K`): only the part needed here is
  used, and it is proved in `PocketLabel.pocket_faceOf`.
* **Lane 04** (the list `L` of the class): `L` is quantified, with only the forward half of lane 04's
  membership iff and `L.Nodup`.  This makes the theorem stronger.  Lane 15 applies it to lane 04's
  `L` through `.mp` of that iff.
* **Other hypotheses.**  The unused hypotheses of the P07 block (`Disjoint a.1 b.1`, labels, word
  lengths, `X.outerFace ∉ sideFaces K`, the two Euler identities) are left out, which again only
  strengthens the theorem.
So the endpoint `pocketOrbitLabel` is unconditional.

## Proof

* **Labels.**  `PocketLabel.pocket_faceOf` puts the base face in `sideFaces K` and off `a`, `b`.
  `PocketLabel.label_of_pocket` then does the case analysis on `Q₀`.
* **Counts.**  `PocketLabel.length_filter_le_of_alpha_mem`, using injectivity of `α` and
  `RegionCandidate.sideFrom_length_le`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded SimpleClosedWalkSides

open Classical in
/-- **Labels of pocket-orbit darts.**  Consider a duplicate-free list `L` of darts on an edge of the
pocket walk `K`, of `∂a` or of `∂b`, whose base faces lie in the class of the kept cell `C` under
face moves and crossings off `K`, `∂a`, `∂b`.
* Every dart of `L` is on a gap `invDarts G₁`, `invDarts G₂`, or reverses a dart of a far side
  `a.sideFrom j`, `b.sideFrom i`.
* Each far side is reversed by at most `ε` darts of `L`. -/
def PocketOrbitLabelStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    ∀ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i →
    ∀ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j →
    IsNoncrossingClosedWalk X.toCombMap K.walk →
    ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
    ∀ L : List X.toCombMap.Dart, L.Nodup →
      (∀ d ∈ L,
        (walkKeep X.toCombMap K.walk d ∨ walkKeep X.toCombMap a.2.boundary.cycle d ∨
          walkKeep X.toCombMap b.2.boundary.cycle d) ∧
        ∃ x, X.toCombMap.faceOf x = X.toCombMap.faceOf d ∧ ∃ y, X.toCombMap.faceOf y = C.face ∧
          Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (fun z =>
            walkKeep X.toCombMap K.walk z ∨ walkKeep X.toCombMap a.2.boundary.cycle z ∨
              walkKeep X.toCombMap b.2.boundary.cycle z)) y x) →
      (∀ d ∈ L, d ∈ invDarts X G₁.darts ∨ d ∈ invDarts X G₂.darts ∨
          X.toCombMap.alpha d ∈ a.sideFrom j ∨ X.toCombMap.alpha d ∈ b.sideFrom i) ∧
        (L.filter fun d => decide (X.toCombMap.alpha d ∈ a.sideFrom j)).length ≤ eps ∧
        (L.filter fun d => decide (X.toCombMap.alpha d ∈ b.sideFrom i)).length ≤ eps

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbitLabelStatement

open Classical in
/-- **Labels of pocket-orbit darts, proved.**  The labels come from `PocketLabel.pocket_faceOf` and
`PocketLabel.label_of_pocket`.  The counts come from `PocketLabel.length_filter_le_of_alpha_mem`
and `RegionCandidate.sideFrom_length_le`. -/
theorem pocketOrbitLabel : PocketOrbitLabelStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hfirst hsecond G₁ h₁ G₂ h₂ hw C _ hCK hCa hCb
    L hL hmem
  refine ⟨fun d hd => ?_, ?_, ?_⟩
  · obtain ⟨hQ, hcls⟩ := hmem d hd
    obtain ⟨hK, ha, hb⟩ := PocketLabel.pocket_faceOf hw hCK hCa hCb hcls
    exact PocketLabel.label_of_pocket hij hai hbi hfirst hsecond h₁ h₂ hw hQ hK ha hb
  · refine le_trans (PocketLabel.length_filter_le_of_alpha_mem hL _ ?_) (a.sideFrom_length_le j)
    intro d _ hpd
    exact of_decide_eq_true hpd
  · refine le_trans (PocketLabel.length_filter_le_of_alpha_mem hL _ ?_) (b.sideFrom_length_le i)
    intro d _ hpd
    exact of_decide_eq_true hpd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketOrbitLabel

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
