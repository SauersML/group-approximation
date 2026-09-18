import GroupApproximation.Manuscript.NonMF.Full.GL03B.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# The enclosed inner pocket of a cell pocket walk: the corrected statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex 2134, Hull's small cancellation theorem, through Osin's Lemma 9.7).

## The local statements are false

`Full.GL03B.InnerPocketEnclosedTwoArcLocal` and `Full.GL03B.InnerPocketEnclosedTwoArcPinchedLocal`
(and so the foreign `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`) are false.  Their
conclusion asks for a cell `Π_{k₁}` off the enclosed face set.  The pocket may instead absorb every
relator cell.  This refutes no printed sentence.  `thm:hull` (non_mf_groups_exist.tex 2134–2141)
cites Hull, Theorem 7.1, whose small cancellation input is Osin's Lemma 9.7.  The false statements
are intermediate formal clauses of this formalization's route through the proof of Lemma 9.7(b).
The counterexample below is on paper.  A Lean model would need a concrete planar map with 48 darts
and the Euler characteristics of both reclosed maps, which cannot be checked without compiling.

**Counterexample.**  Take the trivial group, every label `base 1`, and `ε = 1`.
* The outer face `o` is a digon with edges `s₁` (`v' → v`) and `s₂` (`v → v'`).
* `b` is a `G`-digon with edges `s₁`, `far_b`, and `a` is a `G`-digon with edges `s₂`, `far_a`.
  Both regions have source `i`, target `j` and empty arcs, so `b.sideFrom j = [s₁]` and
  `a.sideFrom i = [s₂]`.
* Between `far_a` and `far_b` lie three relator cells, all hexagons: `Π_i` through `v`, `Π_j`
  through `v'`, and `C`.  The edges `p₃ c₀` and `c₃ q₃` join opposite vertices of `Π_i`, `C`
  and `C`, `Π_j`.  They cut the rest into two `G`-faces `H₁`, `H₂`.  Each of `H₁`, `H₂` has three
  edges on each of the three cells.
* This gives `V = 18`, `E = 24` and `F = 8`.  The pocket walk is
  `K = s₁ · (all of ∂Π_i)⁻¹ · s₂ · (all of ∂Π_j)⁻¹`.

All the hypotheses hold.
* `K` is noncrossing, and its side is `{a, b, H₁, H₂, C}`, which does not contain `o`.
* The inner reclosed map has `χ = 2`.  The outer one has three discs glued at `v` and `v'`, so
  `χ = 3 + 1 - 2 = 2`.
* The outer cycle does not follow its boundary.

The conclusion fails.
* An enclosed outer walk reading `s₁' A₁⁻¹ s₂' A₂⁻¹`, with `|s₁'|, |s₂'| ≤ 1`, has at most two
  darts off relator cells.  So a face set holding `Π_i`, `Π_j` or `C` holds `H₁` and `H₂` (each
  would contribute three darts).
* A cell off the face set with every neighbour inside turns to its own successors (`turn_next`
  with `m = 1`).  It would form a closed orbit on its own, while `s₁`, `s₂` or `far_a`, `far_b`
  also face the set.
* So every relator cell is inside, and no cell `k₁` off the face set exists.

The near miss is `faces = {C, H₁, H₂}` with walk `far_b · ∂Π_i · far_a · ∂Π_j`.  It is an
`EnclosedFaceSet`, since `turn_mem` holds, but it is not successor-form.  If `d` is the dart of
`Π_i` arriving at `v`, then `σ (α d) = facePerm d` is the next dart of `Π_i`, and it is on the walk.
So `turn_next` with `m = 1` forces that dart, not `far_a`, as the next position.

## The correction

`InnerPocketEnclosedTwoArcCorrected` has the same hypotheses and adds a disjunct: an enclosed face
set holding every relator cell, with outer walk of length at most `2ε`.  In the model this is the
whole inner disc, with outer walk `s₁ s₂`.  `InnerPocketEnclosedTwoArcPinchedCorrected` adds the
pinch hypothesis.  The lake-filling proof does not use it.
-/

namespace GroupApproximation.Full.GL03BPinch

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **The enclosed inner pocket of a cell pocket walk, corrected.**  The hypotheses of
`Full.GL03B.InnerPocketEnclosedTwoArcLocal`.  The conclusion is its conclusion, or an enclosed face
set holding every relator cell whose outer walk has length at most `2ε` (Osin, proof of
Lemma 9.7(b); `thm:hull`). -/
def InnerPocketEnclosedTwoArcCorrected : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : Embedded.RegionCandidate D eps X)
    (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : Embedded.CyclicArc (Embedded.cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : Embedded.CyclicArc (Embedded.cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ SimpleClosedWalkSides.sideFaces X.toCombMap K.walk →
      (Surgery.MapCollapse.reclosedMap X.toCombMap
          (SimpleClosedWalkSides.sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (Surgery.MapCollapse.reclosedMap X.toCombMap
          (SimpleClosedWalkSides.sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ SimpleClosedWalkSides.sideFaces X.toCombMap K.walk →
        C.face ∉ a.1 → C.face ∉ b.1 →
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
          (k₁ k₂ : Fin X.rCellCount) (A₁ : Embedded.CyclicArc (Embedded.cellDarts X k₁))
          (A₂ : Embedded.CyclicArc (Embedded.cellDarts X k₂)) (s₁ s₂ : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧
            (∃ C' ∈ X.relatorCells, C'.face ∈ faces) ∧
            (Embedded.cell X k₁).face ∉ faces ∧ (Embedded.cell X k₂).face ∉ faces ∧
            Embedded.invDarts X outerWalk =
              s₁ ++ Embedded.invDarts X A₁.darts ++ s₂ ++ Embedded.invDarts X A₂.darts ∧
            s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ (A₁.length = 0 ∨ 0 < A₂.length)) ∨
        ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧
            (∀ C' ∈ X.relatorCells, C'.face ∈ faces) ∧ outerWalk.length ≤ eps + eps

/-- **The pinched enclosed inner pocket, corrected.**  `InnerPocketEnclosedTwoArcCorrected` with
the extra hypothesis that the complement cycle of the pocket walk does not follow its boundary
walk (Osin, proof of Lemma 9.7(b); `thm:hull`). -/
def InnerPocketEnclosedTwoArcPinchedCorrected : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : Embedded.RegionCandidate D eps X)
    (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : Embedded.CyclicArc (Embedded.cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : Embedded.CyclicArc (Embedded.cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ SimpleClosedWalkSides.sideFaces X.toCombMap K.walk →
      (Surgery.MapCollapse.reclosedMap X.toCombMap
          (SimpleClosedWalkSides.sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (Surgery.MapCollapse.reclosedMap X.toCombMap
          (SimpleClosedWalkSides.sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ¬ (hw.outerCycle X.planar).FollowsBoundary →
      ∀ C ∈ X.relatorCells, C.face ∈ SimpleClosedWalkSides.sideFaces X.toCombMap K.walk →
        C.face ∉ a.1 → C.face ∉ b.1 →
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
          (k₁ k₂ : Fin X.rCellCount) (A₁ : Embedded.CyclicArc (Embedded.cellDarts X k₁))
          (A₂ : Embedded.CyclicArc (Embedded.cellDarts X k₂)) (s₁ s₂ : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧
            (∃ C' ∈ X.relatorCells, C'.face ∈ faces) ∧
            (Embedded.cell X k₁).face ∉ faces ∧ (Embedded.cell X k₂).face ∉ faces ∧
            Embedded.invDarts X outerWalk =
              s₁ ++ Embedded.invDarts X A₁.darts ++ s₂ ++ Embedded.invDarts X A₂.darts ∧
            s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ (A₁.length = 0 ∨ 0 < A₂.length)) ∨
        ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧
            (∀ C' ∈ X.relatorCells, C'.face ∈ faces) ∧ outerWalk.length ≤ eps + eps

/-- **The pinched corrected statement from the corrected statement** (`thm:hull`). -/
theorem innerPocketEnclosedTwoArcPinchedCorrected_of_corrected
    (h : InnerPocketEnclosedTwoArcCorrected.{u, w, v}) :
    InnerPocketEnclosedTwoArcPinchedCorrected.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter _ C hC hCf hCa hCb
  exact h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC
    hCf hCa hCb

end GroupApproximation.Full.GL03BPinch

#audit_axioms GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcPinchedCorrected_of_corrected
