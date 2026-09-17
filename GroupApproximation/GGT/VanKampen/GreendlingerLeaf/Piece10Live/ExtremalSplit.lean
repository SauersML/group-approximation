import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveCore
import GroupApproximation.Meta.AxiomGuard

/-!
# The extremal-region core, split into contiguity and side bounds

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-11a.

The gap `P10RegionMove.RoseExtremalCoreStatement` (module `Piece10Live/RegionMoveCore`) is split
into two statements with the same premise block.

* `ExtremalContigClauses K r source kept t₁ t₂ s₁ s₂`: every clause of the conclusion of
  `RoseExtremalCoreStatement` except the four bounds `s₁.length ≤ ε`, `s₂.length ≤ ε`,
  `lo ≤ t₂.start`, `t₂.start + t₂.length ≤ hi`, together with the *block containment*:
  - `t₂` sits inside the old target arc by positions: `K.targetArc.start ≤ t₂.start` and
    `t₂.start + t₂.length ≤ K.targetArc.start + K.targetArc.length`;
  - the free sides are made of darts of the old sides, one side each:
    `s₁ ⊆ firstSide ∧ s₂ ⊆ secondSide`, or `s₁ ⊆ secondSide ∧ s₂ ⊆ firstSide`.
* `RoseExtremalContiguityStatement` (OPEN, PLAUSIBLE): some witness satisfies these clauses.  This
  is the planarity core: the extremal region meets the arcs in contiguous blocks (so the kept arc
  darts are exactly `t₁⁻¹` and `t₂`, and the remaining kept darts are side darts), clause 1 (the
  class avoids the exterior face), properness.
* `RoseExtremalSideBoundStatement` (elementary): every witness of the clauses has the four bounds.
  Proof sketch.  The listing `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` is a permutation of a filter of the nodup
  cycle, so `s₁`, `s₂` are nodup; a nodup list contained in a side is a subpermutation of it
  (`List.subperm_of_subset`), so its length is at most the side length, which is at most `ε`
  (`K.firstSide_length_le`, `K.secondSide_length_le`).  The position bounds follow from
  `K.lo_le`, `K.le_hi` by `omega`.
* `extremalCore_of_contiguity_sideBound` (proved): the two statements give the core.

## Truth of the split

A witness of the clauses is a witness of the core as soon as the bounds hold, and the side-bound
statement is proved from the clauses by the argument above, so the split is sound.  The added block
containment is what "the extremal region meets the arcs in contiguous blocks" means for the listing
in cyclic order `firstSide' t₁'⁻¹ secondSide' t₂'`; on the three-petal flower
`c = p₁ q₁ | t₁⁻¹ | p₃ | t₂` the witness `s₁ = [p₁, q₁]`, `t₁' = t₁`, `s₂ = [p₃]`,
`t₂' = zeroArc t₂` satisfies it (first disjunct).  Risk (reported): a wrapping target arc
(`K.targetArc.start + K.targetArc.length > (outerDarts X).length`) whose extremal region eats a
prefix of the arc across the base point; then no `t₂'` has a start position above the old start.
The same risk is already present in the bound `lo ≤ t₂.start` of the core itself.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSplit

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Clauses

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The contiguity clauses of an extremal-region witness**: the conclusion clauses of
`RoseExtremalCoreStatement` without the four bounds, plus the block containment of `t₂` in the old
target arc and of the free sides in the old sides. -/
def ExtremalContigClauses (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (source kept : Fin X.rCellCount) (t₁ : CyclicArc (cellDarts X source))
    (t₂ : CyclicArc (outerDarts X)) (s₁ s₂ : List X.toCombMap.Dart) : Prop :=
  (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
    (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
  (cell X source).face ∉ flipFaces X.toCombMap K.faces
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
  (cell X kept).face ∈ flipFaces X.toCombMap K.faces
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
  List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
    (K.boundary.cycle.filter (movePred X.toCombMap
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))) ∧
  s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ≠ [] ∧
  (s₁.IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
  (s₂.IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
  (∀ a ∈ s₁.getLast?, ∀ b ∈ (invDarts X t₁.darts).head?,
    X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
  (∀ a ∈ (s₁ ++ invDarts X t₁.darts).getLast?, ∀ b ∈ s₂.head?,
    X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
  (∀ a ∈ (s₁ ++ invDarts X t₁.darts ++ s₂).getLast?, ∀ b ∈ t₂.darts.head?,
    X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
  t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length ∧
  K.targetArc.start.1 ≤ t₂.start.1 ∧
  t₂.start.1 + t₂.length ≤ K.targetArc.start.1 + K.targetArc.length ∧
  (((∀ d ∈ s₁, d ∈ K.firstSide) ∧ (∀ d ∈ s₂, d ∈ K.secondSide)) ∨
    ((∀ d ∈ s₁, d ∈ K.secondSide) ∧ (∀ d ∈ s₂, d ∈ K.firstSide)))

end Clauses

/-- **The contiguity statement** (OPEN, PLAUSIBLE; the planarity core of the rose step).  Under
the premises of `RoseExtremalCoreStatement`, some witness satisfies `ExtremalContigClauses`. -/
def RoseExtremalContiguityStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ (r : X.toCombMap.Dart) (source kept : Fin X.rCellCount)
          (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
          (s₁ s₂ : List X.toCombMap.Dart), ExtremalContigClauses K r source kept t₁ t₂ s₁ s₂

/-- **The side-bound statement** (elementary, see the module docstring).  Under the premises of
`RoseExtremalCoreStatement`, every witness of `ExtremalContigClauses` has short free sides and a
target arc between `lo` and `hi`. -/
def RoseExtremalSideBoundStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∀ (r : X.toCombMap.Dart) (source kept : Fin X.rCellCount)
          (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
          (s₁ s₂ : List X.toCombMap.Dart), ExtremalContigClauses K r source kept t₁ t₂ s₁ s₂ →
            s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
              t₂.start.1 + t₂.length ≤ hi

/-- **The extremal-region core from contiguity and side bounds.** -/
theorem extremalCore_of_contiguity_sideBound
    (hcontig : RoseExtremalContiguityStatement.{u, w, v})
    (hbound : RoseExtremalSideBoundStatement.{u, w, v}) :
    P10RegionMove.RoseExtremalCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, source, kept, t₁, t₂, s₁, s₂, hcl⟩ :=
    hcontig D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨hs₁, hs₂, hlo, hhi⟩ :=
    hbound D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose r source kept t₁ t₂ s₁ s₂
      hcl
  obtain ⟨hrout, hsource, hkept, hperm, hne, hs₁c, hs₂c, hj₁, hj₂, hj₃, ht₁, ht₂, -, -, -⟩ := hcl
  exact ⟨r, hrout, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hne, hs₁c, hs₂c,
    hj₁, hj₂, hj₃, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSplit

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSplit.ExtremalContigClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSplit.RoseExtremalContiguityStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSplit.RoseExtremalSideBoundStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSplit.extremalCore_of_contiguity_sideBound
