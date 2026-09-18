import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalContig
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalSideBound
import GroupApproximation.Meta.AxiomGuard

/-!
# The wrap risk of the extremal core: no-wrap variants

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-12a.

## Verdict: wrapping is NOT excluded

`PocketFaceSet D eps X lo hi` records `lo ≤ K.targetArc.start` and
`K.targetArc.start + K.targetArc.length ≤ hi`, but nothing bounds `hi` by `|outerDarts X|`.  None
of the premises of `P10RegionMove.RoseExtremalCoreStatement` (least area, letter labels, walk
order, not first-turn order, proper arcs, pinched, rose configuration) does either.  So a target
arc may wrap past the base point of the outer cycle: `K.targetArc.start + K.targetArc.length >
|outerDarts X|`, with `hi` as large as that sum.  When the extremal region removes a proper prefix
of such an arc reaching past the base point, the kept target block starts at a position
`K.targetArc.start + i - |outerDarts X| < K.targetArc.start = lo` (the start is stored in
`Fin |outerDarts X|`).  No `t₂` then satisfies `lo ≤ t₂.start`, so the clause `lo ≤ t₂.start.1`
of the core and the clause `K.targetArc.start ≤ t₂.start` of
`P10ExtremalContig.RoseExtremalContigResidualStatement` are UNSAFE.  No full-premise counterexample
has been built (small one-vertex rose searches always found a witness), so the originals are
suspect, not refuted.

## Where a no-wrap hypothesis is available

Every live use of the step comes through `sectionPocketCutInput_of_residualsTwoArc`, where
`hi = cuts.cut j.succ ≤ cuts.cut (Fin.last _) = |Δ.boundaryWord| = |outerDarts X₀|`
(`SectionCuts.cut_mono`, `SectionCuts.cut_last`, `Embedded.dartWord_outerDarts`, and the
O-equivalence `S.equiv.trans E₀`).  The pinch induction keeps `hi` and passes to O-equivalent
copies, which keep `|outerDarts|`.  So the premise `hi ≤ |outerDarts X|` is available all the way
down, and the no-wrap variants below are sufficient (modules `ExtremalWrapInPlace`,
`ExtremalWrapStep`, `ExtremalWrapPinch`).

* `targetArc_noWrap` (proved): under `hi ≤ |outerDarts X|` the target arc does not wrap.
* `outerDarts_length_eq_boundaryWord_length`, `outerDarts_length_eq_of_oEquivalent` (proved).
* `RoseExtremalCoreNoWrapStatement` (OPEN, PLAUSIBLE): the core with the premise
  `hi ≤ |outerDarts X|`; `extremalCoreNoWrap_of_extremalCore` (proved) shows it is implied by the
  original.
* `RoseExtremalContigResidualNoWrapStatement` (OPEN, PLAUSIBLE) with
  `contigResidualNoWrap_of_contigResidual` and `extremalCoreNoWrap_of_contigResidualNoWrap`
  (proved).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Lengths

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **No wrap of the target arc** when `hi` is at most the length of the outer cycle. -/
theorem targetArc_noWrap {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
    {lo hi : ℕ} (K : PocketFaceSet D eps X lo hi) (h : hi ≤ (outerDarts X).length) :
    K.targetArc.start.1 + K.targetArc.length ≤ (outerDarts X).length :=
  Nat.le_trans K.le_hi h

/-- The outer cycle is as long as the boundary word. -/
theorem outerDarts_length_eq_boundaryWord_length (X : DiscDiagram.{u, w, v} W) :
    (outerDarts X).length = X.boundaryWord.length := by
  rw [← dartWord_outerDarts X]
  simp only [dartWord, List.length_map]

/-- O-equivalent diagrams have outer cycles of the same length. -/
theorem outerDarts_length_eq_of_oEquivalent {X X' : DiscDiagram.{u, w, v} W}
    (e : OEquivalentDiscDiagram X X') : (outerDarts X').length = (outerDarts X).length := by
  rw [outerDarts_length_eq_boundaryWord_length, outerDarts_length_eq_boundaryWord_length,
    e.boundaryWord_eq]

end Lengths

/-- **The extremal-region core without wrap** (OPEN, PLAUSIBLE): `RoseExtremalCoreStatement` with
the extra premise `hi ≤ |outerDarts X|`, so the target arc does not wrap. -/
def RoseExtremalCoreNoWrapStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart,
          (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
            (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
          ∃ (source kept : Fin X.rCellCount),
            (cell X source).face ∉ flipFaces X.toCombMap K.faces
              (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
            (cell X kept).face ∈ flipFaces X.toCombMap K.faces
              (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
            ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
              (s₁ s₂ : List X.toCombMap.Dart),
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
              s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
              t₂.start.1 + t₂.length ≤ hi ∧
              t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

/-- **The no-wrap core is implied by the original core** (it only adds a premise). -/
theorem extremalCoreNoWrap_of_extremalCore
    (h : P10RegionMove.RoseExtremalCoreStatement.{u, w, v}) :
    RoseExtremalCoreNoWrapStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi _ hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose

/-- **The residual contiguity statement without wrap** (OPEN, PLAUSIBLE):
`P10ExtremalContig.RoseExtremalContigResidualStatement` with the premise `hi ≤ |outerDarts X|`. -/
def RoseExtremalContigResidualNoWrapStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ (r : X.toCombMap.Dart) (source kept : Fin X.rCellCount)
          (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
          (s₁ s₂ : List X.toCombMap.Dart),
            P10ExtremalContig.ExtremalContigResidualClauses K r source kept t₁ t₂ s₁ s₂

/-- **The no-wrap residual is implied by the original residual.** -/
theorem contigResidualNoWrap_of_contigResidual
    (h : P10ExtremalContig.RoseExtremalContigResidualStatement.{u, w, v}) :
    RoseExtremalContigResidualNoWrapStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi _ hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose

/-- **The no-wrap core from the no-wrap residual**: target properness by `omega`, side and
position bounds by `P10ExtremalSideBound.sideBound`. -/
theorem extremalCoreNoWrap_of_contigResidualNoWrap
    (h : RoseExtremalContigResidualNoWrapStatement.{u, w, v}) :
    RoseExtremalCoreNoWrapStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, source, kept, t₁, t₂, s₁, s₂, hrout, hsource, hkept, hperm, hne, hs₁c, hs₂c,
      hj₁, hj₂, hj₃, ht₁, hst, hen, hside⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have ht₂ : t₂.length < (outerDarts X).length := by omega
  have hcl : P10ExtremalSplit.ExtremalContigClauses K r source kept t₁ t₂ s₁ s₂ :=
    ⟨hrout, hsource, hkept, hperm, hne, hs₁c, hs₂c, hj₁, hj₂, hj₃, ht₁, ht₂, hst, hen, hside⟩
  obtain ⟨hs₁, hs₂, hlo, hhi⟩ :=
    P10ExtremalSideBound.sideBound D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
      r source kept t₁ t₂ s₁ s₂ hcl
  exact ⟨r, hrout, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hne, hs₁c, hs₂c,
    hj₁, hj₂, hj₃, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.targetArc_noWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.outerDarts_length_eq_boundaryWord_length
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.outerDarts_length_eq_of_oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.RoseExtremalCoreNoWrapStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalCoreNoWrap_of_extremalCore
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.RoseExtremalContigResidualNoWrapStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.contigResidualNoWrap_of_contigResidual
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalCoreNoWrap_of_contigResidualNoWrap
