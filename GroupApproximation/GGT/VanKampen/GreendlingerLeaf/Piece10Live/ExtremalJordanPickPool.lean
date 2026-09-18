import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickPoolSide
import GroupApproximation.Meta.AxiomGuard

/-!
# Existence of a pool class from a region class

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-34.

**LOUD: clause (a) of `ExtremalJordanPickRunStatement` (`Piece10Live/ExtremalJordanPickRun`,
lane gl-p10-32), `∃ r, ExtremalJordanPickPool K r`, is NOT closed outright here.**  It is reduced
to ONE open Statement, `ExtremalJordanPickPoolRegionStatement`, by
`extremalJordanPickPool_exists`.

## The split

(a) asks for a class that is a choice class (`ExtremalClassChoice`, part (a1)) and meets both
arcs through one end (`ExtremalArcEndBoth`, part (a2)).  A face class lies on one side of
`K.faces` (`extremalJordanPickPool_mem_faces_iff`), and on each side (a2) and the avoidance
clauses of (a1) come for free once the class is placed (`Piece10Live/ExtremalJordanPickPoolSide`,
PROVED outright, no hypothesis on `K`):

* an outside class avoiding the exterior and source faces keeps every arc dart, and avoids the
  kept cell `K.kept`;
* an inside class avoids the exterior and source faces; if it meets no arc dart it keeps every
  arc dart, and it needs one avoided cell of `K.faces`.

So all arc-end and kept-dart combinatorics is proved, and the Statement asks only for a class
placed as above (`ExtremalJordanPickPoolRegion`): pure region existence.  No canonical `r` is
available: in the model neither side alone always works (below).

(a1) alone is NOT proved outright either: it needs a region of the walk graph off the exterior
and source faces, or an inside region off some cell of `K.faces`.  A C-shaped walk graph (one
inside region holding every cell of `K.faces`, the outside split into the exterior and source
regions only) has no choice class at all, so it must be excluded from the premises, which is
planar (Euler) information not available in the corpus.

## LOUD: logical strength of the gap

`ExtremalJordanPickPoolRegionStatement` is logically STRONGER than (a): every region class is a
pool class (`extremalJordanPickPool_of_region`), the converse is not claimed.  It is strictly
smaller in proof content: no arc-end, kept-dart or clause-by-clause case split remains, only the
existence of one region class.  It is not an equivalent restatement of (a).

## Truth check (model)

Exact Lean form, in the model of lanes gl-p10-17/27/30/31/32 (pocket walk, arcs, source and
exterior regions), every vertex degree, script `gl-p10-34/cls.py`: (A) an outside class off the
exterior and source regions, (B) an inside class off a cell of `K.faces` and off every arc dart.

| darts | instances | A and B   | B only  | A only  | neither |
|-------|-----------|-----------|---------|---------|---------|
| 3     | 204       | 0         | 36      | 168     | 0       |
| 4     | 7,852     | 4,816     | 968     | 2,068   | 0       |
| 5     | 220,700   | 178,760   | 18,090  | 23,850  | 0       |
| 6     | 6,489,102 | 5,918,994 | 298,650 | 271,458 | 0       |

So the Statement held on every instance, and neither disjunct can be dropped (both "only" columns
are nonempty).  Every instance with a (B) class also had an inside pool class, as
`extremalJordanPickPool_of_inside` predicts.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **OPEN (lane gl-p10-34).**  Under the premises of `ExtremalJordanStatement`, some class is a
region class: outside `K.faces` and off the exterior and source faces, or inside `K.faces`, off
some cell of `K.faces` and off every arc dart.  LOUD: logically STRONGER than clause (a) of
`ExtremalJordanPickRunStatement` (`extremalJordanPickPool_exists`), strictly smaller in proof
content; true in the model at 3 to 6 darts (see the module docstring). -/
def ExtremalJordanPickPoolRegionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, ExtremalJordanPickPoolRegion K r

section PickPoolExists

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Clause (a) from the region statement**: under the premises of `ExtremalJordanStatement`,
some class is a pool class. -/
theorem extremalJordanPickPool_exists (hreg : ExtremalJordanPickPoolRegionStatement.{u, w, v})
    (hwrap : hi ≤ (outerDarts X).length) (hlea : X.LeastArea)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk) (hnft : ¬ K.FirstTurns)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (hpinch : ¬Unpinched X.toCombMap K.faces) (hrose : P10ChordLift.AllNonFirstTurnsCrossed K) :
    ∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r := by
  obtain ⟨r, hr⟩ := hreg D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, extremalJordanPickPool_of_region K hr⟩

end PickPoolExists

/-- **The wire**: the region statement and the rerouting step for every pocket give
`ExtremalJordanPickRunStatement`. -/
theorem extremalJordanPickPool_extremalJordanPickRun
    (hreg : ExtremalJordanPickPoolRegionStatement.{u, w, v})
    (hdesc : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}
      (K : PocketFaceSet D eps X lo hi), ExtremalJordanPickRunDescent K) :
    ExtremalJordanPickRunStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨extremalJordanPickPool_exists hreg hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose,
    hdesc K⟩

/-- **The wire, descent under the premises**: the region statement and the rerouting step for
every pocket meeting the premises of `ExtremalJordanStatement` give
`ExtremalJordanPickRunStatement`. -/
theorem extremalJordanPickPool_extremalJordanPickRun_of_premises
    (hreg : ExtremalJordanPickPoolRegionStatement.{u, w, v})
    (hdesc : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
      hi ≤ (outerDarts X).length → X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length →
        ¬Unpinched X.toCombMap K.faces →
        P10ChordLift.AllNonFirstTurnsCrossed K → ExtremalJordanPickRunDescent K) :
    ExtremalJordanPickRunStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨extremalJordanPickPool_exists hreg hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose,
    hdesc D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickPoolRegionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_exists
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_extremalJordanPickRun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_extremalJordanPickRun_of_premises
