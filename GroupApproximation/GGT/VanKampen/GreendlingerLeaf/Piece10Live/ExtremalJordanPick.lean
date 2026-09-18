import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanReroute
import GroupApproximation.Meta.AxiomGuard

/-!
# The reroute statement from a pick rule on the arc-good classes

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-31.

**LOUD: the target `ExtremalJordanRerouteStatement` (`Piece10Live/ExtremalJordanReroute`, lane
gl-p10-30) is NOT closed outright here.**  It is reduced to ONE open Statement,
`ExtremalJordanPickStatement`, by `extremalJordanPick_extremalJordanReroute`.

## The pick rule

The *arc-good pool* is the set of classes `r` with `ExtremalJordanPickPool K r`: the choice
property and both arcs met through one end (`ExtremalArcEndBoth`).  The measure
`ExtremalJordanPickChanges K r` counts the kind changes (kept / removed) between cyclically
consecutive darts of the pocket walk after the removed loop darts are deleted; it is twice the
number of removed runs of non-loop darts (or `0`).

The pick rule: **take an arc-good class with the fewest kind changes.**
`ExtremalJordanPickStatement` says that the arc-good pool is nonempty and that every class the
rule picks has one removed run up to loops (`ExtremalJordanRerouteLoopRun`) or one pinning
vertex (`ExtremalArcEndExistsPinned`).  The minimum exists (`extremalJordanPick_exists_min`,
by the descent `extremalArcEnd_exists_of_descent`), and the picked class is the witness of the
target.

## LOUD: logical strength of the gap

`ExtremalJordanPickStatement` is logically STRONGER than `ExtremalJordanRerouteStatement` (it
implies it; the converse is not claimed: the target gives one good class, the pick clause asks
that every arc-good class of least measure be shaped).  It is strictly smaller in proof content:

* the existence clause drops the shape (and so the whole linked-runs half): it only asks for a
  choice class meeting both arcs through one end, a consequence of the target;
* the pick clause is a local rerouting step about one given class: an arc-good choice class
  with neither shape must be replaced by an arc-good choice class with fewer kind changes.  No
  simultaneous search over shape and arc ends remains; the descent to the minimum is proved.

It is not an equivalent restatement (strictly stronger), and not one of the refuted forms: the
measure is not the removed arc count, the pool is not the linked pool of lane gl-p10-21, and the
shape keeps the loop darts (the loop-free variant is false, see `ExtremalJordanReroute`).

## Truth check (lane gl-p10-31, scratchpad folder `gl-p10-31/`, script `pick5.py`)

Exact linear Lean forms (`ExtremalJordanPickChanges` as `c'.zip (c'.rotate 1)`), every
instance of the model of lanes gl-p10-17/21/27/30 (pocket walk, base point, arcs, source and
exterior regions), every choice class:

* 6 darts, every vertex degree: 6,489,102 instances, no failure of either clause (the pool is
  never empty; every class of least measure has one of the two shapes).
* 8 darts, vertex degree at most 3: 5,024,192 instances, no failure; 9,214,800 least-measure
  pool classes checked, and 5,934,504 pool classes have neither shape (so the pick clause is not
  vacuous: the rule really has to choose).
* Sanity: every class of measure at most `2` is a loop-run class, on every instance above.
* 7 darts, every vertex degree (`pick5.py 7 7 4 i`, files `s7_i.out`): 215,705,028 instances,
  no failure; 1,179,867,668 least-measure pool classes checked, and 8,710,464 pool classes have
  neither shape.

* In every instance checked, the least measure is `0` or `2`: the picked class has at most one
  removed run of non-loop darts, so it is already a loop-run class (the pinned alternative is
  kept in the conclusion only to make the Statement weaker).
* Rejected pick rules (script `pick.py`, `pick2.py`, `pick3.py`, `pick4.py`): over the shape
  pool, the fewest removed arc darts (`ExtremalArcEndRemoved`) FAILS at 8 darts of degree at most
  3 (64 instances; two monogon classes of one removed arc dart each, one in the middle of an
  arc), also with the ties broken by removed darts or runs; over all choice classes, the fewest
  removed arc darts then runs FAILS at 6 darts (168 instances); over the arc-good pool, the
  fewest removed runs counting loops FAILS at 8 darts (224 instances), and the fewest removed
  darts FAILS at 8 darts (550416 instances).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **A least element for a natural measure**: from one `P`-element, a `P`-element whose measure
is at most that of every `P`-element. -/
theorem extremalJordanPick_exists_min {α : Type*} (P : α → Prop) (μ : α → ℕ) (a : α)
    (ha : P a) : ∃ b, P b ∧ ∀ c, P c → μ b ≤ μ c := by
  refine extremalArcEnd_exists_of_descent P (fun b => ∀ c, P c → μ b ≤ μ c) μ ?_ a ha
  intro b _ hb
  by_contra hne
  exact hb fun c hc => Nat.not_lt.mp fun hlt => hne ⟨c, hc, hlt⟩

section PickPool

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The arc-good pool**: a choice class meeting both arcs through one end. -/
def ExtremalJordanPickPool (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) : Prop :=
  ExtremalClassChoice K r ∧ ExtremalArcEndBoth K r

open Classical in
/-- **The pocket walk without its removed loop darts**: the kept darts and the removed darts
that are not loops, in walk order. -/
noncomputable def ExtremalJordanPickWalk (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) : List X.toCombMap.Dart :=
  K.boundary.cycle.filter (fun x => P10ExtremalResidual.keptPred K r x ||
    !decide (X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x)))

/-- **Kind changes up to removed loops**: the cyclically consecutive pairs of darts of different
kind (kept / removed) on `ExtremalJordanPickWalk K r`. -/
noncomputable def ExtremalJordanPickChanges (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) : ℕ :=
  ((ExtremalJordanPickWalk K r).zip ((ExtremalJordanPickWalk K r).rotate 1)).countP
    (fun p => P10ExtremalResidual.keptPred K r p.1 != P10ExtremalResidual.keptPred K r p.2)

end PickPool

/-- **OPEN (lane gl-p10-31).**  Under the premises of `ExtremalJordanStatement`: some choice
class meets both arcs through one end, and every such class with the fewest kind changes up to
removed loops has one removed run up to loops or one pinning vertex.  LOUD: logically STRONGER
than `ExtremalJordanRerouteStatement` (`extremalJordanPick_extremalJordanReroute`), strictly
smaller in proof content (existence without shape, plus one local rerouting step); true in the
model (see the module docstring). -/
def ExtremalJordanPickStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        (∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r) ∧
        ∀ r : X.toCombMap.Dart, ExtremalJordanPickPool K r →
          (∀ r' : X.toCombMap.Dart, ExtremalJordanPickPool K r' →
            ExtremalJordanPickChanges K r ≤ ExtremalJordanPickChanges K r') →
          ExtremalJordanRerouteLoopRun K r ∨ ExtremalArcEndExistsPinned K r

/-- **The reroute statement from the pick rule**: take an arc-good choice class with the fewest
kind changes. -/
theorem extremalJordanPick_extremalJordanReroute (h : ExtremalJordanPickStatement.{u, w, v}) :
    ExtremalJordanRerouteStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨⟨r₀, h₀⟩, hpick⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hr, hle⟩ := extremalJordanPick_exists_min (ExtremalJordanPickPool K)
    (ExtremalJordanPickChanges K) r₀ h₀
  have hp := hpick r hr hle
  obtain ⟨hc, hT, hS⟩ := hr
  exact ⟨r, hc, hp, hT, hS⟩

/-- **Chain consequence**: the Jordan arc-end statement from the pick statement. -/
theorem extremalJordanPick_extremalJordan (h : ExtremalJordanPickStatement.{u, w, v}) :
    ExtremalJordanStatement.{u, w, v} :=
  extremalJordanReroute_extremalJordan (extremalJordanPick_extremalJordanReroute h)

/-- **Chain consequence**: the relative Greendlinger statement from the four-piece-off
statement and the pick statement. -/
theorem extremalJordanPick_relativeGreendlinger
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : ExtremalJordanPickStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  extremalJordanReroute_relativeGreendlinger hoff (extremalJordanPick_extremalJordanReroute h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_exists_min
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickPool
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickChanges
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_extremalJordanReroute
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_extremalJordan
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_relativeGreendlinger

