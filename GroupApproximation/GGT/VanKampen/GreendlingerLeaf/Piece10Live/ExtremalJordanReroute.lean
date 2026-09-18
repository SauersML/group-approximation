import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanRerouteRuns
import GroupApproximation.Meta.AxiomGuard

/-!
# The Jordan arc-end statement from a loop-run or pinned class

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-30.

`ExtremalJordanStatement` (lane gl-p10-17, `Piece10Live/ExtremalJordan`) asks for a class with
the choice property, linked runs, and each of the two arcs met through one end.  Here the linked
runs are replaced by a *shape* of the class on the pocket walk:

* `ExtremalJordanRerouteLoopRun` (one removed run, up to loop darts), or
* `ExtremalArcEndExistsPinned` (every kept/removed change at one vertex, lane gl-p10-25).

Each shape gives linked runs by a proved argument (`extremalJordanReroute_linked_of_loopRun`, via
the parity count `extremalJordanReroute_closed_run_loops`, and
`extremalArcEndExists_linked_of_pinned`), so `extremalJordanReroute_extremalJordan` proves
`ExtremalJordanStatement` from `ExtremalJordanRerouteStatement`.

## Strength: LOUD

**`ExtremalJordanRerouteStatement` is logically STRONGER than `ExtremalJordanStatement`**: the
shape implies linked runs, not conversely.  It is strictly smaller in proof content: the whole
linked-runs conclusion (the Jordan-curve half of the target) is discharged here by the parity
count at a vertex, and what is left is a combinatorial statement about the kept/removed pattern
of one class along the pocket walk, plus the two arc-end conditions.

## Truth check (finite model of lanes gl-p10-17/21/27, exact linear Lean forms)

* `ExtremalJordanStatement` holds at every pocket walk of 3 to 7 darts (6 darts: 6,489,102
  instances; 7 darts: 215,705,028) and at 8 darts with vertex degree at most 3 (5,024,192
  instances): no failure.
* `ExtremalJordanRerouteStatement` holds on every one of the same 7-dart and 8-dart
  (degree at most 3) instances, in the exact linear form stated here.
* The loop-free variant FAILS: "one run (`ExtremalArcEndExistsOneRun`) or pinned, and both arc
  ends" has no witness in 224 instances at 8 darts, degree at most 3, for example vertices
  `[1,0,0,1,0,1,2,2]` (tail of dart `i` is vertex `i-1`, head is vertex `i`), region pairs
  `[(0,1),(2,3),(4,5),(2,1),(4,1),(4,3),(0,1),(6,1)]`, target arc `[6,7,0]`, empty source arc.
  The loop darts are what the rerouting uses.
* Sanity in the model: every class with `ExtremalJordanRerouteLoopRun` or
  `ExtremalArcEndExistsPinned` has linked runs (every class, every base point, 7 darts and
  8 darts of degree at most 3), as proved here.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section RerouteOneRun

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **One removed run is one removed run up to loops.** -/
theorem extremalJordanReroute_loopRun_of_oneRun (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) (h : ExtremalArcEndExistsOneRun K r) :
    ExtremalJordanRerouteLoopRun K r := by
  obtain ⟨A, B, C, hdec, ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩⟩ := h
  · refine ⟨A, B, C, hdec, Or.inl ⟨fun x hx => Or.inl ?_, hB⟩⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hA x hx
    · exact hC x hx
  · refine ⟨A, B, C, hdec, Or.inr ⟨fun x hx => ?_, fun x hx => Or.inl (hB x hx)⟩⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hA x hx
    · exact hC x hx

end RerouteOneRun

/-- **OPEN (lane gl-p10-30).**  Under the premises of `ExtremalJordanStatement`, a choice class
exists that meets each arc through one end and has one removed run up to loops or is pinned at
one vertex.  LOUD: logically STRONGER than `ExtremalJordanStatement`
(`extremalJordanReroute_extremalJordan`), strictly smaller in proof content (linked runs are
proved); true in the model at 7 darts and at 8 darts, degree at most 3 (see the module
docstring). -/
def ExtremalJordanRerouteStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, ExtremalClassChoice K r ∧
          (ExtremalJordanRerouteLoopRun K r ∨ ExtremalArcEndExistsPinned K r) ∧
          ExtremalJordanArcEnd K r K.targetArc.darts ∧
          ExtremalJordanArcEnd K r (invDarts X K.sourceArc.darts)

/-- **The Jordan arc-end statement from a loop-run or pinned class.** -/
theorem extremalJordanReroute_extremalJordan (h : ExtremalJordanRerouteStatement.{u, w, v}) :
    ExtremalJordanStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hc, hp, hT, hS⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  rcases hp with hp | hp
  · exact ⟨r, hc, extremalJordanReroute_linked_of_loopRun K hK r hp, hT, hS⟩
  · exact ⟨r, hc, extremalArcEndExists_linked_of_pinned K hK r hp, hT, hS⟩

/-- **Chain consequence**: the relative Greendlinger statement from the four-piece-off
statement and the reroute statement. -/
theorem extremalJordanReroute_relativeGreendlinger
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : ExtremalJordanRerouteStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  extremalJordan_relativeGreendlinger hoff (extremalJordanReroute_extremalJordan h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanReroute_loopRun_of_oneRun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanRerouteStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanReroute_extremalJordan
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanReroute_relativeGreendlinger
