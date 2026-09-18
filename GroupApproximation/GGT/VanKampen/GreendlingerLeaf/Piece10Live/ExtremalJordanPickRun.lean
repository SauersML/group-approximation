import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickRunLists
import GroupApproximation.Meta.AxiomGuard

/-!
# The pick statement from a descent in the kind changes

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-32.

**LOUD: the target `ExtremalJordanPickStatement` (`Piece10Live/ExtremalJordanPick`, lane
gl-p10-31) is NOT closed outright here.**  It is reduced to ONE open Statement,
`ExtremalJordanPickRunStatement`, by `extremalJordanPickRun_extremalJordanPick`.

## The split

`ExtremalJordanPickStatement` has two clauses:

* (a) **existence**: some class lies in the arc-good pool (`ExtremalJordanPickPool`);
* (b) **the pick clause**: every pool class of least `ExtremalJordanPickChanges` has one removed
  run up to loops or is pinned.

(b) is split in two:

* (b1) **the rerouting step** (`ExtremalJordanPickRunDescent`): a pool class with more than two
  kind changes can be replaced by a pool class with fewer.  Open, in the Statement.
* (b2) **at most two kind changes give one removed run up to loops**:
  `extremalJordanPickRun_loopRun`, PROVED outright here (no hypothesis on `K`), from the list
  facts of `Piece10Live/ExtremalJordanPickRunLists`: the walk without removed loop darts is one
  cyclic run of each kind, and the deleted removed loop darts are put back as wildcards.

With (b2) and the descent, a pool class of least measure has at most two changes
(`extremalJordanPickRun_pick_of_descent`), so the pinned alternative is not needed.

(a) is NOT proved here: no statement in the corpus produces a choice class
(`ExtremalClassChoice`) at all, let alone one meeting both arcs through one end; that needs the
pocket geometry, so (a) stays in the Statement unchanged.

## LOUD: logical strength of the gap

`ExtremalJordanPickRunStatement` is logically STRONGER than `ExtremalJordanPickStatement` (it
implies it; the converse is not claimed, since the pick statement also allows pinned least
classes of four or more changes).  A logically weaker Statement with a proved reduction would be
equivalent to the target, so no weaker form is possible.  It is strictly smaller in proof
content: the shape conclusion (b2) is proved, and what is left of (b) is the numerical rerouting
step (b1) alone.  Given (a), (b1) is equivalent to "some pool class has at most two changes"
(`extremalJordanPickRun_descent_of_exists_le_two`,
`extremalJordanPickRun_exists_le_two_of_descent`).

`2 < ExtremalJordanPickChanges K r` is used rather than `4 ≤`: in the model the measure is always
even, so the two agree there, and no parity proof is needed here.

Not one of the refuted forms: the measure is the kind changes of lane gl-p10-31 (not removed arc
darts, not runs counting loops), and the pool is the arc-good pool (not the shape pool).

## Truth check (lane gl-p10-32, scratchpad folder `gl-p10-32/`, script `pickrun.py`)

Exact linear Lean forms (`ExtremalJordanPickChanges` as `c'.zip (c'.rotate 1)`), the model of
lanes gl-p10-17/21/27/30/31 (pocket walk, base point, arcs, source and exterior regions), every
choice class:

* 5 darts, every vertex degree (`r5.out`): 220,700 instances, no failure of (a) or (b1); 868,270
  classes with at most two changes, all loop-run classes (b2); 3,150 pool classes with more than
  two changes, all of which descend.
* 6 darts, every vertex degree (`r6.out`): 6,489,102 instances, no failure of (a), (b1) or (b2);
  31,709,682 classes with at most two changes, all loop-run; 250,368 pool classes with more than
  two changes, all of which descend (so (b1) is not vacuous).  The measure is even on every class.
* 8 darts, vertex degree at most 3 (lane gl-p10-31, `pick5.py`, files `gl-p10-31/s8b3_*.out`):
  5,024,192 instances, the pool is never empty and its least measure is never `4` or more, which
  is (a) and (b1) through the equivalence above.
* 7 darts, every vertex degree (`gl-p10-31/s7_*.out`): result PENDING when this file was written.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section PickRun

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **(b2) At most two kind changes give one removed run up to loops.** -/
theorem extremalJordanPickRun_loopRun (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (h : ExtremalJordanPickChanges K r ≤ 2) : ExtremalJordanRerouteLoopRun K r := by
  refine extremalJordanPickRun_loopRun_list (P10ExtremalResidual.keptPred K r) _
    (fun x => X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x))
    K.boundary.cycle ?_ h
  intro x hx
  exact extremalJordanPickRun_wild hx

/-- **(b1) The rerouting step**: every arc-good class with more than two kind changes can be
replaced by an arc-good class with fewer. -/
def ExtremalJordanPickRunDescent (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ r : X.toCombMap.Dart, ExtremalJordanPickPool K r → 2 < ExtremalJordanPickChanges K r →
    ∃ r' : X.toCombMap.Dart, ExtremalJordanPickPool K r' ∧
      ExtremalJordanPickChanges K r' < ExtremalJordanPickChanges K r

/-- **The pick clause from the descent**: a pool class of least measure has at most two kind
changes, so it has one removed run up to loops. -/
theorem extremalJordanPickRun_pick_of_descent (K : PocketFaceSet D eps X lo hi)
    (hdesc : ExtremalJordanPickRunDescent K) (r : X.toCombMap.Dart)
    (hr : ExtremalJordanPickPool K r)
    (hle : ∀ r' : X.toCombMap.Dart, ExtremalJordanPickPool K r' →
      ExtremalJordanPickChanges K r ≤ ExtremalJordanPickChanges K r') :
    ExtremalJordanRerouteLoopRun K r := by
  refine extremalJordanPickRun_loopRun K r ?_
  by_contra hgt
  obtain ⟨r', hr', hlt⟩ := hdesc r hr (by omega)
  have := hle r' hr'
  omega

/-- **The descent from one pool class of at most two kind changes.** -/
theorem extremalJordanPickRun_descent_of_exists_le_two (K : PocketFaceSet D eps X lo hi)
    (h : ∃ r₀ : X.toCombMap.Dart, ExtremalJordanPickPool K r₀ ∧
      ExtremalJordanPickChanges K r₀ ≤ 2) :
    ExtremalJordanPickRunDescent K := by
  intro r _ hr
  obtain ⟨r₀, h₀, h₂⟩ := h
  exact ⟨r₀, h₀, by omega⟩

/-- **A pool class of at most two kind changes from the descent and one pool class.** -/
theorem extremalJordanPickRun_exists_le_two_of_descent (K : PocketFaceSet D eps X lo hi)
    (hdesc : ExtremalJordanPickRunDescent K) (r₀ : X.toCombMap.Dart)
    (h₀ : ExtremalJordanPickPool K r₀) :
    ∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r ∧ ExtremalJordanPickChanges K r ≤ 2 := by
  obtain ⟨r, hr, hle⟩ := extremalJordanPick_exists_min (ExtremalJordanPickPool K)
    (ExtremalJordanPickChanges K) r₀ h₀
  refine ⟨r, hr, ?_⟩
  by_contra hgt
  obtain ⟨r', hr', hlt⟩ := hdesc r hr (by omega)
  have := hle r' hr'
  omega

end PickRun

/-- **OPEN (lane gl-p10-32).**  Under the premises of `ExtremalJordanStatement`: (a) some choice
class meets both arcs through one end, and (b1) every such class with more than two kind changes
up to removed loops can be replaced by one with fewer.  LOUD: logically STRONGER than
`ExtremalJordanPickStatement` (`extremalJordanPickRun_extremalJordanPick`), strictly smaller in
proof content (the shape of a least class is proved, `extremalJordanPickRun_loopRun`); true in
the model at 5 and 6 darts and at 8 darts of degree at most 3 (see the module docstring). -/
def ExtremalJordanPickRunStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        (∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r) ∧ ExtremalJordanPickRunDescent K

/-- **The pick statement from the descent**: every least pool class is a loop-run class. -/
theorem extremalJordanPickRun_extremalJordanPick (h : ExtremalJordanPickRunStatement.{u, w, v}) :
    ExtremalJordanPickStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨hex, hdesc⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨hex, fun r hr hle => Or.inl (extremalJordanPickRun_pick_of_descent K hdesc r hr hle)⟩

/-- **Chain consequence**: the reroute statement from the descent statement. -/
theorem extremalJordanPickRun_extremalJordanReroute
    (h : ExtremalJordanPickRunStatement.{u, w, v}) :
    ExtremalJordanRerouteStatement.{u, w, v} :=
  extremalJordanPick_extremalJordanReroute (extremalJordanPickRun_extremalJordanPick h)

/-- **Chain consequence**: the Jordan arc-end statement from the descent statement. -/
theorem extremalJordanPickRun_extremalJordan (h : ExtremalJordanPickRunStatement.{u, w, v}) :
    ExtremalJordanStatement.{u, w, v} :=
  extremalJordanPick_extremalJordan (extremalJordanPickRun_extremalJordanPick h)

/-- **Chain consequence**: the relative Greendlinger statement from the four-piece-off
statement and the descent statement. -/
theorem extremalJordanPickRun_relativeGreendlinger
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : ExtremalJordanPickRunStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  extremalJordanPick_relativeGreendlinger hoff (extremalJordanPickRun_extremalJordanPick h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_loopRun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickRunDescent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_pick_of_descent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_descent_of_exists_le_two
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_exists_le_two_of_descent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickRunStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_extremalJordanPick
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_extremalJordanReroute
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_extremalJordan
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_relativeGreendlinger
