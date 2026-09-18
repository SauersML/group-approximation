import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickPool
import GroupApproximation.Meta.AxiomGuard

/-!
# The descent in the kind changes from a uniform class with at most two changes

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-33.

**LOUD: clause (b1) of `ExtremalJordanPickRunStatement` (`Piece10Live/ExtremalJordanPickRun`,
lane gl-p10-32), `ExtremalJordanPickRunDescent K`, is NOT closed outright here.**  It is reduced
to ONE open Statement, `ExtremalJordanPickStepUniformStatement`, by
`extremalJordanPickStep_descent` (clause (a) as a hypothesis).

## LOUD: every one-step local surgery is FALSE

The lane asked for a concrete one-step surgery that lowers `ExtremalJordanPickChanges`.  Every
local rule tried is FALSE in the model of lanes gl-p10-17/27/30/31/32 (pocket walk, arcs, source
and exterior regions).  A walk instance below lists the vertex of each dart, then the (inside,
outside) region pair of each dart; `Z` is the class, `RS`/`RE` the source and exterior regions.

* **The class across a removed dart at a change** (the side region of the removed dart next to a
  kept one): fails at 5 darts, vertices `[0,0,1,1,1]`, regions
  `[(0,1),(2,1),(0,1),(3,1),(4,1)]`, target arc `[4]`, source arc empty, `RS = RE = 1`, `Z = 0`.
* **The class of the kept dart `g` of a removed→kept pair `(p, g)` of the cyclic walk** (the
  statement "`Pool K g` and `Changes K g < Changes K r`"): true at 5 darts, FALSE at 6 darts
  (2,260 + 4,424 instances fail the pool clause, 46,446 + 55,350 fail the decrease).  Decrease
  counterexample: vertices `[0,1,1,0,1,1]`, regions `[(0,1),(2,1),(3,4),(2,5),(0,5),(2,4)]`,
  target arc `[5]`, `RS = 1`, `RE = 4`, `Z = 0`, `g = 1`: the class `2` of `g` also has 4 changes.
  Pool counterexample: a monogon in the middle of the source arc breaks the arc-end clause.
* **Exact decrease by two** is FALSE: a step from 4 changes to 0 occurs, so no "`Changes - 2`"
  form of the step holds.
* **Gap rules** (every / some / the shortest removed gap, a dart of it on the same side, the
  opposite side or either side, gap starts, gap ends): all FALSE at 6 darts, e.g. vertices
  `[0,2,1,2,1,2]`, regions `[(0,1),(0,1),(2,3),(0,3),(0,4),(2,4)]`, target arc `[4,5]`,
  `RS = 3`, `RE = 4`, `Z = 0`: the only better class is the digon `1` across the removed run of
  `Z`, and the regions inside the gap are `RS` and `RE`, which the choice clause excludes.
* **Fixed walk positions** (first dart, first dart of an arc, a fixed side): FALSE at 5 darts.

Pool-free, the gap rule is TRUE (every class with more than two changes has, in every gap, a
dart whose side region has at most two changes: 414/414 at 6 darts, 812/812 at 7 darts of degree
at most 3); the pool constraints (the choice clause excluding `RS`/`RE`, and the arc-end clause)
are what break locality.  So no local step is isolated; the Statement below is global.

## The split

By `extremalJordanPickRun_descent_of_exists_le_two` (lane gl-p10-32, PROVED), (b1) for `K`
follows from one pool class with at most two changes.  By `extremalJordanPickStep_pool_of_uniform`
(PROVED here, from `extremalJordan_arcEnd_of_uniform`), a choice class that keeps every dart or
removes every dart of each arc (`ExtremalJordanPickStepUniform`) is a pool class.  So the
Statement asks for a UNIFORM choice class with at most two changes, given that some pool class
exists (clause (a), a hypothesis): the arc-end split points (`ExtremalJordanArcEnd`: `pre`,
`post` and the side of the split) no longer have to be found.

## LOUD: the region form is FALSE

The stronger form "some region class (`ExtremalJordanPickPoolRegion`, lane gl-p10-34) has at most
two changes" is FALSE: 24 failures at 6 darts (of 6,489,102 instances), 476 at 7 darts of degree
at most 3, e.g. vertices `[0,1,0,0,1,1]`, regions `[(0,1),(0,2),(3,2),(0,4),(3,1),(5,2)]`,
reversed source arc `[3]`, target arc `[5]`, `RS = 4`, `RE = 2`: the only classes with at most two
changes are inside classes meeting an arc dart.  Those arcs have one dart, so the uniform form
survives; the Statement uses the weaker uniform form.

## LOUD: logical strength of the gap

Under (a), (b1) is equivalent to "some pool class has at most two changes"
(`extremalJordanPickRun_descent_of_exists_le_two`,
`extremalJordanPickRun_exists_le_two_of_descent`).  `ExtremalJordanPickStepUniformStatement` is
logically STRONGER than that: a uniform choice class is a pool class, and the converse is not
claimed (an arc met through one end need not be uniform).  It is strictly smaller in proof
content, since no arc-end split is produced.  It is not an equivalent
restatement of (b1), and it is not the rejected minimal-count, arc-end-surgery or shape-pool rule
(it picks nothing; it asks for existence only).

## Truth check (model)

Exact Lean form, script `gl-p10-33/uni.py`: whenever a pool class exists, some choice class that
is uniform on the target arc and on the reversed source arc has at most two changes.

| darts | vertex degree | instances | uniform class with at most two changes |
|-------|---------------|-----------|----------------------------------------|
| 3     | any           | 204       | 204                                    |
| 4     | any           | 7,852     | 7,852                                  |
| 5     | any           | 220,700   | 220,700                                |
| 6     | any           | 6,489,102 | 6,489,102                              |
| 7     | at most 3     | 751,422   | 751,422                                |
| 8     | at most 3     | N8        | N8U                                    |

Every instance had a pool class.  The 7-dart run of lane gl-p10-31, every degree
(`gl-p10-31/s7_*.out`, 215,705,028 instances), found no pool failure and no instance whose least
pool class has four or more changes, so (a) and (b1) themselves hold there.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section PickStep

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A uniform choice class**: a choice class (`ExtremalClassChoice`) that keeps every dart or
removes every dart of each arc (`ExtremalMinimalArcUniform`). -/
def ExtremalJordanPickStepUniform (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) :
    Prop :=
  ExtremalClassChoice K r ∧ ExtremalMinimalArcUniform K r K.targetArc.darts ∧
    ExtremalMinimalArcUniform K r (invDarts X K.sourceArc.darts)

/-- **A uniform choice class is a pool class**: a uniform arc is met through one end
(`extremalJordan_arcEnd_of_uniform`). -/
theorem extremalJordanPickStep_pool_of_uniform (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} (h : ExtremalJordanPickStepUniform K r) :
    ExtremalJordanPickPool K r :=
  ⟨h.1, extremalJordan_arcEnd_of_uniform K r K.targetArc.darts h.2.1,
    extremalJordan_arcEnd_of_uniform K r (invDarts X K.sourceArc.darts) h.2.2⟩

end PickStep

/-- **OPEN (lane gl-p10-33).**  Under the premises of `ExtremalJordanStatement`, if some pool
class exists (clause (a)), then some uniform choice class has at most two kind changes up to
removed loops.  LOUD: logically STRONGER than clause (b1) of `ExtremalJordanPickRunStatement`
under (a) (`extremalJordanPickStep_descent`), strictly smaller in proof content; true in the
model (see the module docstring). -/
def ExtremalJordanPickStepUniformStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      (∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r) →
        ∃ r : X.toCombMap.Dart, ExtremalJordanPickStepUniform K r ∧
          ExtremalJordanPickChanges K r ≤ 2

/-- **Clause (a) of `ExtremalJordanPickRunStatement`**, as an interface: under the premises of
`ExtremalJordanStatement`, some pool class exists.  Lane gl-p10-34 reduces it to
`ExtremalJordanPickPoolRegionStatement` (`extremalJordanPickPool_exists`). -/
def ExtremalJordanPickStepPoolStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r

section PickStepDescent

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A pool class with at most two changes** from the uniform statement and clause (a). -/
theorem extremalJordanPickStep_exists_le_two
    (hstep : ExtremalJordanPickStepUniformStatement.{u, w, v})
    (hwrap : hi ≤ (outerDarts X).length) (hlea : X.LeastArea)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk) (hnft : ¬ K.FirstTurns)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (hpinch : ¬Unpinched X.toCombMap K.faces) (hrose : P10ChordLift.AllNonFirstTurnsCrossed K)
    (hex : ∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r) :
    ∃ r₀ : X.toCombMap.Dart, ExtremalJordanPickPool K r₀ ∧
      ExtremalJordanPickChanges K r₀ ≤ 2 := by
  obtain ⟨r, hr, hle⟩ :=
    hstep D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hex
  exact ⟨r, extremalJordanPickStep_pool_of_uniform K hr, hle⟩

/-- **(b1) from the uniform statement**: under the premises of `ExtremalJordanStatement` and
clause (a), `ExtremalJordanPickRunDescent K` holds. -/
theorem extremalJordanPickStep_descent
    (hstep : ExtremalJordanPickStepUniformStatement.{u, w, v})
    (hwrap : hi ≤ (outerDarts X).length) (hlea : X.LeastArea)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk) (hnft : ¬ K.FirstTurns)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (hpinch : ¬Unpinched X.toCombMap K.faces) (hrose : P10ChordLift.AllNonFirstTurnsCrossed K)
    (hex : ∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r) :
    ExtremalJordanPickRunDescent K :=
  extremalJordanPickRun_descent_of_exists_le_two K
    (extremalJordanPickStep_exists_le_two hstep hwrap hlea hlabel K hK hnft hsrc htgt hpinch
      hrose hex)

end PickStepDescent

/-- **The wire, (a) as a hypothesis**: clause (a) and the uniform statement give
`ExtremalJordanPickRunStatement`. -/
theorem extremalJordanPickStep_extremalJordanPickRun
    (ha : ExtremalJordanPickStepPoolStatement.{u, w, v})
    (hstep : ExtremalJordanPickStepUniformStatement.{u, w, v}) :
    ExtremalJordanPickRunStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hex := ha D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨hex,
    extremalJordanPickStep_descent hstep hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hex⟩

/-- **The wire, (a) from the region statement of lane gl-p10-34**:
`ExtremalJordanPickPoolRegionStatement` and the uniform statement give
`ExtremalJordanPickRunStatement`. -/
theorem extremalJordanPickStep_extremalJordanPickRun_of_region
    (hreg : ExtremalJordanPickPoolRegionStatement.{u, w, v})
    (hstep : ExtremalJordanPickStepUniformStatement.{u, w, v}) :
    ExtremalJordanPickRunStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hex := extremalJordanPickPool_exists hreg hwrap hlea hlabel K hK hnft hsrc htgt hpinch
    hrose
  exact ⟨hex,
    extremalJordanPickStep_descent hstep hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hex⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickStepUniform
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickStep_pool_of_uniform
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickStepUniformStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickStepPoolStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickStep_exists_le_two
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickStep_descent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickStep_extremalJordanPickRun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickStep_extremalJordanPickRun_of_region
