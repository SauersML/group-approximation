import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickPool
import GroupApproximation.Meta.AxiomGuard

/-!
# The descent in the kind changes from a region class with at most two changes

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-33.

**LOUD: clause (b1) of `ExtremalJordanPickRunStatement` (`Piece10Live/ExtremalJordanPickRun`,
lane gl-p10-32), `ExtremalJordanPickRunDescent K`, is NOT closed outright here.**  It is reduced
to ONE open Statement, `ExtremalJordanPickStepRegionStatement`, by
`extremalJordanPickStep_descent`.

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
follows from one pool class with at most two changes.  By `extremalJordanPickPool_of_region`
(lane gl-p10-34, PROVED), a region class (`ExtremalJordanPickPoolRegion`: an outside class off
the exterior and source faces, or an inside class off a cell of `K.faces` and off every arc dart)
is a pool class.  So the Statement asks only for a REGION class with at most two changes, given
that some pool class exists (clause (a), a hypothesis): no arc-end, kept-dart or choice-clause
combinatorics remains.

## LOUD: logical strength of the gap

`ExtremalJordanPickStepRegionStatement` is logically STRONGER than (b1) under (a): a region class
is a pool class, the converse is not claimed, and "at most two changes" is stronger than a
decrease.  It is strictly smaller in proof content (the pool clauses are discharged by
`extremalJordanPickPool_of_region`, the descent by `extremalJordanPickRun_descent_of_exists_le_two`).
It is not an equivalent restatement of (b1).

## Truth check (model)

Exact Lean form, script `gl-p10-33/reg.py` (every vertex degree unless noted): whenever a pool
class exists, (A) an outside choice class with at most two changes, or (B) an inside choice class
keeping every arc dart with at most two changes.  See the table in the docstring of
`ExtremalJordanPickStepRegionStatement`.  Neither disjunct can be dropped.  The 7-dart run of
lane gl-p10-31 (`gl-p10-31/s7_*.out`, about 216 million instances) found no pool failure and no
instance whose least pool class has four or more changes.

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

