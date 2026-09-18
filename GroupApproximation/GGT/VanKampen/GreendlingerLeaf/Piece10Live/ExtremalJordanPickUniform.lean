import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickStep
import GroupApproximation.Meta.AxiomGuard

/-!
# The uniform step outside the loop-only case

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-36.

**LOUD: the target `ExtremalJordanPickStepUniformStatement` (`Piece10Live/ExtremalJordanPickStep`,
lane gl-p10-33) is NOT closed outright here.**  It is reduced to ONE open Statement,
`ExtremalJordanPickUniformStatement`, by `extremalJordanPickUniform_step_of_loopFree`.  The
Statement is the target with one more hypothesis, so it is logically STRICTLY WEAKER.

## Proof route

Call a class `r` *loop-only* (`ExtremalJordanPickUniformLoops K r`) when every walk dart it
removes is a loop.  Then every dart of `ExtremalJordanPickWalk K r` is kept
(`extremalJordanPickUniform_walk_kept`): the walk deletes exactly the removed loops.  So no
consecutive pair changes kind, and `ExtremalJordanPickChanges K r = 0`
(`extremalJordanPickUniform_changes_of_loops`).  The endpoint splits on whether a loop-only
uniform choice class exists:

* if one does, it is the witness of the target, with `0 ≤ 2` changes;
* if none does, the Statement gives the witness.

Two proved helpers give uniform choice classes from region data.  They are not needed by the
endpoint, but they discharge the choice and uniform clauses for the witnesses the model finds:

* `extremalJordanPickUniform_of_region`: a region class (`ExtremalJordanPickPoolRegion`, lane
  gl-p10-34) is a uniform choice class that keeps every arc dart;
* `extremalJordanPickUniform_of_arcClass`: the class of the only dart `e` of a one-dart arc is
  a uniform choice class (`ExtremalJordanPickUniformArcClass`) when it keeps the other arc and
  avoids a cell of `K.faces`.  It removes the arc `[e]`, since `e` lies in its own class
  (`extremalJordanPickUniform_self_removed`).

The *monogon* case (a one-dart arc `[e]`, `e` a loop, and `e` the only walk dart its class
removes) is loop-only and an arc class (`extremalJordanPickUniform_loops_of_monogon`,
`extremalJordanPickUniform_arcClass_of_monogon`; the second uses the disjointness of the two
arcs on the walk, `extremalJordanPickUniform_ne_of_mem`).  Every 6-dart failure of the region
form is a monogon.

## LOUD: the global moves are FALSE

The lane suggested a global descent: take a uniform choice class with the fewest changes, and
from four or more changes produce a uniform choice class with fewer.  Every relation tested
between the old class `Z` and the new class `Z'` FAILS at 6 darts, every vertex degree (script
`gl-p10-36/e4.py`, outputs `e4_6_*.out`; 217,476 uniform choice classes with at least four
changes).  A walk instance lists the vertex of each dart, then the (inside, outside) region pair
of each dart.

* **Touch** (`Z'` meets a kept dart of `Z`): 840 failures, e.g. vertices `[0,2,1,2,1,2]`,
  regions `[(0,1),(0,1),(2,3),(0,3),(0,4),(2,4)]`, target arc `[5]`, `RS = 3`, `RE = 4`,
  `Z = 0`.  The only better class is the digon `1` across the removed run of `Z`.
* **Nested** (every walk dart met by `Z'` is kept by `Z`): 12,624 failures.
* **One gap** (every walk dart met by `Z'` lies in one kept run of `Z`): 32,820 failures.
* **Across** (`Z'` meets a removed dart of `Z`): 60,876 failures.

The pool-free gap lemma ("in every kept run of a class with more than two changes, some dart
has a side class with at most two changes") is FALSE too (script `e2.py`: 5 failures at 5 darts,
156 at 6 darts), e.g. vertices `[0,1,0,1,1]`, regions `[(0,1),(2,1),(2,3),(0,3),(2,4)]`,
`Z = 0`, kept run `[1,2]`.  A window lemma on closed sub-walks (script `e5.py`) fails on rose
crossings.  So no descent rule is isolated here.

## LOUD: two direct constructions are FALSE

Script `e6.py` / `e7.py`, darts 6 (every degree) and 7, 8 (degree at most 3):

* **Region or monogon** ("some region class has at most two changes, or some arc is a monogon
  `[e]`"): true at 6 darts, FALSE at 7 darts (84 instances) and 8 darts (1,696 instances), e.g.
  vertices `[1,2,1,0,1,2,2]`, regions `[(0,1),(2,1),(2,3),(4,1),(4,1),(0,3),(2,5)]`, reversed
  source arc `[3]`, target arc `[6]`, `RS = 1`, `RE = 5`.  The witness is the class `2` of the
  loop `6`, which also removes the non-loop run `[1,2]`.
* **Region or one-dart arc class** ("some region class, or the class of the only dart of a
  one-dart arc, has at most two changes"): true at 6 and 7 darts, FALSE at 8 darts (320
  instances), e.g. vertices `[1,3,1,0,1,3,2,3]`, regions
  `[(0,1),(2,1),(2,3),(4,1),(4,1),(0,3),(2,5),(2,5)]`, reversed source arc `[3,4]`, target arc
  `[6,7]`, `RS = 1`, `RE = 5`.  **This corrects the docstring of `ExtremalJordanPickStep`**:
  there, the witnesses outside the region form are said to have one-dart arcs; at 8 darts some
  need a removed arc of two darts.

So a uniform witness that removes a whole arc of several darts is needed, and the target's
uniform form cannot be narrowed to region classes and one-dart arcs.

## LOUD: logical strength of the gap

`ExtremalJordanPickUniformStatement` is the target with the extra hypothesis "no uniform choice
class is loop-only".  So it is implied by the target, and logically STRICTLY WEAKER: the model
instances with a loop-only uniform choice class satisfy the target and fall outside the
Statement.  They are most instances (table below), so the Statement is also strictly smaller in
proof content.  It is not an equivalent restatement, and it is none of the refuted forms: no
pick rule, no local surgery, no region form and no descent relation.

## Truth check (model)

Model of lanes gl-p10-17/27/30/33 (pocket walk, arcs, source and exterior regions, choice
classes).  Script `gl-p10-36/e8.py`: among the instances with a pool class, those with a
loop-only uniform choice class are closed by the endpoint.  The rest are the gap, and each of
them has a uniform choice class with at most two changes (the target, lane gl-p10-33
`uni.py`).  No failure.

| darts | vertex degree | instances | loop-only (proved) | gap (Statement holds) |
|-------|---------------|-----------|--------------------|-----------------------|
| 4     | any           | 7,852     | 7,620              | 232                   |
| 5     | any           | 220,700   | 217,510            | 3,190                 |
| 6     | any           | 6,489,102 | 6,435,222          | 53,880                |
| 7     | at most 3     | 751,422   | 595,756            | 155,666               |
| 8     | at most 3     | 5,024,192 | 4,086,256          | 937,936               |

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section PickUniform

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A dart is removed by its own class.** -/
theorem extremalJordanPickUniform_self_removed (K : PocketFaceSet D eps X lo hi)
    (e : X.toCombMap.Dart) : P10ExtremalResidual.keptPred K e e = false := by
  cases hk : P10ExtremalResidual.keptPred K e e with
  | false => rfl
  | true =>
      have hself : regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) e e = true :=
        (P10Rose.SubArcMove.regionColour_eq_true_iff X.toCombMap _ e e).mpr
          (Relation.EqvGen.refl e)
      have hfalse := ((P10Rose.FilterMove.movePred_eq_true_iff X.toCombMap
        (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) e) e).mp hk).1
      exact absurd (hself.symm.trans hfalse) (by decide)

/-- **The two arcs are disjoint on the walk**: a dart of the reversed source arc is not a dart
of the target arc, since the walk has no repeated dart. -/
theorem extremalJordanPickUniform_ne_of_mem (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart} (hx : x ∈ invDarts X K.sourceArc.darts)
    (hy : y ∈ K.targetArc.darts) : x ≠ y := by
  have hnd := K.boundary.cycle_nodup
  rw [K.decomposition] at hnd
  exact (List.nodup_append.mp hnd).2.2 x
    (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx)))) y hy

/-- **A loop-only class**: every walk dart the class removes is a loop. -/
def ExtremalJordanPickUniformLoops (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) :
    Prop :=
  ∀ x ∈ K.boundary.cycle, P10ExtremalResidual.keptPred K r x = false →
    X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x)

/-- **A loop-only class keeps every dart of its filtered walk.** -/
theorem extremalJordanPickUniform_walk_kept (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} (hloop : ExtremalJordanPickUniformLoops K r) :
    ∀ x ∈ ExtremalJordanPickWalk K r, P10ExtremalResidual.keptPred K r x = true := by
  intro x hx
  unfold ExtremalJordanPickWalk at hx
  obtain ⟨hxc, hpx⟩ := List.mem_filter.mp hx
  cases hk : P10ExtremalResidual.keptPred K r x with
  | true => rfl
  | false => simp [hk, hloop x hxc hk] at hpx

/-- **No kind change on an all-kept walk.** -/
theorem extremalJordanPickUniform_changes_eq_zero (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart)
    (hall : ∀ x ∈ ExtremalJordanPickWalk K r, P10ExtremalResidual.keptPred K r x = true) :
    ExtremalJordanPickChanges K r = 0 := by
  unfold ExtremalJordanPickChanges
  refine List.countP_eq_zero.mpr ?_
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb⟩ := List.of_mem_zip hab
  have h₁ := hall a ha
  have h₂ := hall b (List.mem_rotate.mp hb)
  show ¬(P10ExtremalResidual.keptPred K r a != P10ExtremalResidual.keptPred K r b) = true
  rw [h₁, h₂]
  decide

/-- **A loop-only class has no kind change.** -/
theorem extremalJordanPickUniform_changes_of_loops (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} (hloop : ExtremalJordanPickUniformLoops K r) :
    ExtremalJordanPickChanges K r = 0 :=
  extremalJordanPickUniform_changes_eq_zero K r (extremalJordanPickUniform_walk_kept K hloop)

/-- **A region class is a uniform choice class** keeping every arc dart. -/
theorem extremalJordanPickUniform_of_region (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} (h : ExtremalJordanPickPoolRegion K r) :
    ExtremalJordanPickStepUniform K r := by
  refine ⟨(extremalJordanPickPool_of_region K h).1, Or.inl fun x hx => ?_,
    Or.inl fun x hx => ?_⟩
  · rcases h with ⟨hr, hO, -⟩ | ⟨hr, -, harc⟩
    · exact extremalJordanPickPool_kept K r x
        (fun hrx => hr ((extremalJordanPickPool_mem_faces_iff K hrx).mpr
          (extremalJordanPickPool_face_mem_of_cycle K
            (extremalJordanPickPool_mem_cycle_of_target K hx))))
        (hO _ (P10Rose.FilterMove.faceOf_alpha_of_mem_targetArc K hx))
    · refine extremalJordanPickPool_kept K r x (harc x (List.mem_append_left _ hx))
        fun hrx => ?_
      have h₁ := (extremalJordanPickPool_mem_faces_iff K hrx).mp hr
      rw [P10Rose.FilterMove.faceOf_alpha_of_mem_targetArc K hx] at h₁
      exact K.outerFace_not_mem h₁
  · rcases h with ⟨hr, -, hS⟩ | ⟨hr, -, harc⟩
    · exact extremalJordanPickPool_kept K r x
        (fun hrx => hr ((extremalJordanPickPool_mem_faces_iff K hrx).mpr
          (extremalJordanPickPool_face_mem_of_cycle K
            (extremalJordanPickPool_mem_cycle_of_invSource K hx))))
        (hS _ (P10Rose.FilterMove.faceOf_alpha_of_mem_invSourceArc K hx))
    · refine extremalJordanPickPool_kept K r x (harc x (List.mem_append_right _ hx))
        fun hrx => ?_
      have h₁ := (extremalJordanPickPool_mem_faces_iff K hrx).mp hr
      rw [P10Rose.FilterMove.faceOf_alpha_of_mem_invSourceArc K hx] at h₁
      exact K.source_not_mem h₁
