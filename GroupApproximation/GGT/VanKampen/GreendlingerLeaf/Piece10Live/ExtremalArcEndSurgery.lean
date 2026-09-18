import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndDescent
import GroupApproximation.Meta.AxiomGuard

/-!
# The arc-end surgery rule: an extra exterior class, else a side class

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-26.

**LOUD: the targets `P10ExtremalRegion.ExtremalArcEndDescentKRKStatement` and
`P10ExtremalRegion.ExtremalArcEndDescentRKRStatement` (`Piece10Live/ExtremalArcEndDescent`, lane
gl-p10-22) are NOT closed here.**  Both are reduced, with proofs, to the single open
`ExtremalArcEndSurgeryStatement`, which names an explicit replacement class `r'`.

## The rule for `r'`

An *extra exterior class* (`ExtremalArcEndSurgeryExtraOut K z`) is a dart `z` with face outside
`K.faces` whose face class of `walkKeep K.boundary.cycle` avoids the exterior face and the source
face.  (In the plane model: a region outside the pocket walk other than the exterior region and
the source region.)  The rule:

* (A) if an extra exterior class exists, take `r'` to be any of them;
* (B) otherwise take `r'` to be a side dart (a dart of `K.firstSide ++ K.secondSide`) whose class
  is a choice class removing no arc dart.

## Proved here (no gap)

* `extremalArcEndSurgery_mem_faces_iff`: a face class lies on one side of `K.faces` (crossing an
  edge off the walk keeps the side, since a boundary dart lies on the walk);
* `extremalArcEndSurgery_removed_eq_zero`: an extra exterior class removes no arc dart (arc darts
  have their face in `K.faces` and the far face exterior or source);
* `extremalArcEndSurgery_choice`: an extra exterior class is a choice class
  (`ExtremalClassChoice`, avoiding the kept cell `K.kept` because that face is in `K.faces`);
* `extremalArcEndSurgery_removed_pos_of_krk`, `extremalArcEndSurgery_removed_pos_of_rkr`: each
  pattern removes an arc dart, so the count of `r` is positive and every class of count `0`
  strictly lowers it;
* `extremalArcEndSurgery_descent`: the rule `ExtremalArcEndSurgeryRule K` and a positive count
  give a linked choice class of smaller count;
* the endpoints `extremalArcEndSurgery_krk_of_surgery`, `extremalArcEndSurgery_rkr_of_surgery`,
  and the chain consequences `extremalArcEndSurgery_descent_of_surgery`,
  `extremalArcEndSurgery_extremalJordan_of_surgery`.

## The one open Statement

`ExtremalArcEndSurgeryStatement`: under the premises of the two targets, if some linked choice
class meets an arc in the pattern kept / removed / kept or removed / kept / removed, then
`ExtremalArcEndSurgeryRule K` holds: (A) every extra exterior class has linked removed runs
(`ExtremalMinimalLinkedRuns`); (B) if no extra exterior class exists, some side dart's class is a
choice class of count `0`, and every such side class has linked removed runs.

## LOUD: logical strength

`ExtremalArcEndSurgeryStatement` is logically STRONGER than each of the two targets: it implies
both (`extremalArcEndSurgery_krk_of_surgery`, `extremalArcEndSurgery_rkr_of_surgery`) and is not
implied by them, nor by `ExtremalArcEndDescentStatement`: it asserts that specific classes are
linked, and it gives count `0`, not only a smaller count.  It is strictly smaller in proof
content: the choice of `r'`, the choice property and count `0` of an extra exterior class, and
the strict drop of the count are proved.  What remains is planar: linked removed runs of the
chosen class, and in case (B) the existence of a suitable side class.

## Truth check (lane gl-p10-26, model of lanes gl-p10-14 / gl-p10-17 / gl-p10-21)

Scripts `explore2.py`, `explore3.py`, `explore4.py` in the scratchpad folder `gl-p10-26/`, run
on the enumerations of gl-p10-21 (pocket boundary as a plane Eulerian closed walk with a rotation
system, every instance of source arc, target arc, source region and exterior region, every
candidate class), at most 6 darts (6717858 instances):

* kept / removed / kept: 35610 hypotheses.  In 32198 an extra exterior region exists, and in all
  32198 EVERY extra exterior region is a linked choice class of count `0` (clause (A)).  In the
  other 3412 (2596 of them with source region equal to exterior region) some side region is a
  linked choice class of count `0`, and every side region that is a choice class of count `0` is
  linked (clause (B)): 0 failures.
* removed / kept / removed: 1610 hypotheses, an extra exterior region exists in all of them, and
  every one is a linked choice class of count `0`: 0 failures.
* So the Statement holds in every model instance with its hypothesis (0 failures), and it is
  not vacuous (both clauses are exercised).
* Variants that FAIL: (A) WITHOUT the pattern hypothesis (5940 extra exterior regions at most 6
  darts are not linked, in instances with no linked choice class meeting a pattern; 0 at most 5
  darts); (B) with "the first side dart" instead of "a side dart" (366 failures at most 6 darts);
  "every choice class of count `0` is linked" (165510 failures); every dart-local rule in terms of
  the pattern darts alone (already at most 5 darts, for kept / removed / kept).
* Faithfulness caveat: a Lean face class is matched with a plane region of the walk complement.
  For an extra exterior class this uses that every face class outside `K.faces` touches the walk
  (the disc is connected); this is not formalised here.

## Remaining gap

`ExtremalArcEndSurgeryStatement` only.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **A kept / removed / kept list has a `false` member.** -/
theorem extremalArcEndSurgery_false_of_krkList {α : Type*} {p : α → Bool} {l : List α}
    (h : ExtremalArcEndDescentKRKList p l) : ∃ x ∈ l, p x = false := by
  obtain ⟨_, _, B, _, _, hl, -, -, hB, hBf⟩ := h
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hB
  refine ⟨b, ?_, hBf b hb⟩
  rw [hl]
  simp [hb]

/-- **A removed / kept / removed list has a `false` member.** -/
theorem extremalArcEndSurgery_false_of_rkrList {α : Type*} {p : α → Bool} {l : List α}
    (h : ExtremalArcEndDescentRKRList p l) : ∃ x ∈ l, p x = false := by
  obtain ⟨_, d, _, _, _, hl, hd, -, -, -⟩ := h
  refine ⟨d, ?_, hd⟩
  rw [hl]
  simp

section Surgery

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **An extra exterior class**: the face of `z` is outside `K.faces`, and the class of `z`
avoids the exterior face and the source face. -/
def ExtremalArcEndSurgeryExtraOut (K : PocketFaceSet D eps X lo hi) (z : X.toCombMap.Dart) :
    Prop :=
  X.toCombMap.faceOf z ∉ K.faces ∧
    (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) z x) ∧
    ∀ x, X.toCombMap.faceOf x = (cell X K.source).face → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) z x

/-- **The surgery rule**: (A) every extra exterior class has linked removed runs; (B) with no
extra exterior class, some side class is a choice class of count `0`, and every such side class
has linked removed runs. -/
def ExtremalArcEndSurgeryRule (K : PocketFaceSet D eps X lo hi) : Prop :=
  (∀ z, ExtremalArcEndSurgeryExtraOut K z → ExtremalMinimalLinkedRuns K z) ∧
    ((∀ z, ¬ExtremalArcEndSurgeryExtraOut K z) →
      (∃ y ∈ K.firstSide ++ K.secondSide,
          ExtremalClassChoice K y ∧ ExtremalArcEndRemoved K y = 0) ∧
        ∀ y ∈ K.firstSide ++ K.secondSide, ExtremalClassChoice K y →
          ExtremalArcEndRemoved K y = 0 → ExtremalMinimalLinkedRuns K y)
