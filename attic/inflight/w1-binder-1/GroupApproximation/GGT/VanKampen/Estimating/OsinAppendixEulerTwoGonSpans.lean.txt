import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonFaceClass
import GroupApproximation.Meta.AxiomGuard

/-!
# The spans of a two-gon pocket walk hold the arcs of its regions

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3.  The pocket walk
`source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` of a two-gon between exterior
regions `a` and `b` of one cell has a source span on the cell and a target span on `∂Δ`.  The walk
hypotheses `twoGonWalk_left_side`, `twoGonWalk_right_side` and `twoGonWalk_base`
(`Estimating/OsinAppendixEulerTwoGonClassHyp`) ask that the source span holds the source arcs of
`a` and `b` and the target span their target arcs.  This module derives these inclusions from the
span data of `CyclicArc.exists_spanArc` and of the section positions.

* `twoGonSource_left`, `twoGonSource_right`: the source span `a.sourceArc ++ gap ++ b.sourceArc`
  holds both source arcs.
* `mem_darts_of_start_eq_of_eq_none`, `twoGonTarget_left`: a target span starting where the target
  arc of `a` starts, and at least as long, holds it.  The target arc of a region with a boundary
  target lives on `targetDarts Delta a.target`, which is the outer carrier only after
  `a.target = none`.
* `mem_darts_of_le_of_eq_none`, `twoGonTarget_right`: a target span ending where the target arc of
  `b` ends, starting no later and not wrapping, holds it.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace Embedded.RegionCandidate

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-- An arc on the target carrier of a boundary target, starting where a longer arc of the outer
carrier starts, lies in that arc. -/
theorem mem_darts_of_start_eq_of_eq_none {t : Option (Fin Delta.rCellCount)} (ht : t = none)
    (X : CyclicArc (targetDarts Delta t)) (Y : CyclicArc (targetDarts Delta none))
    (hs : Y.start.1 = X.start.1) (hl : X.length ≤ Y.length) {d : Delta.toCombMap.Dart}
    (hd : d ∈ X.darts) : d ∈ Y.darts := by
  subst ht
  exact (CyclicArc.darts_prefix_of_start_eq X Y hs.symm hl).sublist.subset hd

/-- An arc on the target carrier of a boundary target, between the ends of an arc of the outer
carrier that does not wrap around, lies in that arc. -/
theorem mem_darts_of_le_of_eq_none {t : Option (Fin Delta.rCellCount)} (ht : t = none)
    (X : CyclicArc (targetDarts Delta t)) (Y : CyclicArc (targetDarts Delta none))
    (hs : Y.start.1 ≤ X.start.1) (he : X.start.1 + X.length ≤ Y.start.1 + Y.length)
    (hY : Y.start.1 + Y.length ≤ (targetDarts Delta none).length) {d : Delta.toCombMap.Dart}
    (hd : d ∈ X.darts) : d ∈ Y.darts := by
  subst ht
  exact CyclicArc.mem_darts_of_le X Y hs he hY hd

/-- **The source span holds the source arc of `a`.** -/
theorem twoGonSource_left {a b : RegionCandidate D eps Delta} {i : Fin Delta.rCellCount}
    (source : CyclicArc (cellDarts Delta i)) {gap : List Delta.toCombMap.Dart}
    (hgap : source.darts = a.2.sourceArc.darts ++ gap ++ b.2.sourceArc.darts) :
    ∀ d ∈ a.2.sourceArc.darts, d ∈ source.darts := by
  intro d hd
  rw [hgap]
  exact List.mem_append_left _ (List.mem_append_left _ hd)

/-- **The source span holds the source arc of `b`.** -/
theorem twoGonSource_right {a b : RegionCandidate D eps Delta} {i : Fin Delta.rCellCount}
    (source : CyclicArc (cellDarts Delta i)) {gap : List Delta.toCombMap.Dart}
    (hgap : source.darts = a.2.sourceArc.darts ++ gap ++ b.2.sourceArc.darts) :
    ∀ d ∈ b.2.sourceArc.darts, d ∈ source.darts := by
  intro d hd
  rw [hgap]
  exact List.mem_append_right _ hd

/-- **The target span holds the target arc of `a`**: it starts where that arc starts and is at
least as long. -/
theorem twoGonTarget_left {a : RegionCandidate D eps Delta} (ht : a.2.target = none)
    (target : CyclicArc (targetDarts Delta none))
    (hstart : target.start.1 = a.2.targetArc.start.1)
    (hlen : a.2.targetArc.length ≤ target.length) :
    ∀ d ∈ a.2.targetArc.darts, d ∈ target.darts :=
  fun _ hd => mem_darts_of_start_eq_of_eq_none ht a.2.targetArc target hstart hlen hd

/-- **The target span holds the target arc of `b`**: it ends where that arc ends, starts no
later, and does not wrap around. -/
theorem twoGonTarget_right {b : RegionCandidate D eps Delta} (ht : b.2.target = none)
    (target : CyclicArc (targetDarts Delta none))
    (hs : target.start.1 ≤ b.2.targetArc.start.1)
    (hend : target.start.1 + target.length = b.2.targetArc.start.1 + b.2.targetArc.length)
    (hY : target.start.1 + target.length ≤ (targetDarts Delta none).length) :
    ∀ d ∈ b.2.targetArc.darts, d ∈ target.darts :=
  fun _ hd => mem_darts_of_le_of_eq_none ht b.2.targetArc target hs (by omega) hY hd

end Embedded.RegionCandidate

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.mem_darts_of_start_eq_of_eq_none
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.mem_darts_of_le_of_eq_none
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.twoGonSource_left
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.twoGonSource_right
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.twoGonTarget_left
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.twoGonTarget_right
