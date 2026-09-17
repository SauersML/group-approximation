import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: sub-lists of sides are short

Lane gl-p07-12 (sub-arc and sub-side list tools), infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof
of Lemma 9.7(b).  Certifies no printed sentence on its own; it serves `thm:hull` (tex 2121) via
the Greendlinger leaf.

The outer walk of the filled pocket may skip darts of a far side whose outside face is a lake, so
the side runs of the decomposition are only sub-lists of the sides of the selected regions (lane
notes, *Pitfall: lakes of `L_C`*).  They still have length at most `ε`.

## The mathematical proof

A sub-list `l <+ s` has `|l| ≤ |s|` (`List.Sublist.length_le`).  The side of a region leaving a
cell has `|sideFrom a k| ≤ ε` (`RegionCandidate.sideFrom_length_le`, from `rightSide_length_le`
and `leftSide_length_le`), and the two sides of a pocket walk have length at most `ε` (fields
`firstSide_length_le`, `secondSide_length_le` of `CellPocketWalk`).  An infix is a sub-list
(`List.IsInfix.sublist`).

Truth check: transitivity of `≤`; no hypothesis beyond the sub-list relation.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

/-- **A sub-list of the side of a region leaving a cell has length at most `ε`.** -/
theorem arcSub_sideFrom_sublist_length_le (a : RegionCandidate D eps X) (k : Fin X.rCellCount)
    {l : List X.toCombMap.Dart} (h : l.Sublist (a.sideFrom k)) : l.length ≤ eps :=
  Nat.le_trans h.length_le (a.sideFrom_length_le k)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.arcSub_sideFrom_sublist_length_le

/-- An infix of the side of a region leaving a cell has length at most `ε`. -/
theorem arcSub_sideFrom_infix_length_le (a : RegionCandidate D eps X) (k : Fin X.rCellCount)
    {l : List X.toCombMap.Dart} (h : l <:+: a.sideFrom k) : l.length ≤ eps :=
  arcSub_sideFrom_sublist_length_le a k h.sublist

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.arcSub_sideFrom_infix_length_le

/-- A sub-list of the first side of a pocket walk has length at most `ε`. -/
theorem arcSub_firstSide_sublist_length_le {i j : Fin X.rCellCount}
    (K : CellPocketWalk D eps X i j) {l : List X.toCombMap.Dart} (h : l.Sublist K.firstSide) :
    l.length ≤ eps :=
  Nat.le_trans h.length_le K.firstSide_length_le

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.arcSub_firstSide_sublist_length_le

/-- A sub-list of the second side of a pocket walk has length at most `ε`. -/
theorem arcSub_secondSide_sublist_length_le {i j : Fin X.rCellCount}
    (K : CellPocketWalk D eps X i j) {l : List X.toCombMap.Dart} (h : l.Sublist K.secondSide) :
    l.length ≤ eps :=
  Nat.le_trans h.length_le K.secondSide_length_le

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.arcSub_secondSide_sublist_length_le

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
