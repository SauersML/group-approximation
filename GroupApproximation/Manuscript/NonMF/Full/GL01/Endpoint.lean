import GroupApproximation.Manuscript.NonMF.Full.GL01.Triangle
import GroupApproximation.Meta.AxiomGuard

/-!
# GL01: empty two-gons in the contact map (gap-nm L01, GL-EmptyTwoGon)

This is infrastructure for Hull's small cancellation theorem, `thm:hull` in
non_mf_groups_exist.tex.  It enters through the relative Greendlinger lemma (Osin,
arXiv:math/0411039v3, Lemma 4.4), in the step of the proof of Lemma 9.4 that bounds the empty
two-gons of the contact map.  It certifies no printed sentence on its own.

* `emptyTouchTwoGon : EmptyTouchTwoGonStatement` feeds the corner exclusion
  `GL01.touchCornerStatement` (module `GL01.Triangle`) into the foreign reduction
  `P01EmptyTwoGon.touchTwoGon_of_corner` (module `P01EmptyTwoGon.TouchTwoGon`).
* `contactMapEmptyTwoGonInput : OsinLemma94ContactMapEmptyTwoGonInput` then follows from
  `P01EmptyTwoGon.proof_of_touch` (module `P01EmptyTwoGon.Proof`).
-/

namespace GroupApproximation.Full.GL01

universe u w v

/-- **The touch two-gons are empty** (`P01EmptyTwoGon.EmptyTouchTwoGonStatement`, with constant
`0`): in the contact map of a maximal polygon system there is no touch two-gon. -/
theorem emptyTouchTwoGon :
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.EmptyTouchTwoGonStatement.{u, w, v} :=
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.touchTwoGon_of_corner
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.touchCornerStatement.{u, w, v}

/-- **The empty two-gon count of the contact map** (`OsinLemma94ContactMapEmptyTwoGonInput`):
Osin, Lemma 9.4, the empty two-gon step. -/
theorem contactMapEmptyTwoGonInput :
    GroupApproximation.GGT.VanKampen.OsinLemma94ContactMapEmptyTwoGonInput.{u, w, v} :=
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.proof_of_touch
    emptyTouchTwoGon.{u, w, v}

/-- The universe-`0` instance of `contactMapEmptyTwoGonInput`. -/
theorem contactMapEmptyTwoGonInput_zero :
    GroupApproximation.GGT.VanKampen.OsinLemma94ContactMapEmptyTwoGonInput.{0, 0, 0} :=
  contactMapEmptyTwoGonInput.{0, 0, 0}

end GroupApproximation.Full.GL01

#audit_closed_axioms GroupApproximation.Full.GL01.emptyTouchTwoGon
#audit_closed_axioms GroupApproximation.Full.GL01.contactMapEmptyTwoGonInput
#audit_closed_axioms GroupApproximation.Full.GL01.contactMapEmptyTwoGonInput_zero
