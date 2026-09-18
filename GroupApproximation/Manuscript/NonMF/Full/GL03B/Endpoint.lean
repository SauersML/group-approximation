import GroupApproximation.Manuscript.NonMF.Full.GL03B.FollowsCase
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Endpoint
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLong
import GroupApproximation.Meta.AxiomGuard

/-!
# GL03B endpoint: the enclosed inner pocket, and the Piece07 lake exclusion

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

* `innerPocketEnclosedTwoArc`: the foreign statement
  `GreendlingerLeaf.P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` holds.  It is the local
  restatement `Full.GL03B.InnerPocketEnclosedTwoArcLocal`, word for word.  That is proved from the
  following case (`Full/GL03B/FollowsCase.lean`) and the pinched case
  (`Full.GL03BPinch.innerPocketEnclosedTwoArcPinched`).
* `cellPocketWalkProperArcsBelowSection`: the Piece07 endpoint
  `CellPocketWalkProperArcsBelowSectionStatement`, by
  `P07LakeExclusion.proof_of_innerPocketEnclosed`.

This file imports `P07LakeExclusion/InnerTwoArcLong.lean`, a WIP snapshot of the foreign swarm, so it
is landed only after that file and the pinched-case lane are clean.
-/

namespace GroupApproximation.Full.GL03B

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **The enclosed inner pocket of a cell pocket walk** (Osin, proof of Lemma 9.7(b); `thm:hull`). -/
theorem innerPocketEnclosedTwoArc :
    GreendlingerLeaf.P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v} :=
  innerPocketEnclosedTwoArcLocal_of_pinched GL03BPinch.innerPocketEnclosedTwoArcPinched

/-- **The Piece07 lake exclusion** (Osin, proof of Lemma 9.7(b); `thm:hull`). -/
theorem cellPocketWalkProperArcsBelowSection :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  GreendlingerLeaf.P07LakeExclusion.proof_of_innerPocketEnclosed innerPocketEnclosedTwoArc

end GroupApproximation.Full.GL03B

#audit_axioms GroupApproximation.Full.GL03B.innerPocketEnclosedTwoArc
#audit_axioms GroupApproximation.Full.GL03B.cellPocketWalkProperArcsBelowSection
