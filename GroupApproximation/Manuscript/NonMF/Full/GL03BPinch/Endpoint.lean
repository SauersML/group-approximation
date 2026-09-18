import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Statement
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Cases
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.Split
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.ORDERMODULE
import GroupApproximation.Meta.AxiomGuard

/-!
# The corrected enclosed inner pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex 2134, Hull's small cancellation theorem, through Osin's Lemma 9.7).

Proof of `InnerPocketEnclosedTwoArcCorrected`.  Fill every face of the pocket walk off the exterior
piece `Cmp`, the component of the outer face off the side faces.  The kept relator cell `C` is on
the side, so it is filled.  Then split on whether `Π_i` and `Π_j` are in `Cmp`.
* Neither: `twoArcConclusion_of_lakes`.
* Only one: `twoArcConclusion_of_firstExterior`, `twoArcConclusion_of_secondExterior`.
* Both: the outer walk reads the pocket walk in order
  (`GL03BPinchOrder.exists_lakeWalk_bothExterior_of_sublist`, with the inner Euler equality
  `hinner` through `GL03BPinchOrder.lakeWalk_reverse_map_alpha_sublist`),
  then `twoArcConclusion_of_ordered`.

The pinched form follows (`innerPocketEnclosedTwoArcPinchedCorrected_of_corrected`).

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex 2134); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.Full.GL03BPinch

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent

/-- **The enclosed inner pocket of a cell pocket walk, corrected** (Osin, proof of Lemma 9.7(b);
`thm:hull`). -/
theorem innerPocketEnclosedTwoArcCorrected : InnerPocketEnclosedTwoArcCorrected.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  show TwoArcConclusion eps X
  by_cases hi : (cell X i).face ∈
      component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace
  · by_cases hj : (cell X j).face ∈
        component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace
    · obtain ⟨x₀, s₁, s₂, hx₀, heq, hs₁, hs₂⟩ :=
        GroupApproximation.Full.GL03BPinchOrder.exists_lakeWalk_bothExterior_of_sublist K hw hoff
          hi hj (GroupApproximation.Full.GL03BPinchOrder.lakeWalk_reverse_map_alpha_sublist hw
            X.planar hinner _
            (GroupApproximation.Full.GL03BPinchOrder.walk_eq_append_alpha_secondArcDart K))
      exact twoArcConclusion_of_ordered K hw hoff hi hj hx₀ heq hs₁ hs₂ hC hCf
    · exact twoArcConclusion_of_firstExterior K hw hoff hi hj hC hCf
  · by_cases hj : (cell X j).face ∈
        component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace
    · exact twoArcConclusion_of_secondExterior K hw hoff hi hj hC hCf
    · exact twoArcConclusion_of_lakes K hw hoff hi hj hC hCf

/-- **The pinched enclosed inner pocket, corrected** (`thm:hull`). -/
theorem innerPocketEnclosedTwoArcPinchedCorrected :
    InnerPocketEnclosedTwoArcPinchedCorrected.{u, w, v} :=
  innerPocketEnclosedTwoArcPinchedCorrected_of_corrected innerPocketEnclosedTwoArcCorrected

end GroupApproximation.Full.GL03BPinch

#audit_axioms GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected
#audit_axioms GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcPinchedCorrected
