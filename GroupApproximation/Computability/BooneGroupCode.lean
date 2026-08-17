import GroupApproximation.Computability.BooneTowerPresentation
import GroupApproximation.Computability.BooneGroupGoodness

/-!
# Simpson's `G_M`, with a code

`BooneTowerPresentation` presents the tower and adjoins the last letter, ending
at `finalPres` and `stageCode`.  What it does not do is say that the group it
has presented is the one the undecidability results are about: `FinalGroup`
occurs in that file only inside a comment.

The two are not definitionally equal, and the reason is worth stating because it
is the kind of gap that typechecks either way.  `FinalGroup mm hM` is

    HNNExtension (tower (machineIdentifications mm hM)).Carrier
      (towerTSub (machineIdentifications mm hM)) (towerTSub …) (MulEquiv.refl _)

whereas the presentation builds `finalStage (machineTower mm hM)
(machineTowerPres mm hM).tsub`, whose associated subgroup is the *presentation's*
`tsub`.  Those agree only by `machineTowerPres_tsub`, an equality of subgroups —
and the subgroup occurs in the **type** of the HNN extension, so the agreement
has to be transported rather than unfolded.  `hnnCongrOfEq` is that transport,
by `subst`, which is what keeps it reasonable afterwards rather than an opaque
`cast`.

With the bridge, `stageCodeEquiv` reaches all the way:

    finalGroupCodeEquiv : Carrier (finalGroupCode mm hM) ≃* FinalGroup mm hM

so `G_M` has a `PresentationCode` presenting it.  That is the first of the two
things `D4'` needs; the second is a computable map from a configuration to the
word attached to it, in this code's numbering.
-/

namespace GroupApproximation
namespace Computability

open BooneGroup BooneTowerPresentation

/-- Transport an HNN extension along an equality of its associated subgroup.
Proved by `subst` rather than `cast` so that the resulting equivalence can be
computed with. -/
noncomputable def hnnCongrOfEq {G : Type*} [Group G] {T₁ T₂ : Subgroup G}
    (h : T₁ = T₂) :
    HNNExtension G T₁ T₁ (MulEquiv.refl _) ≃* HNNExtension G T₂ T₂ (MulEquiv.refl _) := by
  subst h
  exact MulEquiv.refl _

/-- **The presented last stage is Simpson's `G_M`.**  This is the statement
`BooneTowerPresentation` stops one step short of. -/
noncomputable def finalStageEquivFinalGroup (mm : ModularMachine)
    (hM : (mm.size : ℤ) ≠ 0) :
    (finalStage (machineTower mm hM) (machineTowerPres mm hM).tsub).Carrier
      ≃* FinalGroup mm hM :=
  hnnCongrOfEq (machineTowerPres_tsub mm hM)

/-- **A presentation code for `G_M`.** -/
noncomputable def finalGroupCode (mm : ModularMachine) (hM : (mm.size : ℤ) ≠ 0) :
    PresentationCodes.PresentationCode :=
  stageCode (finalPres (machineTowerPres mm hM))

/-- **The code presents `G_M`.**  The group whose word problem is undecidable is
the group the code names, not merely one built the same way. -/
noncomputable def finalGroupCodeEquiv (mm : ModularMachine)
    (hM : (mm.size : ℤ) ≠ 0) :
    PresentationCodes.Carrier (finalGroupCode mm hM) ≃* FinalGroup mm hM :=
  (stageCodeEquiv (finalPres (machineTowerPres mm hM))).trans
    (finalStageEquivFinalGroup mm hM)

end Computability
end GroupApproximation
