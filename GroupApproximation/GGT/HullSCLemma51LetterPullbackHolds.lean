import GroupApproximation.GGT.HullSCLemma51LetterPullbackCut
import GroupApproximation.GGT.HullSCLemma51LetterPullbackCutOutcomeRight
import GroupApproximation.GGT.HullSCLemma51LetterPullbackShortcut
import GroupApproximation.GGT.HullSCLemma51EmbeddedProducer

/-!
# The quotient peripheral letter pullback holds

The embedded Lemma 5.1 bridge of Hull's small cancellation theorem (manuscript line 1636,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`) consumes the letter
pullback: the peripheral letters of the quotient in a bounded relative ball are images of bounded
products of pullback atoms.

* `CutLift.toCutMove`: a cut lift is a cut move.
* `cutLiftOutcome`: every cut lift has an outcome, since every cut move has one
  (`CutMove.outcome`).
* `quotientPeripheralLetterPullbackStatement_holds`: the move bound for words with a non-geodesic
  rotation (`letterStepBound_of_not_isRelGeodesic`) and for words with every rotation geodesic
  (`letterStepBound_of_cutLiftOutcome`).
-/

namespace GroupApproximation
namespace HullSC

universe u v w

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- **A cut lift is a cut move.** -/
theorem CutLift.toCutMove {W : Set (List (GGT.RelLetter G Lambda))} {D : GGT.RelGenSet G Lambda}
    {q : G →* Q} {hq : Function.Surjective q} {lam : Lambda} {h : G} {c : Q}
    {L arc R ext rem tail x y : List (GGT.RelLetter G Lambda)}
    (hcl : CutLift W D q hq lam h c L arc R ext rem tail x y) :
    CutMove W D q hq lam h c L arc R ext rem x y tail :=
  { face := hcl.face
    rem_letters := hcl.rem_adm
    rem_sub := ⟨ext ++ rem, hcl.relator, fun _ ha => List.mem_append_right ext ha⟩
    null := by
      have hk := hcl.rem_null
      rwa [hcl.face.value] at hk
    short := hcl.short
    lift := hcl.lift
    split := hcl.split }

/-- **Every cut lift has an outcome.**  A cut lift is a cut move, and the rotated word
`arc ++ tail = x ++ comp λ h⁻¹ :: y` is one letter longer than `x` and `y` together. -/
theorem cutLiftOutcome (W : Set (List (GGT.RelLetter G Lambda))) (D : GGT.RelGenSet G Lambda)
    (q : G →* Q) (hq : Function.Surjective q) : CutLiftOutcome W D q hq := by
  intro lam h c L arc R ext rem tail x y r N n hcl hr1 hr hN hn
  have hn2 : arc.length + tail.length ≤ n + 2 := by
    have e := congrArg List.length hcl.split
    simp only [List.length_append, List.length_cons] at e
    omega
  exact hcl.toCutMove.outcome hr1 hr hN hn2

/-- **The quotient peripheral letter pullback**, at the inputs of the embedded Lemma 5.1 bridge of
Hull's small cancellation theorem (manuscript line 1636,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`).  A word with a non-geodesic
rotation shortcuts; a word with every rotation geodesic has a certificate cut. -/
theorem quotientPeripheralLetterPullbackStatement_holds :
    QuotientPeripheralLetterPullbackStatement.{u, v, w} := by
  intro G _ Lambda D _ eps rho mu W Q _ q hq _ hmuUpper hrho hsc hker hcert
  exact quotientPeripheralLetterPullbackAt_of_letterStepBound
    ((letterStepBound_of_not_isRelGeodesic D W q hq).or
      (letterStepBound_of_cutLiftOutcome D hsc hmuUpper hrho q hq hker hcert
        (cutLiftOutcome W D q hq)))
    (fun w => (Classical.em (∀ r : ℕ, IsRelGeodesic D (w.rotate r))).symm)

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.CutLift.toCutMove
#audit_axioms GroupApproximation.HullSC.cutLiftOutcome
#audit_closed_axioms GroupApproximation.HullSC.quotientPeripheralLetterPullbackStatement_holds
