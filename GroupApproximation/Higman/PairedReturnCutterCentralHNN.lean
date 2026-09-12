import GroupApproximation.GroupTheory.CentralHNNResiduallyFinite
import GroupApproximation.Higman.PairedReturnAmbientResiduallyFinite
import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# The central HNN extension over the paired-return cutter

The paired-return ambient is already finitely presented and residually finite.
Consequently, once its literal five-generator cutter is proved profinitely
closed, the central HNN extension over that cutter is again both finitely
presented and residually finite.  This file packages that final consumption
step separately from the finite-quotient argument proving closedness.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnCutterCentralHNN

open PairedReturnCutter

/-- The central HNN extension which adjoins one stable letter commuting with
the literal five-generator cutter. -/
abbrev CutterExtension : Type := CentHNN fiveCutter

/-- Countability of a central HNN extension, exposed locally because Mathlib
does not install quotient countability as a global instance. -/
private theorem centHNNCountable
    {G : Type} [Group G] [Countable G]
    (M : Subgroup G) : Countable (CentHNN M) := by
  letI : Countable (Multiplicative ℤ) :=
    Countable.of_equiv ℤ Multiplicative.ofAdd
  letI : Countable (FreeMonoid (G ⊕ Multiplicative ℤ)) :=
    inferInstanceAs (Countable (List (G ⊕ Multiplicative ℤ)))
  letI : Countable (Monoid.Coprod G (Multiplicative ℤ)) :=
    Monoid.Coprod.mk_surjective.countable
  unfold CentHNN HNNExtension
  exact Con.mk'_surjective.countable

/-- The new stable letter detects Higman's infinite conjugator graph exactly
on the canonical left copy of `F₃ × F₃`.  The forward implication is
Britton's lemma; the final rewrite is the five-generator cutter theorem. -/
theorem stable_commutes_left_iff
    (p : PairedReturnGraphIntersection.P) :
    Commute (HNNExtension.t : CutterExtension)
        (HNNExtension.of
          (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC p)) ↔
      p ∈ Star.graphSub := by
  rw [commute_t_of_iff]
  exact SetLike.ext_iff.mp fiveCutter_comap_left p

/-- Finite presentability uses only finite presentability of the paired
ambient and finite generation of the five-generator cutter. -/
theorem cutterExtension_finitelyPresented :
    Group.IsFinitelyPresented CutterExtension := by
  letI : Group.IsFinitelyPresented Ambient := ambient_finitelyPresented
  exact isFinitelyPresented_centHNN fiveCutter fiveCutter_fg

/-- Profinite closedness of the cutter is exactly the remaining hypothesis
for residual finiteness of its central HNN extension. -/
theorem cutterExtension_residuallyFinite
    (hclosed : profiniteClosure fiveCutter = fiveCutter) :
    Group.ResiduallyFinite CutterExtension := by
  letI : Group.ResiduallyFinite Ambient :=
    PairedReturnAmbientResiduallyFinite.ambient_residuallyFinite
  exact CentralHNNResiduallyFinite.centralHNN_residuallyFinite
    fiveCutter hclosed

/-- The combined endpoint consumed by the effective compiler: one closedness
proof supplies both finiteness properties of the central detector extension. -/
theorem cutterExtension_fp_and_residuallyFinite
    (hclosed : profiniteClosure fiveCutter = fiveCutter) :
    Group.IsFinitelyPresented CutterExtension ∧
      Group.ResiduallyFinite CutterExtension :=
  ⟨cutterExtension_finitelyPresented,
    cutterExtension_residuallyFinite hclosed⟩

/-- The exact positive-branch consequence: the closed paired cutter produces
a finitely presented operator-MF central detector group. -/
theorem cutterExtension_finitelyPresented_and_operatorMF
    (hclosed : profiniteClosure fiveCutter = fiveCutter) :
    Group.IsFinitelyPresented CutterExtension ∧
      IsOperatorMF CutterExtension := by
  letI : Countable PairedReturnAmbientResiduallyFinite.Stage1 :=
    centHNNCountable PairedReturnAmbientResiduallyFinite.Edge
  letI : Countable PairedReturnAmbientResiduallyFinite.Stage2 :=
    centHNNCountable
      (FreeLampFinitePresentation.stage1Sub
        PairedReturnAmbientResiduallyFinite.P
        PairedReturnAmbientResiduallyFinite.Edge)
  letI : Countable Ambient :=
    Countable.of_equiv PairedReturnAmbientResiduallyFinite.Stage2
      PairedReturnAmbientResiduallyFinite.ambientEquivStage2.symm
  letI : Countable (Multiplicative ℤ) :=
    Countable.of_equiv ℤ Multiplicative.ofAdd
  letI : Countable (FreeMonoid (Ambient ⊕ Multiplicative ℤ)) :=
    inferInstanceAs (Countable (List (Ambient ⊕ Multiplicative ℤ)))
  letI : Countable (Monoid.Coprod Ambient (Multiplicative ℤ)) :=
    Monoid.Coprod.mk_surjective.countable
  letI : Countable CutterExtension := by
    unfold CutterExtension CentHNN HNNExtension
    exact Con.mk'_surjective.countable
  letI : Group.ResiduallyFinite CutterExtension :=
    cutterExtension_residuallyFinite hclosed
  exact ⟨cutterExtension_finitelyPresented,
    isOperatorMF_of_residuallyFinite⟩

end PairedReturnCutterCentralHNN
end Higman
end GroupApproximation

#audit_closed_axioms GroupApproximation.Higman.PairedReturnCutterCentralHNN.cutterExtension_finitelyPresented
