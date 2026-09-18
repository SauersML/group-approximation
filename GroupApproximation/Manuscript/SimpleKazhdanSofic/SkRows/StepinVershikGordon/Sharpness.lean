import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.StepinVershikGordon.Iff
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ToeplitzAnswer
import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Meta.AxiomGuard

/-!
# Sharpness of the finite-presentation hypothesis in Stepin / Vershik–Gordon

`simple_kazhdan_sofic_group.tex`, tex l.730–732:

> No group in Theorem~\ref{thm:general}\textup{(b)} is finitely presented:
> a finitely presented LEF group is residually
> finite~\cite{Stepin,VershikGordon}, and an infinite simple group is not.

The sentence uses the hypothesis "finitely presented" in an essential way: finite generation is not
enough.  The witness is the note's own group `G_X = EL_3(LC(X, F_2) ⋊_T ℤ)` at the Toeplitz
subshift.

## Route

* `printedSimpleKazhdanSoficMain` (closed, `thm:main`) at `n = 3`: `G_X` is infinite, finitely
  generated, simple and LEF.
* `NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite`: an infinite simple group
  is not residually finite.
* Hence `G_X` is finitely generated, LEF, not residually finite, and (by the forward direction of
  `manuscriptSentence_finitelyPresentedLEFIffResiduallyFinite`) not finitely presented.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.StepinVershikGordon

open GroupApproximation GroupApproximation.SimpleKazhdanSofic

/-- The Toeplitz instance of `G_X` is finitely generated, LEF, not residually finite and not
finitely presented. -/
theorem toeplitzGX_fg_isLEF_not_residuallyFinite_not_finitelyPresented :
    Group.FG (G toeplitzSubshift) ∧ IsLEF (G toeplitzSubshift) ∧
      ¬ IsResiduallyFinite (G toeplitzSubshift) ∧
      ¬ Group.IsFinitelyPresented (G toeplitzSubshift) := by
  obtain ⟨hinf, hfg, hsimple, -, -, hlef, -, -⟩ :=
    printedSimpleKazhdanSoficMain Bool toeplitzSubshift toeplitzSubshift_infinite
      toeplitzSubshift_isMinimal 3 le_rfl
  have hnrf : ¬ IsResiduallyFinite (G toeplitzSubshift) :=
    @GroupApproximation.NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite
      (G toeplitzSubshift) _ hsimple hinf
  refine ⟨hfg, hlef, hnrf, fun hfp => ?_⟩
  exact hnrf ((manuscriptSentence_finitelyPresentedLEFIffResiduallyFinite hfp).mp hlef)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.StepinVershikGordon.toeplitzGX_fg_isLEF_not_residuallyFinite_not_finitelyPresented

/-- **Sharpness**: finite generation does not suffice in Stepin / Vershik–Gordon; there is a
finitely generated LEF group that is not residually finite. -/
theorem not_forall_fg_isLEF_residuallyFinite :
    ¬ ∀ (E : Type) [Group E], Group.FG E → IsLEF E → IsResiduallyFinite E := by
  intro h
  obtain ⟨hfg, hlef, hnrf, -⟩ :=
    toeplitzGX_fg_isLEF_not_residuallyFinite_not_finitelyPresented
  exact hnrf (h (G toeplitzSubshift) hfg hlef)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.StepinVershikGordon.not_forall_fg_isLEF_residuallyFinite

/-- **tex l.730–732, with sharpness**: a finitely presented group is LEF iff it is residually finite,
and the hypothesis cannot be weakened to finite generation. -/
theorem manuscriptSentence_stepinVershikGordonIffSharp :
    (∀ (E : Type) [Group E], Group.IsFinitelyPresented E → (IsLEF E ↔ IsResiduallyFinite E)) ∧
      ¬ ∀ (E : Type) [Group E], Group.FG E → IsLEF E → IsResiduallyFinite E :=
  ⟨fun _ _ hfp => manuscriptSentence_finitelyPresentedLEFIffResiduallyFinite hfp,
    not_forall_fg_isLEF_residuallyFinite⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.StepinVershikGordon.manuscriptSentence_stepinVershikGordonIffSharp

end GroupApproximation.SimpleKazhdanSofic.SkRows.StepinVershikGordon
