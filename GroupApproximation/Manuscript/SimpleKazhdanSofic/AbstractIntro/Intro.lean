import GroupApproximation.Manuscript.SimpleKazhdanSofic.CStarNoLocalLifting
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThomFactorizationSentence
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GXAnswersBrownOzawaPestovClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.McDuffBrownFormulation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ToeplitzAnswer
import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Meta.AxiomGuard

/-!
# `simple_kazhdan_sofic_group.tex`, introduction (tex l.49–67)

> l.54–57: Ozawa stated the hyperlinear form in 2003, noting that the full $C^*$-algebra of such a
> group cannot have the local lifting property~\cite[\S7]{Ozawa}, and Pestov asked the sofic form as
> Open question~9.1~\cite{Pestov}.
>
> l.57–60: Thom constructed a finitely generated Kazhdan group that is locally embeddable into finite
> groups but not residually finite, and so lacks the factorization property~\cite{Thom}, but his
> example is not simple.
>
> l.66–67: The groups below answer all three forms of the question positively.

The sentences at l.60–63 (Pestov–Kwiatkowska) and l.63–66 (Arzhantseva) are credit.

Route.

* `manuscriptSentence_ozawaFullCStarNoLocalLifting`: the closed `printedOzawaNoLocalLiftingGeneral`
  (Kazhdan ⇒ finitely generated; hyperlinear ⇒ trace-preserving matrix model; LLP ⇒ factorization
  property; Kirchberg's theorem excludes the factorization property for infinite simple Kazhdan
  groups).
* `manuscriptSentence_kazhdanLEFNotResiduallyFiniteLacksFactorization`: a Kazhdan group that is not
  residually finite lacks the factorization property (Kirchberg), and there is a finitely generated
  Kazhdan LEF group that is not residually finite, witnessed by `G_X` at the Toeplitz subshift, which
  is infinite and simple, hence not residually finite.  Thom's own (non-simple) group is not built.
* `manuscriptSentence_groupsAnswerAllThreeForms`: some `G_X` is infinite, simple, Kazhdan, sofic
  (Pestov's form) and hyperlinear (Ozawa's form); for Brown's form, `L(G_X)` is a II₁ factor,
  `L(G_X) ⊗̄ 𝓡` is McDuff and `G_X` embeds in its unitary group.  The embedding of
  `L(G_X) ⊗̄ 𝓡` in `𝓡^ω` is not stated.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- **tex l.54–57**, mathematical clause: the full C⋆-algebra of an infinite simple hyperlinear group
with property (T) does not have the local lifting property. -/
theorem manuscriptSentence_ozawaFullCStarNoLocalLifting :
    ∀ (E : Type) [Group E] [IsSimpleGroup E] [Infinite E],
      HasKazhdanPropertyT.{0, 0} E → IsHyperlinear E →
        ¬ GroupApproximation.LocalLifting.HasLocalLiftingProperty.{1, 0}
          (GroupApproximation.MaximalGroupCStar E) :=
  printedOzawaNoLocalLiftingGeneral

/-- **tex l.57–60**, mathematical clauses: a Kazhdan group that is not residually finite lacks the
factorization property, and there is a finitely generated Kazhdan LEF group that is not residually
finite (and so lacks the factorization property). -/
theorem manuscriptSentence_kazhdanLEFNotResiduallyFiniteLacksFactorization :
    (∀ (E : Type) [Group E], HasKazhdanPropertyT.{0, 0} E → ¬ IsResiduallyFinite E →
        ¬ GroupApproximation.NinetyNineProblems.HasFactorizationProperty E) ∧
      ∃ (E : Type) (_ : Group E), Group.FG E ∧ HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E ∧
        ¬ IsResiduallyFinite E ∧ ¬ GroupApproximation.NinetyNineProblems.HasFactorizationProperty E := by
  obtain ⟨hinf, hfg, hsimple, hT, -, hlef, -, -⟩ :=
    printedSimpleKazhdanSoficMain Bool toeplitzSubshift toeplitzSubshift_infinite
      toeplitzSubshift_isMinimal 3 le_rfl
  have hnrf : ¬ IsResiduallyFinite (G toeplitzSubshift) :=
    @GroupApproximation.NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite
      (G toeplitzSubshift) _ hsimple hinf
  exact ⟨fun E _ => printedKazhdanNotResiduallyFiniteLacksFactorizationProperty.{0} E,
    G toeplitzSubshift, inferInstance, hfg, hT, hlef, hnrf,
    printedKazhdanNotResiduallyFiniteLacksFactorizationProperty.{0} (G toeplitzSubshift) hT hnrf⟩

/-- **tex l.66–67**: some `G_X`, with `X` an infinite minimal subshift, is an infinite simple group
with property (T) that is sofic and hyperlinear, `L(G_X)` is a II₁ factor, `L(G_X) ⊗̄ 𝓡` is a McDuff
factor, and `G_X` embeds in the unitary group of `L(G_X) ⊗̄ 𝓡`. -/
theorem manuscriptSentence_groupsAnswerAllThreeForms :
    ∃ S : Subshift Bool ℤ, Infinite S.carrier ∧ IsMinimal S ∧ Infinite (G S) ∧ IsSimpleGroup (G S) ∧
      HasKazhdanPropertyT.{0, 0} (G S) ∧ IsSofic (G S) ∧ IsHyperlinear (G S) ∧
      GroupApproximation.IIOneFactor.IsIIOneFactor
          (GroupApproximation.GroupVonNeumann.groupVonNeumannAlgebra (G S)) ∧
        GroupApproximation.McDuff.IsMcDuffFactor
          (GroupApproximation.McDuff.tensorHyperfinite
            (GroupApproximation.GroupVonNeumann.groupVonNeumannAlgebra (G S))) ∧
        ∃ φ : G S →* unitary
            ↥(GroupApproximation.McDuff.tensorHyperfinite
              (GroupApproximation.GroupVonNeumann.groupVonNeumannAlgebra (G S))).toStarSubalgebra,
          Function.Injective φ := by
  obtain ⟨S, hSinf, hmin, hinf, hsimple, hT, hsof, hhyp⟩ := printedGXAnswersBrownOzawaPestov
  exact ⟨S, hSinf, hmin, hinf, hsimple, hT, hsof, hhyp,
    printedBrownFormulationFactors.{0} (G S) hsimple hinf⟩

end GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_ozawaFullCStarNoLocalLifting
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_kazhdanLEFNotResiduallyFiniteLacksFactorization
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_groupsAnswerAllThreeForms
