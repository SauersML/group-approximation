import GroupApproximation.Manuscript.SimpleKazhdanSofic.CStarNoLocalLifting
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GXAnswersBrownOzawaPestovClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# `simple_kazhdan_sofic_group.tex`, introduction, Ozawa's form and the LLP obstruction (tex l.54–57)

> l.49: Can an infinite simple group with property~\textup{(T)} be hyperlinear?
>
> l.54–57: Ozawa stated the hyperlinear form in 2003, noting that the full $C^*$-algebra of such a
> group cannot have the local lifting property~\cite[\S7]{Ozawa}, and Pestov asked the sofic form as
> Open question~9.1~\cite{Pestov}.

"The hyperlinear form" is the question of l.49: is there an infinite simple group with property (T)
that is hyperlinear?  "Such a group" is an infinite simple hyperlinear group with property (T).
"The sofic form" asks the same with "sofic" in place of "hyperlinear".  The names and dates are
credit.

`manuscriptSentence_ozawaHyperlinearFormNoLocalLifting` states, unconditionally:

1. Ozawa's §7 reason ("by the above theorem"): for a countable hyperlinear group `E`, if `C⋆(E)` has
   the local lifting property then `E` has the factorization property
   (`LocalLifting.localLiftingFactorizationStatement_holds` together with
   `HyperlinearTraceVanishing.hyperlinearTracePreservingModelStatement_holds`).
2. The obstruction: the full C⋆-algebra of every infinite simple hyperlinear group with property (T)
   does not have the local lifting property (the closed endpoint
   `SimpleKazhdanSofic.printedOzawaNoLocalLiftingGeneral`, audited with `#audit_closed_axioms`; it
   runs through Kirchberg's Theorem 1.1, `KirchbergTheorem.kirchbergKazhdanFactorizationInput`,
   which is proved).
3. The hyperlinear form of the question has a positive answer, and the witness has a full
   C⋆-algebra without the local lifting property: some `G_X` is infinite, simple, Kazhdan and
   hyperlinear (`printedGXAnswersBrownOzawaPestov`, closed), and clause 2 applies to it.
4. The sofic form of the question has a positive answer, by the same `G_X`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro

open GroupApproximation.SimpleKazhdanSofic

/-- **tex l.54–57**, mathematical content.  (1) For a countable hyperlinear group, the local lifting
property of the full C⋆-algebra gives the factorization property.  (2) The full C⋆-algebra of an
infinite simple hyperlinear group with property (T) does not have the local lifting property.
(3) The hyperlinear form of the question holds: there is an infinite simple hyperlinear group with
property (T), and its full C⋆-algebra does not have the local lifting property.  (4) The sofic form
of the question holds: there is an infinite simple sofic group with property (T). -/
theorem manuscriptSentence_ozawaHyperlinearFormNoLocalLifting :
    (∀ (E : Type) [Group E] [Countable E], IsHyperlinear E →
        GroupApproximation.LocalLifting.HasLocalLiftingProperty.{1, 0}
            (GroupApproximation.MaximalGroupCStar E) →
          GroupApproximation.NinetyNineProblems.HasFactorizationProperty E) ∧
      (∀ (E : Type) [Group E] [IsSimpleGroup E] [Infinite E],
        HasKazhdanPropertyT.{0, 0} E → IsHyperlinear E →
          ¬ GroupApproximation.LocalLifting.HasLocalLiftingProperty.{1, 0}
            (GroupApproximation.MaximalGroupCStar E)) ∧
      (∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
        IsHyperlinear E ∧
          ¬ GroupApproximation.LocalLifting.HasLocalLiftingProperty.{1, 0}
            (GroupApproximation.MaximalGroupCStar E)) ∧
      ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
        IsSofic E := by
  have hfact : ∀ (E : Type) [Group E] [Countable E], IsHyperlinear E →
      GroupApproximation.LocalLifting.HasLocalLiftingProperty.{1, 0}
          (GroupApproximation.MaximalGroupCStar E) →
        GroupApproximation.NinetyNineProblems.HasFactorizationProperty E :=
    fun E _ _ hH hLLP =>
      GroupApproximation.LocalLifting.localLiftingFactorizationStatement_holds E hLLP
        (GroupApproximation.HyperlinearTraceVanishing.hyperlinearTracePreservingModelStatement_holds.{0}
          E hH)
  have hobs : ∀ (E : Type) [Group E] [IsSimpleGroup E] [Infinite E],
      HasKazhdanPropertyT.{0, 0} E → IsHyperlinear E →
        ¬ GroupApproximation.LocalLifting.HasLocalLiftingProperty.{1, 0}
          (GroupApproximation.MaximalGroupCStar E) :=
    printedOzawaNoLocalLiftingGeneral
  obtain ⟨S, -, -, hinf, hsimple, hT, hsof, hhyp⟩ := printedGXAnswersBrownOzawaPestov
  exact ⟨hfact, hobs,
    ⟨G S, inferInstance, hinf, hsimple, hT, hhyp, @hobs (G S) _ hsimple hinf hT hhyp⟩,
    ⟨G S, inferInstance, hinf, hsimple, hT, hsof⟩⟩

end GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro

#audit_closed_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_ozawaHyperlinearFormNoLocalLifting
