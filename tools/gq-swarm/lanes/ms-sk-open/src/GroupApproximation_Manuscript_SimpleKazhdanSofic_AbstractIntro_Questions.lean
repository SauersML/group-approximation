import GroupApproximation.Manuscript.SimpleKazhdanSofic.QuestionsClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanGeneralClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitLEF
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.CrossedProductConjugacy
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Meta.AxiomGuard

/-!
# `simple_kazhdan_sofic_group.tex`, questions (census slice, tex l.731–752)

Census sentences of `sec:questions`, located by text (the section has since been rewritten as
"The finitely presented case", tex l.728–738).

> l.733–737: Infinite finitely presented simple Kazhdan groups exist~\cite{CapraceRemy}, while no
> group in Theorem~\ref{thm:general}\textup{(b)} is finitely presented: a finitely presented LEF
> group is residually finite~\cite{Stepin,VershikGordon}, and an infinite simple group is not.
>
> l.742–743: A sofic example for Question~\ref{q:fp} would answer this negatively.  (Current text:
> "A sofic example would not be LEF, and it would answer Open problem 6.1 of Alekseev and Thom,
> which asks for finitely presented sofic groups with property (T) that are not residually finite.")
>
> l.745–746: Corollary~\ref{cor:lef} gives this for LEF groups, with LEF hosts.
>
> l.747–749: If $(X,T)$ is flip conjugate to $(Y,T')$, that is, topologically conjugate to $(Y,T')$
> or to $(Y,T'^{-1})$, then $G_X\cong G_Y$, and for topological full groups the converse
> holds~\cite{GPS99,BezuglyiMedynets}.

Route.

* `manuscriptSentence_generalLimitsNotFinitelyPresented`: the closed Stepin–Vershik–Gordon
  statement `printedFinitelyPresentedLEFResiduallyFinite`, non-residual-finiteness of infinite
  simple groups, and for every instance of `thm:general`(b) (`printedSimpleKazhdanGeneral`) the
  group `EL_n` is infinite, simple and a marked limit of finite groups, hence LEF
  (`isLEF_of_isMarkedLimit`) and not finitely presented.  The Caprace–Rémy existence clause is not
  formalized.
* `manuscriptSentence_soficFinitelyPresentedExampleNotLEF`: `printedSoficKazhdanExampleNotLEF`.
* `manuscriptSentence_lefGroupsEmbedInLEFHosts`: `cor:lef` (`printedLEFSubgroupCharacterization`)
  gives an LEF host, which is LEF as a marked limit of finite groups, hence sofic.
* `manuscriptSentence_flipConjugateSubshiftsIsomorphicGroups`: `printedConjugacyIsomorphism`.  The
  converse for topological full groups (Giordano–Putnam–Skau, Bezuglyi–Medynets) is not formalized.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- **tex l.733–737**, mathematical clauses: a finitely presented LEF group is residually finite, an
infinite simple group is not residually finite, and no group `EL_n(R)`, `n ≥ 3`, of
Theorem `thm:general`(b) is finitely presented. -/
theorem manuscriptSentence_generalLimitsNotFinitelyPresented :
    (∀ (E : Type) [Group E], Group.IsFinitelyPresented E → IsLEF E → IsResiduallyFinite E) ∧
      (∀ (E : Type) [Group E] [IsSimpleGroup E] [Infinite E], ¬ IsResiduallyFinite E) ∧
      ∀ (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type) [TopologicalSpace Z] [CompactSpace Z]
        [TopologicalSpace.MetrizableSpace Z] [TotallyDisconnectedSpace Z] [PerfectSpace Z]
        [Nonempty Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z], MulAction.IsMinimal Λ Z →
        (∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z) →
        ∀ S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2)), 1 ∈ S →
          Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤ →
        ∀ (N : ℕ → ℕ)
          (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
          IsMatricialVia S N φ → ∀ n : ℕ, 3 ≤ n →
            ¬ Group.IsFinitelyPresented
              ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) := by
  refine ⟨fun E _ => printedFinitelyPresentedLEFResiduallyFinite.{0} E,
    fun E _ _ _ => GroupApproximation.NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite E,
    ?_⟩
  intro Λ _ _ Z _ _ _ _ _ _ _ _ hmin hfree S h1 hS N φ hφ n hn
  obtain ⟨hinf, -, hsimple, -, hlim, -, -, hexp⟩ :=
    printedSimpleKazhdanGeneral Λ Z hmin hfree S h1 hS N φ hφ n hn
  obtain ⟨-, hfin, -, -⟩ := hexp
  exact @printedNotFinitelyPresentedOfLEFSimpleInfinite.{0} _ _ hsimple hinf
    (isLEF_of_isMarkedLimit hfin hlim)

/-- **tex l.742–743** (current text l.735–738): an infinite finitely presented simple sofic group
with property (T) is not LEF, and it is a finitely presented sofic Kazhdan group that is not
residually finite. -/
theorem manuscriptSentence_soficFinitelyPresentedExampleNotLEF :
    ∀ (E : Type) [Group E] [IsSimpleGroup E] [Infinite E], Group.IsFinitelyPresented E →
      HasKazhdanPropertyT.{0, 0} E → IsSofic E →
        ¬ IsLEF E ∧ (Group.IsFinitelyPresented E ∧ IsSofic E ∧ HasKazhdanPropertyT.{0, 0} E ∧
          ¬ IsResiduallyFinite E) :=
  printedSoficKazhdanExampleNotLEF

/-- **tex l.745–746**: every finitely generated LEF group is a subgroup of an infinite, finitely
generated, simple Kazhdan group that is a marked limit of finite simple groups whose Cayley graphs
form expanders, and that host is LEF, hence sofic. -/
theorem manuscriptSentence_lefGroupsEmbedInLEFHosts (Γ : Type) [Group Γ] (hfg : Group.FG Γ)
    (hLEF : IsLEF Γ) :
    ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ IsLEF E ∧ IsSofic E ∧
      ∃ f : Γ →* E, Function.Injective f := by
  obtain ⟨E, _, hhost, hemb⟩ := (printedLEFSubgroupCharacterization Γ hfg).mp hLEF
  obtain ⟨-, -, -, -, _, _, _, _, _, _, -, hlim, hexp⟩ := id hhost
  obtain ⟨-, hfin, -, -⟩ := hexp
  have hLEFE : IsLEF E := isLEF_of_isMarkedLimit hfin hlim
  exact ⟨E, inferInstance, hhost, hLEFE, isSofic_of_isLEF hLEFE, hemb⟩

/-- **tex l.747–749**, first clause: if the subshifts `X` and `Y` are flip conjugate, that is,
topologically conjugate or conjugate after inverting the shift of `Y`, then `G_X ≅ G_Y`. -/
theorem manuscriptSentence_flipConjugateSubshiftsIsomorphicGroups :
    ∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B] (S : Subshift A ℤ) (S' : Subshift B ℤ)
      (φ : S.carrier ≃ₜ S'.carrier),
      ((∀ x, φ (subshiftHomeo S x) = subshiftHomeo S' (φ x)) ∨
        ∀ x, φ (subshiftHomeo S x) = (subshiftHomeo S').symm (φ x)) →
      Nonempty (G S ≃* G S') :=
  printedConjugacyIsomorphism

end GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_generalLimitsNotFinitelyPresented
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_soficFinitelyPresentedExampleNotLEF
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_lefGroupsEmbedInLEFHosts
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_flipConjugateSubshiftsIsomorphicGroups
