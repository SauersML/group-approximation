import GroupApproximation.Manuscript.SimpleKazhdanSofic.QuestionsNotFinitelyPresented
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitLEF
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Dynamics.SurjunctivityTransfer
import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Kazhdan.Kazhdan
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite presentation, LEF and residual finiteness (Section 5, `tab:props`)

`simple_kazhdan_sofic_group.tex`, Section 5 "Questions" (l.728–738):

> No group in Theorem `thm:general`(b) is finitely presented: a finitely presented LEF group is
> residually finite [Stepin, VershikGordon], and an infinite simple group is not. Infinite finitely
> presented simple Kazhdan groups exist [CapraceRemy], and whether one of them is sofic, or at least
> hyperlinear, remains open. A sofic example would not be LEF, and it would answer Open problem 6.1 of
> Alekseev and Thom, which asks for finitely presented sofic groups with property (T) that are not
> residually finite.

and the rows of `tab:props`:

> not residually finite & infinite and simple
>
> not finitely presented & finitely presented LEF groups are residually finite

This file proves the group-theoretic content of these sentences for arbitrary groups, from rooted
modules only. The instances at `G_X` and at the groups of `thm:general`(b) are in
`Full/FinitelyPresented/Endpoints`.

* `isResiduallyFinite_of_isFinitelyPresented_of_isLEF`: a finitely presented LEF group is residually
  finite [Stepin, VershikGordon].
* `isLEF_iff_isResiduallyFinite_of_isFinitelyPresented`: for finitely presented groups, LEF and
  residual finiteness coincide (the converse needs no presentation).
* `not_isResiduallyFinite_of_isSimpleGroup_of_infinite`: an infinite simple group is not residually
  finite.
* `not_isFinitelyPresented_of_isLEF_of_isSimpleGroup_of_infinite`: an infinite simple LEF group is
  not finitely presented.
* `not_isFinitelyPresented_of_isMarkedLimit`: an infinite simple group that is a limit of finite groups
  in the space of marked groups is not finitely presented (the form used for `thm:general`(b)).
* `IsAlekseevThomExample`, `manuscriptSentence_soficExampleNotLEF_answersAlekseevThom`: a finitely
  presented infinite simple sofic Kazhdan group would not be LEF and would answer Open problem 6.1 of
  Alekseev and Thom.

The existence of infinite finitely presented simple Kazhdan groups [CapraceRemy] is not treated
here, and whether one of them is sofic or hyperlinear is an open problem, not a theorem.
-/

namespace GroupApproximation.Full.SK14

open GroupApproximation.SimpleKazhdanSofic

universe u v

/-! ## Stepin, Vershik–Gordon -/

/-- **A finitely presented LEF group is residually finite** (tex l.729–730, [Stepin, VershikGordon];
`tab:props`, row "not finitely presented"). -/
theorem isResiduallyFinite_of_isFinitelyPresented_of_isLEF {Γ : Type u} [Group Γ]
    (hfp : Group.IsFinitelyPresented Γ) (hLEF : IsLEF Γ) : IsResiduallyFinite Γ :=
  printedFinitelyPresentedLEFResiduallyFinite.{u} Γ hfp hLEF

/-- A residually finite group is LEF. -/
theorem isLEF_of_isResiduallyFinite {Γ : Type u} [Group Γ] (hrf : IsResiduallyFinite Γ) :
    IsLEF Γ := by
  haveI : Group.ResiduallyFinite Γ := isResiduallyFinite_iff_group_residuallyFinite.mp hrf
  exact isLEF_of_residuallyFinite

/-- **For finitely presented groups, LEF is residual finiteness** (tex l.729–730). -/
theorem isLEF_iff_isResiduallyFinite_of_isFinitelyPresented {Γ : Type u} [Group Γ]
    (hfp : Group.IsFinitelyPresented Γ) : IsLEF Γ ↔ IsResiduallyFinite Γ :=
  ⟨isResiduallyFinite_of_isFinitelyPresented_of_isLEF hfp, isLEF_of_isResiduallyFinite⟩

/-! ## Infinite simple groups -/

/-- **An infinite simple group is not residually finite** (tex l.730; `tab:props`, row "not residually
finite": "infinite and simple"). -/
theorem not_isResiduallyFinite_of_isSimpleGroup_of_infinite (Γ : Type u) [Group Γ]
    [IsSimpleGroup Γ] [Infinite Γ] : ¬ IsResiduallyFinite Γ :=
  NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite Γ

/-- **An infinite simple LEF group is not finitely presented** (tex l.728–730; `tab:props`, row "not
finitely presented"). -/
theorem not_isFinitelyPresented_of_isLEF_of_isSimpleGroup_of_infinite {Γ : Type u} [Group Γ]
    [IsSimpleGroup Γ] [Infinite Γ] (hLEF : IsLEF Γ) : ¬ Group.IsFinitelyPresented Γ := fun hfp =>
  not_isResiduallyFinite_of_isSimpleGroup_of_infinite Γ
    (isResiduallyFinite_of_isFinitelyPresented_of_isLEF hfp hLEF)

/-- **An infinite simple limit of finite groups is not finitely presented** (tex l.728–730). A limit
of finite groups in the space of marked groups is LEF (tex l.177–180), so it is not finitely
presented once it is infinite and simple. -/
theorem not_isFinitelyPresented_of_isMarkedLimit {ι : Type*} {Γ : Type u} [Group Γ]
    [IsSimpleGroup Γ] [Infinite Γ] {s : ι → Γ} {H : ℕ → Type} [∀ ℓ, Group (H ℓ)]
    {σ : ∀ ℓ, ι → H ℓ} (hfin : ∀ ℓ, Finite (H ℓ)) (hlim : IsMarkedLimit s σ) :
    ¬ Group.IsFinitelyPresented Γ :=
  not_isFinitelyPresented_of_isLEF_of_isSimpleGroup_of_infinite (isLEF_of_isMarkedLimit hfin hlim)

/-! ## A sofic example and Open problem 6.1 of Alekseev and Thom -/

/-- **Open problem 6.1 of Alekseev and Thom** (tex l.736–738) asks for a group that is finitely
presented, sofic, has property (T), and is not residually finite. Property (T) is taken at
representation-space universe `v`. -/
def IsAlekseevThomExample (Γ : Type u) [Group Γ] : Prop :=
  Group.IsFinitelyPresented Γ ∧ IsSofic Γ ∧ HasKazhdanPropertyT.{u, v} Γ ∧ ¬ IsResiduallyFinite Γ

/-- **An infinite simple finitely presented group is not LEF** (tex l.736: "A sofic example would not
be LEF"). No soficity or property (T) is needed. -/
theorem not_isLEF_of_isFinitelyPresented_of_isSimpleGroup_of_infinite {Γ : Type u} [Group Γ]
    [IsSimpleGroup Γ] [Infinite Γ] (hfp : Group.IsFinitelyPresented Γ) : ¬ IsLEF Γ := fun hLEF =>
  not_isFinitelyPresented_of_isLEF_of_isSimpleGroup_of_infinite hLEF hfp

/-- An infinite simple finitely presented sofic Kazhdan group answers Open problem 6.1 of Alekseev
and Thom (tex l.736–738). -/
theorem isAlekseevThomExample_of_isSimpleGroup {Γ : Type u} [Group Γ] [IsSimpleGroup Γ]
    [Infinite Γ] (hfp : Group.IsFinitelyPresented Γ) (hsof : IsSofic Γ)
    (hT : HasKazhdanPropertyT.{u, v} Γ) : IsAlekseevThomExample.{u, v} Γ :=
  ⟨hfp, hsof, hT, not_isResiduallyFinite_of_isSimpleGroup_of_infinite Γ⟩

/-- **The printed sentence** (tex l.731–738): let `Γ` be an infinite finitely presented simple Kazhdan
group that is sofic. Then `Γ` is not LEF, and `Γ` answers Open problem 6.1 of Alekseev and Thom. -/
theorem manuscriptSentence_soficExampleNotLEF_answersAlekseevThom (Γ : Type u) [Group Γ]
    [IsSimpleGroup Γ] [Infinite Γ] (hfp : Group.IsFinitelyPresented Γ)
    (hT : HasKazhdanPropertyT.{u, v} Γ) (hsof : IsSofic Γ) :
    ¬ IsLEF Γ ∧ IsAlekseevThomExample.{u, v} Γ :=
  ⟨not_isLEF_of_isFinitelyPresented_of_isSimpleGroup_of_infinite hfp,
    isAlekseevThomExample_of_isSimpleGroup hfp hsof hT⟩

/-! ## Closed printed forms -/

/-- `tab:props`, row "not finitely presented" (tex l.728–730), as a closed proposition: an infinite
simple LEF group is not finitely presented. -/
def PrintedInfiniteSimpleLEFNotFinitelyPresented : Prop :=
  ∀ (Γ : Type u) [Group Γ] [IsSimpleGroup Γ] [Infinite Γ], IsLEF Γ → ¬ Group.IsFinitelyPresented Γ

theorem printedInfiniteSimpleLEFNotFinitelyPresented :
    PrintedInfiniteSimpleLEFNotFinitelyPresented.{u} := by
  intro Γ _ _ _ hLEF
  exact not_isFinitelyPresented_of_isLEF_of_isSimpleGroup_of_infinite hLEF

/-- The sentence of tex l.731–738 as a closed proposition. -/
def PrintedSoficKazhdanExampleNotLEF : Prop :=
  ∀ (Γ : Type u) [Group Γ] [IsSimpleGroup Γ] [Infinite Γ], Group.IsFinitelyPresented Γ →
    HasKazhdanPropertyT.{u, v} Γ → IsSofic Γ → ¬ IsLEF Γ ∧ IsAlekseevThomExample.{u, v} Γ

theorem printedSoficKazhdanExampleNotLEF : PrintedSoficKazhdanExampleNotLEF.{u, v} := by
  intro Γ _ _ _ hfp hT hsof
  exact manuscriptSentence_soficExampleNotLEF_answersAlekseevThom Γ hfp hT hsof

end GroupApproximation.Full.SK14

#audit_axioms GroupApproximation.Full.SK14.isResiduallyFinite_of_isFinitelyPresented_of_isLEF
#audit_axioms GroupApproximation.Full.SK14.isLEF_iff_isResiduallyFinite_of_isFinitelyPresented
#audit_axioms GroupApproximation.Full.SK14.not_isFinitelyPresented_of_isMarkedLimit
#audit_axioms GroupApproximation.Full.SK14.manuscriptSentence_soficExampleNotLEF_answersAlekseevThom
#audit_closed_axioms GroupApproximation.Full.SK14.printedInfiniteSimpleLEFNotFinitelyPresented
#audit_closed_axioms GroupApproximation.Full.SK14.printedSoficKazhdanExampleNotLEF
