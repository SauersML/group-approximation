import GroupApproximation.Sofic.MFCamouflageConsequences

/-!
# The printed one-word quotient test

`non_mf_groups_exist.tex`, closing paragraph of
`\section{MF-visible quotients}`:

> Taking `Q = ℤ` makes the quotient criterion especially concrete: for every
> normal subgroup `N ⊴ W_ℤ`, `W_ℤ/N` is MF if and only if `d ∈ N`.
> Indeed, every quotient of `ℤ` is MF, while `ker π_ℤ = ⟪d⟫`.

`Sofic/MFCamouflageConsequences.lean` proves the classification for a general
visible group all of whose quotients are MF; `Sofic/MFCamouflage.lean` proves
the kernel identity.  Both take the ambient group, the distinguished element
and the relation subgroup as caller-supplied binders, so
`#audit_closed_axioms` -- which throws on any leading binder -- cannot be
applied to them.  The two declarations below restate the printed display and
its printed justification with every quantifier inside the statement.

No theorem from the literature is an input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

noncomputable section

/-- The quotient of a countable group is countable.  The same local instance
carries the corresponding statements in `Sofic/ActualCoronaMFRadical.lean`. -/
local instance quotientGroupCountable {G : Type*} [Group G] (N : Subgroup G)
    [hN : N.Normal] [Countable G] :
    Countable (G ⧸ N) :=
  Function.Surjective.countable (@QuotientGroup.mk'_surjective G _ N hN)

/-- The visible group of the printed specialization is `ℤ`, written
multiplicatively.  `Sofic/MFCamouflageConsequences.lean` installs the same
instance locally; the countability of the camouflage group itself is the
global `MFCamouflage.instCountable`. -/
local instance multiplicativeIntCountable : Countable (Multiplicative ℤ) :=
  Countable.of_equiv ℤ Multiplicative.toAdd

/-- **`eq:one-word-quotient-test`.**  With the visible group taken to be `ℤ`,
a quotient of the camouflage group `W_ℤ` is MF exactly when the relation
subgroup contains the single distinguished defect `d` -- whatever else it
contains.  The manuscript's standing hypotheses on the hidden vertex (its MF
radical is everything, and `d` normally generates it) appear here as
hypotheses of the sentence rather than in front of it. -/
def PrintedOneWordQuotientTest : Prop :=
  ∀ (B : Type) [Group B] [Countable B] (d : B),
    actualCoronaMFResidual B = ⊤ →
    Subgroup.normalClosure ({d} : Set B) = ⊤ →
      ∀ (N : Subgroup (MFCamouflage.Camouflage d (Multiplicative ℤ)))
        (hN : N.Normal),
        letI := hN
        (IsCDEOperatorMF (MFCamouflage.Camouflage d (Multiplicative ℤ) ⧸ N) ↔
          MFCamouflage.defect d (Multiplicative ℤ) ∈ N)

/-- Closed proof of the printed one-word quotient test. -/
theorem manuscriptPrintedOneWordQuotientTest : PrintedOneWordQuotientTest := by
  intro B _ _ d hfull hgen N hN
  letI := hN
  exact MFCamouflage.quotient_isCDEOperatorMF_iff_defect_mem d (Multiplicative ℤ)
    hfull hgen MFCamouflage.multiplicativeInt_quotient_isCDEOperatorMF N

/-- **The printed justification of the one-word test**, both halves: every
quotient of `ℤ` is MF, and the kernel of the projection is the normal closure
of the single defect. -/
def PrintedOneWordQuotientJustification : Prop :=
  (∀ (M : Subgroup (Multiplicative ℤ)) (hM : M.Normal),
      letI := hM
      IsCDEOperatorMF (Multiplicative ℤ ⧸ M)) ∧
    ∀ (B : Type) [Group B] (d : B),
      Subgroup.normalClosure ({d} : Set B) = ⊤ →
        (MFCamouflage.projection d (Multiplicative ℤ)).ker =
          Subgroup.normalClosure
            ({MFCamouflage.defect d (Multiplicative ℤ)} :
              Set (MFCamouflage.Camouflage d (Multiplicative ℤ)))

/-- Closed proof of both printed justification clauses. -/
theorem manuscriptPrintedOneWordQuotientJustification :
    PrintedOneWordQuotientJustification := by
  constructor
  · intro M hM
    letI := hM
    exact MFCamouflage.multiplicativeInt_quotient_isCDEOperatorMF M
  · intro B _ d hgen
    exact MFCamouflage.projection_ker_eq_normalClosure d (Multiplicative ℤ) hgen

/-- The printed display together with its printed justification. -/
def PrintedOneWordQuotientParagraph : Prop :=
  PrintedOneWordQuotientTest ∧ PrintedOneWordQuotientJustification

/-- Closed proof of the complete printed paragraph. -/
theorem manuscriptPrintedOneWordQuotientParagraph :
    PrintedOneWordQuotientParagraph :=
  ⟨manuscriptPrintedOneWordQuotientTest,
    manuscriptPrintedOneWordQuotientJustification⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
