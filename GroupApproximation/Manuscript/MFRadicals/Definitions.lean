import GroupApproximation.Sofic.ActualCoronaMFRadical

/-!
# The MF radical and its universal quotient

The manuscript namespace is a thin layer: every declaration under
`Manuscript/MFRadicals` is a *statement wrapper*, so that the theorem printed
in the paper is literally the type of one Lean declaration and the proof is a
reference to the implementation module that carries it.  No mathematics is done
here.

This file fixes the two definitions the paper opens with — the MF radical and
its quotient — and records the universal property.

`Res_MF(G) = ⋂_ρ ker ρ`, the intersection taken over every representation of
`G` into the unitary group of a genuine matrix C\*-corona
(`actualCoronaMFResidual`).  Its quotient is MF, and every homomorphism to an
MF group factors through it uniquely.

## A note on the audit gate

`#audit_closed_axioms` rejects a declaration whose type begins with a
caller-supplied binder, deliberately without unfolding a named proposition.
A genuinely universal theorem — "for every countable group, ..." — therefore has
to be advertised through a named `Prop` like `UniversalMFQuotient` below.  That
is not a way around the gate: the binders live *inside* the proposition, so the
statement is closed, and nothing is accepted as construction data from a caller.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

/-- Quotients of countable groups are countable; mirrored locally, as in the
implementation modules where the same instance is `local`. -/
local instance quotientCountable {G : Type*} [Group G] (N : Subgroup G)
    [hN : N.Normal] [Countable G] : Countable (G ⧸ N) :=
  Function.Surjective.countable (@QuotientGroup.mk'_surjective G _ N hN)

/-- **The universal MF-visible quotient.**  For every countable group the
quotient by the MF radical is MF, and every homomorphism into a countable MF
group factors through it uniquely. -/
def UniversalMFQuotient : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsCDEOperatorMF (G ⧸ actualCoronaMFResidual G) ∧
      ∀ (H : Type) [Group H] [Countable H] (f : G →* H), IsCDEOperatorMF H →
        ∃! fBar : (G ⧸ actualCoronaMFResidual G) →* H,
          fBar.comp (QuotientGroup.mk' (actualCoronaMFResidual G)) = f

theorem manuscriptUniversalMFQuotient : UniversalMFQuotient := by
  intro G _ _
  refine ⟨actualCoronaMFQuotient_isCDEOperatorMF, ?_⟩
  intro H _ _ f hH
  exact existsUnique_actualCoronaMFQuotient_factorization_to_isCDEOperatorMF f hH

/-- **A group is MF exactly when its MF radical is trivial.** -/
def MFIffRadicalTrivial : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsCDEOperatorMF G ↔ actualCoronaMFResidual G = ⊥

theorem manuscriptMFIffRadicalTrivial : MFIffRadicalTrivial := by
  intro G _ _
  exact isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot

end MFRadicals
end Manuscript
end GroupApproximation
