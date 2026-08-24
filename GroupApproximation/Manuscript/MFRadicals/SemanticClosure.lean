import GroupApproximation.Sofic.MFRelationClosure

/-!
# Theorem E: MF semantic closure

Imposing relations on a group and then asking what MF approximation still sees
is a closure operator.  For `N ⊴ G` put

  `Cl_MF(N) = q_N⁻¹ (Res_MF(G/N))`.

It is extensive, monotone and idempotent; its fixed points are exactly the
relations whose quotient is MF; and the quotient by any closure is MF.  On top
of it sits the saturation calculus `IsSoundIterate`: everything soundly
deducible from the imposed relations already lies in the MF radical, and if the
sound deductions reach the whole group then the radical *is* the whole group.

This is what makes the full-radical constructions of `FullRadical` and
`SimpleSofic` instances of a theory rather than isolated examples: they are the
extreme case `Cl_MF(1) = G`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

/-- Quotients of countable groups are countable; mirrored locally, as in the
implementation modules where the same instance is `local`. -/
local instance quotientCountable {G : Type*} [Group G] (N : Subgroup G)
    [hN : N.Normal] [Countable G] : Countable (G ⧸ N) :=
  Function.Surjective.countable (@QuotientGroup.mk'_surjective G _ N hN)

/-- **Theorem E.**  `Cl_MF` is a closure operator on normal subgroups whose
fixed points are exactly the relations with MF quotient. -/
def MFSemanticClosure : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (N : Subgroup G) [N.Normal],
    N ≤ actualCoronaMFClosure N ∧
      (∀ (M : Subgroup G) [M.Normal], N ≤ M →
        actualCoronaMFClosure N ≤ actualCoronaMFClosure M) ∧
      actualCoronaMFClosure (actualCoronaMFClosure N) =
        actualCoronaMFClosure N ∧
      (actualCoronaMFClosure N = N ↔ IsCDEOperatorMF (G ⧸ N)) ∧
      IsCDEOperatorMF (G ⧸ actualCoronaMFClosure N)

theorem manuscriptSemanticClosure : MFSemanticClosure := by
  intro G _ _ N _
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := manuscriptRelationClosure G N
  exact ⟨h1, h3, h4, h5, h6⟩

/-- **The saturation calculus.**  Sound deductions from the imposed relations
stay inside the MF radical, and a full sound iterate saturates it. -/
def MFSoundSaturation : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    (∀ N : Subgroup G, IsSoundIterate N → N ≤ actualCoronaMFResidual G) ∧
      (IsSoundIterate (⊤ : Subgroup G) → actualCoronaMFResidual G = ⊤)

theorem manuscriptSoundSaturation : MFSoundSaturation := by
  intro G _ _
  refine ⟨fun N h => h.le_actualCoronaMFResidual, fun h => ?_⟩
  obtain ⟨-, -, h3⟩ := manuscriptSoundIterationClosure G
  rw [← manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  exact h3 h

end MFRadicals
end Manuscript
end GroupApproximation
