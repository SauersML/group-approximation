import GroupApproximation.Sofic.HyperlinearResidualDetector
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.RadicalSeparation
import GroupApproximation.Sofic.SoficTransfer

/-!
# Separating the approximation radicals on the literal group

The literal eight-generator forty-one-relator group `E` of
`LiteralNonMFPresentation` carries three approximation radicals: the elements
killed by every homomorphism to a sofic group, to a hyperlinear group, and to
a norm-matrix corona.  This file establishes the half of their comparison that
is unconditional.

## What is proved here

Two general facts, and the MF side of the literal computation.

A group detects its own radical: the identity homomorphism is a homomorphism
to a sofic group as soon as the group is sofic, so a sofic group has trivial
sofic radical, and likewise for hyperlinear.  Neither statement mentions the
literal group.

For `E` itself the MF radical is *not* trivial.  The marked central
involution `w` is nontrivial (`LiteralNonMFLinearWitness.literal_mark_ne_one`)
and is killed by every genuine norm-matrix C-star-corona representation
(`LiteralNonMFEndpoint.literal_mark_eq_one_in_CStarCorona`), so it is a
nonidentity element of the radical exactly as the manuscript prints it.  With
`E` finitely presented and not operator MF, this gives

```text
  1 < Res_MF(E)
```

on a single finitely presented group, unconditionally.

## What is missing, and the exact shape of the missing step

The separation the construction is aiming at is

```text
  Rad_sof(E) = Rad_hyp(E) = 1 < Res_MF(E),
```

whose left-hand equalities need `IsSofic MarkedGroup`.  That is not proved
anywhere in this development yet, so it is not asserted here, in any form:
there is deliberately no hypothesis-bearing package taking soficity of `E` as
an input and returning the separation, since such a statement assumes the
half that is open.

Soficity of `E` is expected to arrive by transporting a block-model tower
across the normal form.  When the block lane lands, the whole of the missing
step is a single application of `isSofic_mulEquiv_iff` to an isomorphism
`MarkedGroup ≃* LiteralBlockModel.Model` and soficity of that model, taken in
the direction that reads soficity back along the isomorphism -- the shape
`CommutingLampQuotientSofic.isSofic_signFreeQuotient` already uses.  Both of
its inputs must be closed sentences; a hypothesis surviving on either would
propagate to every consequence below.

Given that one term, `soficResidual_eq_bot_of_isSofic` and
`hyperlinearResidual_eq_bot_of_isHyperlinear` turn it into the two left-hand
equalities with no further work, and
`markedGroup_bot_lt_manuscriptCoronaMFResidual` supplies the strict
inequality on the right.
-/

namespace GroupApproximation
namespace LiteralSoficSeparation

open LiteralNonMFPresentation

/-! ## A group detects its own radical

Both statements are closed sentences about arbitrary groups. -/

/-- Closed proposition: a sofic group has trivial sofic radical. -/
def SoficRadicalTrivialInSoficGroups : Prop :=
  ∀ (G : Type) [Group G], IsSofic G → soficResidual G = ⊥

/-- Closed proposition: a hyperlinear group has trivial hyperlinear
radical. -/
def HyperlinearRadicalTrivialInHyperlinearGroups : Prop :=
  ∀ (G : Type) [Group G], IsHyperlinear G → hyperlinearResidual G = ⊥

/-- **A sofic group is its own detector.**  The identity is a homomorphism
into a sofic target, so it kills the sofic radical, so the radical is
trivial. -/
theorem soficResidual_eq_bot_of_isSofic : SoficRadicalTrivialInSoficGroups := by
  intro G _ hG
  refine le_antisymm ?_ bot_le
  intro x hx
  have hx1 : (MonoidHom.id G) x = 1 :=
    (mem_soficResidual_iff.mp hx) G inferInstance hG (MonoidHom.id G)
  simpa using hx1

/-- **A hyperlinear group is its own detector.** -/
theorem hyperlinearResidual_eq_bot_of_isHyperlinear :
    HyperlinearRadicalTrivialInHyperlinearGroups := by
  intro G _ hG
  refine le_antisymm ?_ bot_le
  intro x hx
  have hx1 : (MonoidHom.id G) x = 1 :=
    (mem_hyperlinearResidual_iff.mp hx) G inferInstance hG (MonoidHom.id G)
  simpa using hx1

/-! ## The MF radical of the literal group is nontrivial -/

/-- The marked central involution is a nonidentity element of the MF radical
of the literal group, in the manuscript's own natural-dimension
coordinates. -/
theorem markedGroup_mark_mem_manuscriptCoronaMFResidual_and_ne_one :
    mark ∈ manuscriptCoronaMFResidual MarkedGroup ∧ mark ≠ 1 :=
  ⟨LiteralNonMFEndpoint.literal_mark_mem_manuscriptCoronaMFResidual,
    LiteralNonMFLinearWitness.literal_mark_ne_one⟩

/-- **The MF radical of the literal group is nontrivial.** -/
theorem markedGroup_manuscriptCoronaMFResidual_ne_bot :
    manuscriptCoronaMFResidual MarkedGroup ≠ ⊥ := by
  intro hbot
  have hmem : mark ∈ manuscriptCoronaMFResidual MarkedGroup :=
    LiteralNonMFEndpoint.literal_mark_mem_manuscriptCoronaMFResidual
  rw [hbot] at hmem
  exact LiteralNonMFLinearWitness.literal_mark_ne_one (Subgroup.mem_bot.mp hmem)

/-- The same nontriviality for the basis-free unitary-sequence radical. -/
theorem markedGroup_normMFResidual_ne_bot :
    normMFResidual MarkedGroup ≠ ⊥ := by
  intro hbot
  have hmem : mark ∈ normMFResidual MarkedGroup :=
    mem_normMFResidual_iff.mpr LiteralNonMFEndpoint.literal_mark_normMFInvisible
  rw [hbot] at hmem
  exact LiteralNonMFLinearWitness.literal_mark_ne_one (Subgroup.mem_bot.mp hmem)

/-- The strict inequality on the right of the intended separation.  This is
the form that composes with a triviality theorem for the sofic radical. -/
theorem markedGroup_bot_lt_manuscriptCoronaMFResidual :
    (⊥ : Subgroup MarkedGroup) < manuscriptCoronaMFResidual MarkedGroup :=
  bot_lt_iff_ne_bot.mpr markedGroup_manuscriptCoronaMFResidual_ne_bot

/-! ## The closed half of the separation -/

/-- **What the literal group is known to be, unconditionally.**  It is
finitely presented, it is not operator MF, and its MF radical is nontrivial
with the marked central involution as an explicit witness.

The sofic and hyperlinear radicals of this same group are not addressed: that
requires soficity of `E`, which this statement does not use and which is
established elsewhere in the development. -/
theorem literal_finitelyPresented_nonMF_nontrivialMFRadical :
    Group.IsFinitelyPresented MarkedGroup ∧
      ¬ IsOperatorMF MarkedGroup ∧
      mark ≠ 1 ∧
      mark ∈ manuscriptCoronaMFResidual MarkedGroup ∧
      manuscriptCoronaMFResidual MarkedGroup ≠ ⊥ :=
  ⟨inferInstance,
    LiteralNonMFEndpoint.literal_not_isOperatorMF,
    LiteralNonMFLinearWitness.literal_mark_ne_one,
    LiteralNonMFEndpoint.literal_mark_mem_manuscriptCoronaMFResidual,
    markedGroup_manuscriptCoronaMFResidual_ne_bot⟩

end LiteralSoficSeparation
end GroupApproximation
