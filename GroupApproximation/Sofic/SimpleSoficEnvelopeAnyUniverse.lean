import GroupApproximation.Sofic.SimpleSoficEnvelope
import GroupApproximation.Sofic.Type0Transfer
import GroupApproximation.Sofic.CommensurabilityInvariance

/-!
# The displayed equivalence of `p:E-simple`, at any universe

The paragraph prints

> equivalently, for a countable group the residual is everything exactly when
> every homomorphism into an MF group is trivial.

Ledger row `SO.18b` grades the statement MISMATCH and its note is exact about
why: "`univ0` is the whole of the MISMATCH: the iff is stated at
`{S : Type} [Countable S]` while the print quantifies over no universe at all.
The print does say *countable*, so this is the transfer-closable kind rather
than a real narrowing."  This file does that transfer, on both sides.

## Two universes, two different arguments

The source group and the target group are narrowed for different reasons and
they come back by different routes.

*The source.*  `coronaMFResidual` is already universe-polymorphic — a corona
representation lands in `NormMatrixCoronaUnitary X`, which does not depend on
the source at all — so the only obstacle is that the Type-0 theorem is stated at
`Type`.  Property `Countable` gives a `Type 0` model, and
`coronaMFResidual_eq_top_congr` moves the hypothesis and the conclusion across
it.  That transport is the content: invisibility is preserved in both directions
because a representation of one group precomposes with the isomorphism to give
one of the other.

*The target.*  Here the narrowing is real and `ULift` is what removes it.  The
converse direction proves `Res = ⊤` by testing against `rho.range`, which lives
at `Type 0`; a hypothesis quantified over `Type w` cannot be applied there
directly.  Lifting the range and transporting `IsOperatorMF` along
`MulEquiv.ulift` supplies the instance at the right universe, and injectivity of
the lift brings the conclusion back.
-/

namespace GroupApproximation
namespace SimpleSoficEnvelopeAnyUniverse

open SimpleSoficEnvelope

universe v w

/-- **Invisibility transports along an isomorphism.**  A corona representation
of one group precomposes with the isomorphism to give one of the other, and the
value at the transported element is the transported value. -/
theorem coronaMFInvisible_congr {S : Type v} [Group S] {T : Type w} [Group T]
    (e : S ≃* T) {x : S} (hx : CoronaMFInvisible x) :
    CoronaMFInvisible (e x) := by
  intro X hX rho
  have h := hx X hX (rho.comp e.toMonoidHom)
  simpa using h

/-- **The residual being everything transports along an isomorphism.** -/
theorem coronaMFResidual_eq_top_congr {S : Type v} [Group S] {T : Type w}
    [Group T] (e : S ≃* T) (h : coronaMFResidual S = ⊤) :
    coronaMFResidual T = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro y
  have hx : CoronaMFInvisible (e.symm y) := by
    have hmem : e.symm y ∈ coronaMFResidual S := by rw [h]; trivial
    exact hmem
  have := coronaMFInvisible_congr e hx
  rw [MulEquiv.apply_symm_apply] at this
  exact this

/-- **`SO.18b`, at any universe on both sides.**

> for a countable group the residual is everything exactly when every
> homomorphism into an MF group is trivial.

The source group is at an arbitrary universe, with the printed countability as
the only hypothesis, and the target group is quantified over an arbitrary
universe too.  Neither narrowing survives. -/
theorem coronaMFResidual_eq_top_iff_forall_map_eq_one_anyUniverse
    {S : Type v} [Group S] [Countable S] :
    coronaMFResidual S = ⊤ ↔
      ∀ (H : Type w) [Group H], IsOperatorMF H → ∀ (φ : S →* H) (s : S), φ s = 1 := by
  obtain ⟨S₀, _groupS₀, ⟨e⟩⟩ := Type0Transfer.exists_type0_model S
  haveI : Countable S₀ := Type0Transfer.countable_type0_model S e
  constructor
  · intro htop H _ hH φ s
    have htop₀ : coronaMFResidual S₀ = ⊤ := coronaMFResidual_eq_top_congr e htop
    have := map_eq_one_of_coronaMFResidual_eq_top htop₀ hH
      (φ.comp e.symm.toMonoidHom) (e s)
    simpa using this
  · intro hall
    refine coronaMFResidual_eq_top_congr e.symm ?_
    rw [Subgroup.eq_top_iff']
    intro x
    show CoronaMFInvisible x
    intro X hX rho
    have hMFrange : IsOperatorMF rho.range :=
      ⟨X, hX, rho.range.subtype, Subtype.val_injective⟩
    -- The hypothesis is stated at `Type w`; the range lives at `Type 0`.  Lift
    -- it, move `IsOperatorMF` across the lift, and bring the conclusion back by
    -- injectivity.
    have hMFlift : IsOperatorMF (ULift.{w} rho.range) :=
      CommensurabilityInvariance.isOperatorMF_of_mulEquiv
        (MulEquiv.ulift (α := (rho.range : Type))).symm hMFrange
    -- `hall` speaks about homomorphisms out of `S`, and the goal after the
    -- transport is about `S₀`, so the test map is precomposed with `e`.
    have hone := hall (ULift.{w} rho.range) hMFlift
      (((MulEquiv.ulift (α := (rho.range : Type))).symm.toMonoidHom.comp
        rho.rangeRestrict).comp e.toMonoidHom) (e.symm x)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] at hone
    have hres : rho.rangeRestrict x = 1 := by
      have := congrArg (MulEquiv.ulift (α := (rho.range : Type))) hone
      simpa using this
    simpa using congrArg Subtype.val hres

end SimpleSoficEnvelopeAnyUniverse
end GroupApproximation
