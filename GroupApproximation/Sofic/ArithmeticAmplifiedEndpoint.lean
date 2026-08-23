import GroupApproximation.Sofic.PushedDefectSaturation
import GroupApproximation.Sofic.ArithmeticSingleDefectEndpoint
import GroupApproximation.Sofic.LiteralAffineFreeProductSource

/-!
# The arithmetic single-defect obligation, at its weakest statement

`ArithmeticSingleDefectEndpoint` states the arithmetic construction over
`SingleDefectSaturation.SingleDefectRouterData`, whose `quotient_surjective`
field `Sofic/PushedDefectSaturation` has since shown to be unnecessary.  This
file restates the endpoint over the weaker `SaturatingRouterData`, and then
settles a question the older statement left ambiguous: whether the free-product
amplification `E ↦ E * ℤ` changes the routing obligation.

It does not.  `saturatingRouterData_envelope_of_ambient` and
`saturatingRouterData_ambient_of_envelope` are inverse-shaped transports, so a
router for the amplified source and a router for the bare HNN envelope are
interchangeable.  Forwards is precomposition with the free-factor embedding;
backwards is `Monoid.Coprod.lift` against the trivial map on the second factor.
Both directions rest on `markedCommutator_mapAmbient`: the amplified marked
commutator is the free-factor image of the envelope's own, so the normal closure
condition reads the same element on both sides.

The consequence is that the amplification is **routing-neutral**.  It was
introduced to make the routing map surjective onto a group with a Bass--Serre
action, and once surjectivity is not asked for, nothing is left to choose
between the two sources.  A construction may work with whichever is convenient.

## What is still a hypothesis

`SaturatingRouterData` is not constructed here or anywhere.  Every theorem below
carries `_of_saturatingRouter` in its name and none may be cited as an
unconditional existence theorem.  Producing an inhabitant is the small
cancellation step, and the repository's own route to it
(`SmallCancellationRouter` and the `Greendlinger*` lane) bottoms out in leaves
that are open; no literature is imported to stand in for them.
-/

namespace GroupApproximation

open scoped commutatorElement

namespace BareDefectSourceData

universe u v

variable {P : Type} {E : Type u} [Group P] [Group E]

/-- **The marked commutator transports along an injective ambient map.**  The
same computation as `markedCommutator_pushAmbient`, at the injective transport
that the amplified arithmetic source is built with. -/
theorem markedCommutator_mapAmbient (D : BareDefectSourceData P E)
    {F : Type v} [Group F] (f : E →* F) (hf : Function.Injective f) :
    SingleDefectSaturation.markedCommutator (D.mapAmbient f hf) =
      f (SingleDefectSaturation.markedCommutator D) := by
  rw [SingleDefectSaturation.markedCommutator_eq,
    SingleDefectSaturation.markedCommutator_eq, map_commutatorElement]
  rfl

end BareDefectSourceData

namespace ArithmeticAmplifiedEndpoint

open LiteralAffineCongruenceBase
open LiteralAffineCongruenceSource
open LiteralAffineFreeProductSource
open SingleDefectSaturation
open PushedDefectSaturation

noncomputable section

/-! ## 1.  The two sources -/

/-- The bare arithmetic source: `ℤ³ ⋊ Γ(3)` compressed by translation doubling,
inside its HNN envelope. -/
abbrev envelopeSource : BareDefectSourceData P Envelope :=
  literalBareDefectSourceData

/-- The same source pushed into the free product `Envelope * ℤ`. -/
abbrev ambientSource : BareDefectSourceData P Ambient :=
  amplifiedDefectData

/-- The amplified marked commutator is the free-factor image of the envelope's
own marked commutator. -/
theorem markedCommutator_ambient :
    markedCommutator ambientSource = envelopeEmbedding
      (markedCommutator envelopeSource) :=
  BareDefectSourceData.markedCommutator_mapAmbient envelopeSource
    envelopeEmbedding envelopeEmbedding_injective

/-! ## 2.  The amplification is routing-neutral -/

/-- **A router for the free product gives one for the envelope.**  Precompose
with the free-factor embedding.  The marked element is unchanged by
`markedCommutator_ambient`, so the saturation clause transports verbatim; no
other field mentions the source at all. -/
def saturatingRouterData_envelope_of_ambient
    (R : SaturatingRouterData.{0} ambientSource) :
    SaturatingRouterData.{0} envelopeSource :=
  letI : Group R.Quotient := R.groupQuotient
  letI : Nontrivial R.Quotient := R.nontrivial
  letI : Group.IsFinitelyPresented R.Quotient := R.finitelyPresented
  { Quotient := R.Quotient
    quotient := R.quotient.comp envelopeEmbedding
    kazhdan := R.kazhdan
    torsionFree := R.torsionFree
    generatorOne := R.generatorOne
    generatorTwo := R.generatorTwo
    generates := R.generates
    saturates := by
      have h := R.saturates
      rw [markedCommutator_ambient] at h
      exact h }

/-- **A router for the envelope gives one for the free product.**  Extend the
map by `Monoid.Coprod.lift` against the trivial homomorphism on the second free
factor; the extension agrees with the original on the embedded envelope, which
is where the marked element lives.

Nothing is asked of the second factor, which is the point: the amplification
adds a free factor that the obligation never reads. -/
def saturatingRouterData_ambient_of_envelope
    (R : SaturatingRouterData.{0} envelopeSource) :
    SaturatingRouterData.{0} ambientSource :=
  letI : Group R.Quotient := R.groupQuotient
  letI : Nontrivial R.Quotient := R.nontrivial
  letI : Group.IsFinitelyPresented R.Quotient := R.finitelyPresented
  { Quotient := R.Quotient
    quotient := Monoid.Coprod.lift R.quotient 1
    kazhdan := R.kazhdan
    torsionFree := R.torsionFree
    generatorOne := R.generatorOne
    generatorTwo := R.generatorTwo
    generates := R.generates
    saturates := by
      have h := R.saturates
      rw [markedCommutator_ambient]
      show Subgroup.normalClosure
        ({Monoid.Coprod.lift R.quotient 1
          (envelopeEmbedding (markedCommutator envelopeSource))}
            : Set R.Quotient) = ⊤
      rwa [envelopeEmbedding, Monoid.Coprod.lift_apply_inl] }

/-- **The obligation is the same on both sources.**  Two transports in opposite
directions: the free-product amplification neither strengthens nor weakens what
a router has to do. -/
theorem nonempty_saturatingRouterData_ambient_iff_envelope :
    Nonempty (SaturatingRouterData.{0} ambientSource) ↔
      Nonempty (SaturatingRouterData.{0} envelopeSource) :=
  ⟨fun ⟨R⟩ => ⟨saturatingRouterData_envelope_of_ambient R⟩,
    fun ⟨R⟩ => ⟨saturatingRouterData_ambient_of_envelope R⟩⟩

/-! ## 3.  The endpoint, over the weakest interface -/

/-- **The arithmetic construction from a saturating router at the envelope.**

Everything except the router is discharged inside Lean: the source is the
concrete arithmetic one, its property `(T)` and torsion-freeness are proved, the
marked commutator is nontrivial by Britton's lemma, and
`PushedDefectSaturation` upgrades that single element to the whole compression
defect with no surjectivity assumption anywhere.

The router is a hypothesis and is not constructed here. -/
theorem exists_twoGenerated_torsionFree_fullMFRadical_of_saturatingRouter
    (h : Nonempty (SaturatingRouterData.{0} envelopeSource)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsTwoGenerated Q ∧
      Group.IsFinitelyPresented Q ∧
      IsPowerTorsionFree Q ∧
      HasKazhdanPropertyT.{0, 0} Q ∧
      Nontrivial Q ∧
      cdeMFResidual Q = ⊤ :=
  exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical_of_saturatingRouter
    h

/-- The same conclusion from a saturating router at the amplified source,
through the transport. -/
theorem exists_twoGenerated_torsionFree_fullMFRadical_of_amplifiedSaturatingRouter
    (h : Nonempty (SaturatingRouterData.{0} ambientSource)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsTwoGenerated Q ∧
      Group.IsFinitelyPresented Q ∧
      IsPowerTorsionFree Q ∧
      HasKazhdanPropertyT.{0, 0} Q ∧
      Nontrivial Q ∧
      cdeMFResidual Q = ⊤ :=
  exists_twoGenerated_torsionFree_fullMFRadical_of_saturatingRouter
    (nonempty_saturatingRouterData_ambient_iff_envelope.mp h)

/-- **The older interface is subsumed.**  A `SingleDefectRouterData` at the
arithmetic source produces a `SaturatingRouterData` at it, so every consequence
of the older hypothesis is a consequence of the weaker one. -/
def saturatingRouterData_of_singleDefectRouter
    (R : SingleDefectRouterData.{0} envelopeSource) :
    SaturatingRouterData.{0} envelopeSource :=
  PushedDefectSaturation.SingleDefectRouterData.toSaturatingRouterData R

end

end ArithmeticAmplifiedEndpoint
end GroupApproximation
