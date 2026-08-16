import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Sofic.SimpleSoficEnvelope
import GroupApproximation.Sofic.SoficEnvelopeSimplicity

/-!
# The manuscript's simple sofic envelope, end to end

`GroupApproximation.Sofic.SimpleSoficEnvelope` proves everything the
manuscript's paragraph *A simple sofic envelope* does after its citation, for
a group `S` handed to it: the transported mark, the normality argument, the
resulting full MF radical, and the triviality of every homomorphism into an MF
group.  It does not build `S`.

`GroupApproximation.Sofic.SoficEnvelopeSimplicity` builds `S`, from the single
external input `hBNG` -- bounded normal generation of finite alternating groups,
which that module's docstring states in full and which this repository does not
prove.

This file is the composite: it feeds the concrete witness `W`
(`LiteralNonMFLinearWitness.WitnessGroup`, sofic by
`LiteralWitnessConsequences.witnessGroup_isSofic` and countable by
`CommutingLampCollapse.witnessGroup_countable`) into the envelope construction
and reads off the paragraph's displayed statement.

The whole file rests on `hBNG` and must never be cited by a `\leanverified`
badge; the reasons are in the docstring of
`GroupApproximation.Sofic.SoficEnvelopeSimplicity`, and they apply verbatim
here.  What the composite adds over that module is only that the two halves fit
together at the manuscript's own witness, with no gap between the group the
envelope construction produces and the group the radical argument consumes.
-/

namespace GroupApproximation
namespace SoficEnvelopeWitness

open SoficEnvelopeSimplicity

/-- **The manuscript's displayed statement, on the premise `hBNG`.**  There is a
countable simple sofic group `S` whose MF radical is all of `S`; equivalently,
every homomorphism from `S` into an MF group is trivial; and `S` is in
particular not MF itself.

The group produced is a subgroup of a metric ultraproduct of finite symmetric
groups, and the four conclusions are, in order, the manuscript's
`Res_MF(S) = S` in the cofinite-corona radical, the same in the ultraproduct
residual, the "equivalently" clause, and the sanity check that the statement is
not vacuous. -/
theorem manuscript_simpleSoficEnvelope
    (hBNG : ∀ δ : ℝ, 0 < δ → ∃ K M : ℕ,
      ∀ (Y : FiniteModel) (s a : Equiv.Perm Y), M ≤ Fintype.card Y →
        Equiv.Perm.sign s = 1 →
        δ * (Fintype.card Y : ℝ) ≤ ((s.support.card : ℝ)) →
        Equiv.Perm.sign a = 1 → IsBoundedConjProduct s K a) :
    ∃ (𝒰 : Ultrafilter ℕ) (X : ℕ → FiniteModel)
      (E : Subgroup (UniversalSofic 𝒰 X)),
      Countable ↥E ∧ IsSimpleGroup ↥E ∧ IsSofic ↥E ∧
        coronaMFResidual ↥E = ⊤ ∧ normMFResidual ↥E = ⊤ ∧
        (∀ (H : Type) [Group H], IsOperatorMF H →
          ∀ (φ : ↥E →* H) (s : ↥E), φ s = 1) ∧
        ¬ IsOperatorMF ↥E := by
  obtain ⟨𝒰, X, E, hEc, hEs, hEsofic, f, hf⟩ :=
    exists_countable_simple_sofic_envelope hBNG
      LiteralWitnessConsequences.witnessGroup_isSofic
  haveI : Countable ↥E := hEc
  haveI : IsSimpleGroup ↥E := hEs
  obtain ⟨hcorona, hnorm, htrivial, hnotMF⟩ :=
    SimpleSoficEnvelope.simpleEnvelope_of_witnessEmbedding f hf
  exact ⟨𝒰, X, E, hEc, hEs, hEsofic, hcorona, hnorm, htrivial, hnotMF⟩

end SoficEnvelopeWitness
end GroupApproximation
