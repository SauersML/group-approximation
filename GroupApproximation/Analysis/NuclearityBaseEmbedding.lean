import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Sofic.LiteralNonMFLinearWitness

/-!
# The canonical map `𝓑 → E` is injective

The nonnuclearity paragraph of `non_mf_group_notes.tex` (navigate by the
anchor string "The algebra is not nuclear") opens with

> the canonical map `\mathcal B → E` is injective (Section
> `sec:literal-presentation`)

and this module proves exactly that by the route the notes name.  Section
`sec:literal-presentation` contains both ingredients: the witness homomorphism
`E → W` with its injective level-zero map `j`, and Remark
`rem:classical-base`, which identifies `\mathcal B` with the affine group.

The claim is not free.  Definition `def:E` introduces `ι : \mathcal B → E`
with the explicit warning "This map is not assumed to be injective", and every
result of the paper up to Theorem D is arranged so that it never needs to be:
the twenty base relators are used only to *impose* relations in `E`, never to
deny any.  Injectivity is a strictly extra input, and it costs the completeness
of the twenty-relator presentation.

## The route

Section `sec:literal-presentation` builds `W = \Cl(X) ⋊ Σ` and a homomorphism `E → W`
carrying the six base letters to the level-zero copy `j(\bar\Gamma)` of the
exact affine matrix group.  Compose:

    𝓑  --baseMap-->  E  --witnessHom-->  W
    𝓑  --affineQuotient-->  \bar\Gamma  --iotaAmbient-->  W

The two composites agree, because they agree on the six generators of the
presented base and a homomorphism out of a presented group is determined by
its values on generators (`PresentedGroup.ext`).  The lower route is injective
twice over:

* `LiteralBaseCompleteness.affineQuotient_injective` --- the twenty relators
  present `\bar\Gamma`, i.e. `ℤ³ ⋊ SL₃(ℤ)`.  This is Remark
  `rem:classical-base`, "the surjection `\mathcal B → \bar\Gamma` of
  Lemma `lem:linear` onto the matrix realization is an isomorphism", whose own
  badge is `LiteralBaseCompleteness.baseAffineEquiv`.  It is the expensive
  half: it consumes the Steinberg descent of `P13DescentMaster.toSL3_injective`
  on the rotation factor and the exact translation normal form on the lattice
  factor.
* `MarkedCompression.iotaAmbient_injective` --- the hooked arrow in Section
  `sec:literal-presentation`'s "let `j : \bar\Gamma ↪ Σ` be the level-zero map".  In the
  telescope this is structural: the level-zero copy survives both the direct
  limit and the adjunction of the Clifford lamps.

Injectivity of `baseMap` follows, and with it the manuscript's clause "`E`
contains an infinite Kazhdan group": the copy is `baseMap.range`.  The
nonamenability consequence is drawn in
`GroupApproximation.Analysis.NuclearityAmenability`.

Nothing here touches nuclearity; see that module for the state of Lance's
theorem.
-/

namespace GroupApproximation
namespace NuclearityBaseEmbedding

open ExplicitLinearModel LiteralNonMFPresentation MarkedCompression
open LiteralNonMFLinearWitness LiteralBaseAffineQuotient

/-- **The two routes out of the literal base agree.**  Evaluating a base word
in `E` and then in the affine--Clifford witness gives the same answer as
evaluating it in the affine matrix group and then including that at level
zero.  Both sides are homomorphisms out of a presented group, so the six
generators decide it. -/
theorem witnessHom_comp_baseMap :
    witnessHom.comp baseMap =
      (iotaAmbient alpha conjD_injective).comp affineQuotient := by
  refine PresentedGroup.ext fun i => ?_
  simp only [MonoidHom.comp_apply, witnessHom_base_generator,
    affineQuotient_generator]

/-- The pointwise form of `witnessHom_comp_baseMap`. -/
theorem witnessHom_baseMap (g : LiteralNonMFPresentation.Base) :
    witnessHom (baseMap g) =
      iotaAmbient alpha conjD_injective (affineQuotient g) :=
  DFunLike.congr_fun witnessHom_comp_baseMap g

/-- **The canonical map `\mathcal B → E` is injective**, the opening clause of
the manuscript's nonnuclearity paragraph.

Two base elements with the same image in `E` have the same image in the
affine--Clifford witness group; that image factors through the level-zero copy
of the exact affine matrix group, and both legs of the factorization are
injective. -/
theorem baseMap_injective : Function.Injective baseMap := by
  intro a b hab
  have h := congrArg witnessHom hab
  rw [witnessHom_baseMap, witnessHom_baseMap] at h
  exact LiteralBaseCompleteness.affineQuotient_injective
    (iotaAmbient_injective alpha conjD_injective h)

/-- The base copy inside `E`, as a subgroup isomorphic to the literal base.
This is the "infinite Kazhdan group" the manuscript says `E` contains. -/
noncomputable def baseCopy : LiteralNonMFPresentation.Base ≃* baseMap.range :=
  MonoidHom.ofInjective baseMap_injective

end NuclearityBaseEmbedding
end GroupApproximation
