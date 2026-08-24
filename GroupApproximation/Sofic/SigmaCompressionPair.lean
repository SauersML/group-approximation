import GroupApproximation.Sofic.SymmetricDoubleShulman
import GroupApproximation.Sofic.DoubleFiniteDimensionalRigidity

/-!
# The literal pair is a compression pair, and what that forbids the models

`Sofic/SymmetricDoubleShulman` reduces the manuscript's exact MF-radical
computation to one finite-matrix statement,
`MFTraceRecognition.IsMFRegularCharacter (SymmetricDouble SigmaGroup sigmaBase)`:
a bound `B` chosen once, and then for each finite `F` and each `ε > 0` one
finite index type with matrices that are `ε`-multiplicative on `F`,
`ε`-adjoint-compatible on `F`, and `ε`-correct in normalized trace at `1` and
away from `1`.

This file settles how much of that can be done exactly.  The answer is none of
it, and the reason is now a theorem about the literal pair rather than about
finite groups.

## `(Σ, B)` is a compression pair

`Sofic/InfranormalCompressionPair.IsCompressionPair` asks for two things:
`B` is infranormal in `Σ` -- its compressors generate -- and `B` is not normal.
Both hold, and both are short:

* `sigmaStable_mem_compressionSubmonoid` -- the stable letter compresses the
  base copy, because that is literally the ascending-HNN relation
  `t b t⁻¹ = α(b)` of `MarkedCompression.vertical_compress`;
* `sigmaBase_isInfranormal` -- `B` and `t` therefore all lie in the closure of
  the compressors, and `MarkedCompression.vertical_mem_subgroup_of_iota_mem_of_t_mem`
  says those two generate the telescope model;
* `sigmaBase_not_normal` is already in `Sofic/SymmetricDoubleShulman`, from the
  escape element `s = t⁻¹ v₁ t`.

So `sigmaBase_isCompressionPair`.  Until now every endpoint of the
Kun--Thom/Shulman double construction was stated for an abstract compression
pair; this is the first time the literal pair is shown to be one, so all of
them now apply to `Σ *_B Σ` itself.

## What that forbids

`Sofic/DoubleFiniteDimensionalRigidity` proves that every finite-dimensional
representation of the double of a compression pair kills the Bass--Serre
witness, over *any* field.  Instantiated at the literal pair:

* `sigmaDoubleWitness` is the witness, `sigmaDoubleWitness_ne_one` says it is
  not trivial, and `fdRep_sigmaDoubleWitness_eq_one` says every
  finite-dimensional representation sends it to the identity;
* `symmetricDouble_no_faithful_fdRep_sigma` -- `Σ *_B Σ` has no faithful
  finite-dimensional representation over any field;
* `matrixHom_sigmaDoubleWitness_eq_one` -- carried to matrices: *every* group
  homomorphism `Σ *_B Σ →* M_Y(ℂ)` sends the witness to `1`.  The bridge is the
  left regular action, `Matrix.toLinAlgEquiv'` followed by
  `MonoidHom.toHomUnits` and `LinearMap.GeneralLinearGroup.generalLinearEquiv`;
* `regularCharacterModel_not_multiplicative` -- the consequence for the target.
  No `RegularCharacterModel` whose test set contains the witness, at any
  accuracy below `1`, can have its map be an exact unital homomorphism.  Its
  normalized trace at the witness would be exactly `1`, and the clause
  `trace_correct_ne` asks for at most `ε`.

## Why this is the useful negative

`Sofic/SymmetricDoubleMF` already closed the exact routes, but through *finite
groups*: `B` is not separable in `Σ`, so the amalgam is not residually finite
and not `LEF`.  That leaves open, formally, every model built from a
finite-dimensional representation with infinite image.  The statements above
close that too, over every field and with no separability input.

The multiplicativity defect in `IsMFRegularCharacter` is therefore not a
technical slack that a sharper construction could drive to zero.  It has to be
strictly positive at every model whose test set reaches the witness.  A proof of
the target must produce maps that are provably *not* homomorphisms and are not
perturbations of homomorphisms, which is what freeness with amalgamation over
`C⋆(B)` produces and what nothing in this repository produces.
-/

namespace GroupApproximation
namespace TerminalQuotientPresentation

open MarkedCompression ExplicitLinearModel LiteralNonMFLinearWitness

noncomputable section

/-! ## The compressors of `B` generate `Σ` -/

/-- **The stable letter compresses the base copy.**  This is the
ascending-HNN relation `t b t⁻¹ = α(b)` of `MarkedCompression.vertical_compress`
read as a statement about the compression semigroup. -/
theorem sigmaStable_mem_compressionSubmonoid :
    tVertical alpha conjD_injective ∈ compressionSubmonoid sigmaBase := by
  intro g hg
  obtain ⟨x, hx⟩ := hg
  refine ⟨alpha x, ?_⟩
  rw [← hx]
  exact (vertical_compress alpha conjD_injective x).symm

/-- **`B` is infranormal in `Σ`.**  The base copy compresses itself and the
stable letter compresses it, and those two generate the telescope model. -/
theorem sigmaBase_isInfranormal : IsInfranormal sigmaBase := by
  show Subgroup.closure (compressionSubmonoid sigmaBase : Set SigmaGroup) = ⊤
  rw [Subgroup.eq_top_iff']
  intro v
  exact vertical_mem_subgroup_of_iota_mem_of_t_mem alpha conjD_injective
    (Subgroup.closure (compressionSubmonoid sigmaBase : Set SigmaGroup))
    (fun g ↦ Subgroup.subset_closure
      (mem_compressionSubmonoid_of_mem sigmaBase _ (iotaVertical_mem_sigmaBase g)))
    (Subgroup.subset_closure sigmaStable_mem_compressionSubmonoid) v

/-- **The literal pair is a compression pair.**  Infranormal by
`sigmaBase_isInfranormal`, not normal by `sigmaBase_not_normal`.

Every endpoint of the Kun--Thom/Shulman double construction is stated for an
abstract compression pair; this is what lets all of them be read at `(Σ, B)`. -/
theorem sigmaBase_isCompressionPair : IsCompressionPair sigmaBase :=
  ⟨sigmaBase_isInfranormal, sigmaBase_not_normal⟩

/-! ## The Bass--Serre witness of the literal double -/

/-- The witness commutator of the literal double, at the compressor `t` and the
marked translation `v₁`. -/
def sigmaDoubleWitness : SymmetricDouble SigmaGroup sigmaBase :=
  DoubleFdRigidity.doubleComponent SigmaGroup sigmaBase
    SymmetricDoubleMF.sigmaStable SymmetricDoubleMF.sigmaUnit FlipC2.swap

/-- The witness is not trivial: the half-translation escapes `B`. -/
theorem sigmaDoubleWitness_ne_one : sigmaDoubleWitness ≠ 1 :=
  DoubleFdRigidity.doubleComponent_ne_one SigmaGroup sigmaBase
    SymmetricDoubleMF.escapeElement_not_mem_sigmaBase flipC2_swap_ne_one

/-- **Every finite-dimensional representation of the literal double kills the
witness**, over every field. -/
theorem fdRep_sigmaDoubleWitness_eq_one
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (pi : SymmetricDouble SigmaGroup sigmaBase →* (V ≃ₗ[k] V)) :
    pi sigmaDoubleWitness = 1 :=
  DoubleFdRigidity.fdRep_kills_doubleComponent SigmaGroup sigmaBase
    sigmaBase_isInfranormal SymmetricDoubleMF.sigmaUnit_mem_sigmaBase pi

/-- **The literal symmetric double has no faithful finite-dimensional
representation**, over any field. -/
theorem symmetricDouble_no_faithful_fdRep_sigma
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (pi : SymmetricDouble SigmaGroup sigmaBase →* (V ≃ₗ[k] V)) :
    ¬ Function.Injective pi :=
  DoubleFdRigidity.symmetricDouble_no_faithful_fdRep SigmaGroup sigmaBase
    sigmaBase_isCompressionPair pi

/-! ## Carried to matrices -/

/-- **Every group homomorphism of the literal double into a matrix algebra
sends the witness to the identity.**

The bridge is the left regular action of `M_Y(ℂ)` on `Y → ℂ`: a homomorphism
into the matrices is a homomorphism into the endomorphisms of a
finite-dimensional space, and a homomorphism from a *group* lands in the units,
which are the linear automorphisms.  Then
`fdRep_sigmaDoubleWitness_eq_one` applies and the bridge is injective. -/
theorem matrixHom_sigmaDoubleWitness_eq_one {Y : Type} [Fintype Y]
    [DecidableEq Y]
    (phi : SymmetricDouble SigmaGroup sigmaBase →* Matrix Y Y ℂ) :
    phi sigmaDoubleWitness = 1 := by
  classical
  set e := (Matrix.toLinAlgEquiv' (n := Y) (R := ℂ))
  set hEnd : SymmetricDouble SigmaGroup sigmaBase →* Module.End ℂ (Y → ℂ) :=
    e.toRingEquiv.toMulEquiv.toMonoidHom.comp phi with hEndDef
  set hpi : SymmetricDouble SigmaGroup sigmaBase →* ((Y → ℂ) ≃ₗ[ℂ] (Y → ℂ)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ
      (Y → ℂ)).toMonoidHom.comp (MonoidHom.toHomUnits hEnd)
  have hkill : hpi sigmaDoubleWitness = 1 := fdRep_sigmaDoubleWitness_eq_one hpi
  have hunit : (MonoidHom.toHomUnits hEnd) sigmaDoubleWitness = 1 := by
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ (Y → ℂ)).injective
    rw [map_one]
    exact hkill
  have hend : hEnd sigmaDoubleWitness = 1 := by
    have := congrArg (fun u : (Module.End ℂ (Y → ℂ))ˣ ↦ (u : Module.End ℂ (Y → ℂ)))
      hunit
    simpa using this
  have := congrArg (fun x ↦ e.symm x) hend
  simpa [hEndDef] using this

/-! ## The consequence for the finite-matrix target -/

/-- **No admissible model can be an exact homomorphism.**

If a `RegularCharacterModel` for the literal double has the witness in its test
set, runs at an accuracy below `1`, and its map is unital and exactly
multiplicative, the model is contradictory: the map sends the witness to the
identity matrix, whose normalized trace is `1`, while `trace_correct_ne` asks
for at most `ε`.

This is the sharp form of "the models must be approximate".
`Sofic/SymmetricDoubleMF` gets that conclusion from separability, hence only
against finite groups; here it holds against every finite-dimensional model
over every field, with no separability input at all. -/
theorem regularCharacterModel_not_multiplicative
    {F : Finset (SymmetricDouble SigmaGroup sigmaBase)} {eps : ℝ}
    {Bnd : SymmetricDouble SigmaGroup sigmaBase → ℝ}
    (M : MFTraceRecognition.RegularCharacterModel
      (SymmetricDouble SigmaGroup sigmaBase) F eps Bnd)
    (hw : sigmaDoubleWitness ∈ F) (heps : eps < 1)
    (hone : M.map 1 = 1)
    (hmul : ∀ g y : SymmetricDouble SigmaGroup sigmaBase,
      M.map (g * y) = M.map g * M.map y) : False := by
  have h1 : M.map sigmaDoubleWitness = 1 :=
    matrixHom_sigmaDoubleWitness_eq_one
      (⟨⟨M.map, hone⟩, hmul⟩ :
        SymmetricDouble SigmaGroup sigmaBase →* Matrix M.carrier M.carrier ℂ)
  have h2 := M.trace_correct_ne sigmaDoubleWitness hw sigmaDoubleWitness_ne_one
  have hcard : ((Fintype.card M.carrier : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr M.nonempty.ne'
  rw [h1, Matrix.trace_one, div_self hcard, norm_one] at h2
  linarith

end

end TerminalQuotientPresentation
end GroupApproximation
