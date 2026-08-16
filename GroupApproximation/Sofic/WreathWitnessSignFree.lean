import GroupApproximation.Sofic.WreathWitnessGeneric
import GroupApproximation.Sofic.WreathWitnessW3
import GroupApproximation.Sofic.CentralInvolutionFinite

/-!
# The wreath sentence at the sign-free quotient

`non_mf_groups_exist.tex`, the paragraph between `def:invwitness` and
`thm:collapse` (grep `"In a permutational wreath product"`).
`Sofic.WreathWitnessGeneric` proves that sentence generically and instantiates
it at `Wreath K G X`.  The manuscript's *collapse example*, however, is the
sign-free quotient of the Kazhdan--Clifford group, and that group is not a
permutational wreath product in this repository's sense: its lamp group is
`CliffordLamp X`, a presented group with a central sign, not a restricted
direct product.  Reaching it through an isomorphism onto
`Wreath (ZMod 2) (Vertical α hα) (Cosets α hα)` would need a normal form for
the Clifford presentation, which this repository does not have.

It does not need one.  `WreathWitness.LampFamily` isolates the three facts the
printed proof actually uses --- lamps are involutions, lamps commute, and
conjugation moves a lamp's site --- and the sign-free quotient satisfies all
three.  The middle one is exactly what killing the central sign buys: in
`Ambient α hα` the commutator of two lamps at distinct sites *is* the sign, so
the lamps anticommute and `(W3)` fails (`Sofic.WreathWitnessW3`); in the
quotient by that sign the same commutator dies and the family is genuine.

So `CO.02` closes at both examples with one abstraction:

* `WreathWitnessGeneric.isInvolutiveCompressionWitness_map_inr` --- the literal
  permutational wreath product `K^{(X)} ⋊ G`, any lamp group;
* `isInvolutiveCompressionWitness_signFree` below --- the sign-free
  Kazhdan--Clifford quotient, which is the group
  `Sofic.CommutingLampCollapse.commutingLampQuotient_collapse` computes its
  witness in by hand.

The witness produced here is the same element that theorem builds: the image of
the moved root lamp `t c t⁻¹`, at the site `t Γ`, for the image of the base
copy compressed by the image of the stable letter.  Nothing analytic is used;
the collapse theorem that consumes the witness lives elsewhere.
-/

namespace GroupApproximation
namespace WreathWitnessSignFree

open MarkedCompression MappingTelescope CliffordLamp SemidirectProduct
open scoped commutatorElement

universe u

/-! ## The sign-free quotient -/

/-- The central Clifford sign generates a normal subgroup, so the quotient
below is a group.  `Sofic.CommutingLampCollapse` declares the same instance for
an ambient group in `Type 0`; this is the statement at the manuscript's scope.
The binders are implicit so that instance search can recover them from the
subgroup itself, as in that module. -/
instance signZpowersNormal {Γ : Type u} [Group Γ] {α : Γ →* Γ}
    {hα : Function.Injective α} :
    (Subgroup.zpowers (signAmbient α hα)).Normal :=
  zpowers_normal_of_central _ (signAmbient_central α hα)

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The sign-free quotient of the Kazhdan--Clifford ambient group: kill the
central Clifford sign and the lamps commute. -/
abbrev SignFree : Type u :=
  Ambient α hα ⧸ Subgroup.zpowers (signAmbient α hα)

/-- The quotient map onto the sign-free quotient. -/
def signFreeMk : Ambient α hα →* SignFree α hα :=
  QuotientGroup.mk' (Subgroup.zpowers (signAmbient α hα))

/-- The sign is what the quotient kills. -/
theorem signFreeMk_signAmbient : signFreeMk α hα (signAmbient α hα) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)

/-! ## The lamp family of the sign-free quotient -/

/-- **The sign-free quotient carries a lamp family.**  Its lamps are the images
of the Clifford lamps.  They are still involutions and are still moved by the
acting group; what is new is that they *commute*, because the only obstruction
was the central sign and it has been killed. -/
def signFreeLampFamily :
    WreathWitness.LampFamily (SignFree α hα) (Vertical α hα)
      (Cosets α hα) where
  lam x := signFreeMk α hα (inl (lamp (Cosets α hα) x))
  emb := (signFreeMk α hα).comp (inr : Vertical α hα →* Ambient α hα)
  lam_mul_self := fun x => by
    have h : lamp (Cosets α hα) x * lamp (Cosets α hα) x = 1 := by
      simpa [pow_two] using lamp_sq (Cosets α hα) x
    rw [← map_mul, ← map_mul, h]
    simp
  lam_commute := fun x y => by
    by_cases hxy : x = y
    · subst hxy
      exact Commute.refl _
    · apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement, ← map_commutatorElement,
        commutator_lamp_lamp (Cosets α hα) hxy]
      exact signFreeMk_signAmbient α hα
  conj_lam := fun g x => by
    show signFreeMk α hα (inr g) *
        signFreeMk α hα (inl (lamp (Cosets α hα) x)) *
        (signFreeMk α hα (inr g))⁻¹ =
      signFreeMk α hα (inl (lamp (Cosets α hα) (g • x)))
    rw [← map_inv, ← map_mul, ← map_mul, conj_inl_lamp α hα g x]

@[simp] theorem signFreeLampFamily_lam (x : Cosets α hα) :
    (signFreeLampFamily α hα).lam x =
      signFreeMk α hα (inl (lamp (Cosets α hα) x)) := rfl

@[simp] theorem signFreeLampFamily_emb :
    (signFreeLampFamily α hα).emb =
      (signFreeMk α hα).comp (inr : Vertical α hα →* Ambient α hα) := rfl

/-! ## The witness, from the generic sentence -/

/-- The image of the base copy, described two ways: as the image of the
vertical base copy under the composite embedding, and as the range of the
composite `Γ → SignFree`.  The second is the form
`Sofic.CommutingLampCollapse` uses. -/
theorem map_range_iotaVertical :
    ((iotaVertical α hα).range).map
        ((signFreeMk α hα).comp (inr : Vertical α hα →* Ambient α hα)) =
      ((signFreeMk α hα).comp (iotaAmbient α hα)).range :=
  MonoidHom.map_range _ _

/-- The compressed base copy fixes the witness site, in the form the lamp
family consumes. -/
theorem tVertical_compressed_fixes_tSite :
    ∀ γ ∈ (iotaVertical α hα).range,
      (tVertical α hα * γ * (tVertical α hα)⁻¹) • tSite α hα = tSite α hα := by
  intro γ hγ
  obtain ⟨γ₀, rfl⟩ := MonoidHom.mem_range.mp hγ
  rw [vertical_compress]
  exact iotaVertical_range_smul_tSite α hα γ₀

/-- **`CO.02` at the manuscript's collapse example.**  The image of the moved
root lamp `t c t⁻¹` is an involutive compression witness in the sign-free
quotient, for the image of the base copy compressed by the image of the stable
letter.

It is obtained from the *generic* wreath sentence
(`WreathWitness.LampFamily.isInvolutiveCompressionWitness`) instantiated at
`signFreeLampFamily`, not from a bespoke computation.  The element and the
subgroup are the ones
`Sofic.CommutingLampCollapse.commutingLampQuotient_collapse` builds by hand, so
that theorem's witness step is now an instance of the printed sentence rather
than a parallel argument. -/
theorem isInvolutiveCompressionWitness_signFree :
    CollapseUniverseScope.IsInvolutiveCompressionWitness
      (((signFreeMk α hα).comp (iotaAmbient α hα)).range)
      (signFreeMk α hα (tAmbient α hα))
      (signFreeMk α hα
        (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹)) := by
  rw [WreathWitnessW3.movedRootLamp_eq α hα, ← map_range_iotaVertical α hα]
  exact (signFreeLampFamily α hα).isInvolutiveCompressionWitness
    (iotaVertical α hα).range (tVertical α hα) (tSite α hα)
    (tVertical_compressed_fixes_tSite α hα)

/-- The `Type 0` spelling, for the consumers of
`InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness`. -/
theorem isInvolutiveCompressionWitness_signFree_zero {Γ₀ : Type} [Group Γ₀]
    (β : Γ₀ →* Γ₀) (hβ : Function.Injective β) :
    InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness
      (((signFreeMk β hβ).comp (iotaAmbient β hβ)).range)
      (signFreeMk β hβ (tAmbient β hβ))
      (signFreeMk β hβ
        (tAmbient β hβ * cAmbient β hβ * (tAmbient β hβ)⁻¹)) :=
  isInvolutiveCompressionWitness_signFree β hβ

end WreathWitnessSignFree
end GroupApproximation
