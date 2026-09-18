import GroupApproximation.Monsters.LiteralDyadicCalibration

/-!
# The lamp kernel of a subgroup of the literal Clifford extension

This file serves `non_mf_group_notes.tex`, `\section{Necessity}`, paragraph
*Sharpness of the Kazhdan hypothesis* (tex ≈ 1163–1170).  The realized quotient
`LiteralDyadicCalibration.DyadicRealizedQuotient` is a subgroup of
`CliffordDyadic = lampGroup Sites ⋊ (ℤ[1/2] ⋊ ℤ)`.

For every subgroup `H` of `CliffordDyadic`, the elements with trivial affine part form a
normal subgroup `lampKernel H` of `H` such that

* `lampKernel H` is locally finite (`isLocallyFiniteGroup_lampKernel`): it embeds in the
  Clifford lamp group (`lampPart`, `lampPart_injective`), which is locally finite;
* `H ⧸ lampKernel H` is solvable (`isSolvable_quotient_lampKernel`): it embeds in the
  solvable affine group `ℤ[1/2] ⋊ ℤ`.

This is the structure used by the amenable-to-MF step of the sharpness paragraph ("So it
is MF"): the realized quotient is (locally finite)-by-solvable.  The file also records the
basic identities `affinePart`, `mem_lampKernel` and `lampPart_apply` used by the
detection argument (`CliffordMF.CliffordLift`).
-/

namespace GroupApproximation.Full.NN10b

open GroupApproximation.CliffordAlgebraLamp GroupApproximation.DyadicRationals
  GroupApproximation.LiteralDyadicCalibration

/-- The affine part of an element of a subgroup of the literal Clifford extension. -/
noncomputable def affinePart (H : Subgroup CliffordDyadic) : H →* Affine :=
  SemidirectProduct.rightHom.comp H.subtype

theorem affinePart_apply (H : Subgroup CliffordDyadic) (x : H) :
    affinePart H x = (x : CliffordDyadic).right := rfl

/-- The lamp kernel: elements of `H` with trivial affine part. -/
noncomputable def lampKernel (H : Subgroup CliffordDyadic) : Subgroup H :=
  (affinePart H).ker

instance lampKernel_normal (H : Subgroup CliffordDyadic) : (lampKernel H).Normal :=
  MonoidHom.normal_ker (affinePart H)

theorem mem_lampKernel {H : Subgroup CliffordDyadic} {x : H} :
    x ∈ lampKernel H ↔ (x : CliffordDyadic).right = 1 := by
  rw [lampKernel, MonoidHom.mem_ker, affinePart_apply]

/-- The lamp part of an element of the lamp kernel. -/
noncomputable def lampPart (H : Subgroup CliffordDyadic) : lampKernel H →* lampGroup Sites where
  toFun x := ((x : H) : CliffordDyadic).left
  map_one' := rfl
  map_mul' x y := by
    have hx : ((x : H) : CliffordDyadic).right = 1 := mem_lampKernel.mp x.2
    show ((x : H) : CliffordDyadic).left *
        lampAction ((x : H) : CliffordDyadic).right ((y : H) : CliffordDyadic).left =
      ((x : H) : CliffordDyadic).left * ((y : H) : CliffordDyadic).left
    rw [hx, map_one, MulAut.one_apply]

theorem lampPart_apply (H : Subgroup CliffordDyadic) (x : lampKernel H) :
    lampPart H x = ((x : H) : CliffordDyadic).left := rfl

/-- An element of the lamp kernel is determined by its lamp part. -/
theorem lampPart_injective (H : Subgroup CliffordDyadic) : Function.Injective (lampPart H) := by
  intro x y hxy
  have hx : ((x : H) : CliffordDyadic).right = 1 := mem_lampKernel.mp x.2
  have hy : ((y : H) : CliffordDyadic).right = 1 := mem_lampKernel.mp y.2
  have hl : ((x : H) : CliffordDyadic).left = ((y : H) : CliffordDyadic).left := hxy
  exact Subtype.ext (Subtype.ext (SemidirectProduct.ext hl (hx.trans hy.symm)))

/-- **The lamp kernel is locally finite.** -/
theorem isLocallyFiniteGroup_lampKernel (H : Subgroup CliffordDyadic) :
    IsLocallyFiniteGroup (lampKernel H) :=
  (isLocallyFiniteGroup_lampGroup Sites).comap (lampPart H) (lampPart_injective H)

/-- **The quotient by the lamp kernel is solvable**: it embeds in `ℤ[1/2] ⋊ ℤ`. -/
instance isSolvable_quotient_lampKernel (H : Subgroup CliffordDyadic) :
    IsSolvable (H ⧸ lampKernel H) :=
  solvable_of_solvable_injective (QuotientGroup.kerLift_injective (affinePart H))

/-- The realized quotient of the sharpness paragraph is (locally finite)-by-solvable. -/
theorem dyadicRealizedQuotient_lampKernel :
    IsLocallyFiniteGroup (lampKernel dyadicRealization.range) ∧
      IsSolvable (DyadicRealizedQuotient ⧸ lampKernel dyadicRealization.range) :=
  ⟨isLocallyFiniteGroup_lampKernel _, isSolvable_quotient_lampKernel _⟩

end GroupApproximation.Full.NN10b
