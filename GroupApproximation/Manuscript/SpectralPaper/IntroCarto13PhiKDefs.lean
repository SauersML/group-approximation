import GroupApproximation.Sofic.FinitePerfectLampExactRadical
import GroupApproximation.Manuscript.NonMFNotes.Full.VisibleQuotient.FibreCollapse
import GroupApproximation.Meta.AxiomGuard

/-!
# The visible quotient `Φ_K` for an arbitrary finite lamp group: definitions

Notes census, `thm:notes-visible-quotient` (`non_mf_group_notes.tex` ~1966):

> For every finite group `K`, every homomorphism from `W_K` to a norm matrix
> corona factors uniquely through `Φ_K`.  Moreover
> `ker Φ_K = Rad_MF = Rad_fd = Res_fin = Rad_lin = Rad_Bohr`.

Here `W_K = K^(X) ⋊ G_*` is `FinitePerfectLamp.WFin K`, with
`G_* = Vertical conjD conjD_injective` acting on the cosets
`X = G_* ⧸ ι(Γ̄)`.  The height is `SemidirectProduct.rightHom : G_* → ℤ`.

**Modelling choice.**  The lane writes the target as
`(ℤ →₀ K_ab) ⋊ G_*`.  We use the sites `G_* ⧸ ker(height)` in place of `ℤ`.
This quotient is a model of `ℤ` with the translation action through the height.
So the target is `heightLampQuotient K = Wreath K_ab G_* (G_* ⧸ ker height)`,
and `NN04.wreath_quotient_isResiduallyFinite` applies to it directly.

`Φ_K = heightAbelianization K` abelianizes the lamp values and multiplies them
along the height fibres of `heightSite : X → G_* ⧸ ker height`.

Route of this module.
* `range_iotaVertical_le_ker` gives the site map `heightSite`.  It is
  equivariant because both sides are `mk (g * v)`.
* `heightAbelianization_surjective` is fibre products (`pushHom_surjective`)
  after value maps (`lampValueHom_surjective`).
* `exists_second_site` says every height fibre has a second site: for
  `y = g • root`, take `(g t⁻¹ ι(v₁) t) • root`.  `moved_cosets_ne` separates
  it from `y`, and `ι(v₁)` has height zero.
-/

namespace GroupApproximation.SpectralPaper.IntroCarto13

open SemidirectProduct MarkedCompression ExplicitLinearModel LiteralDoublingWreath
open FinitePerfectLamp GroupApproximation.WreathLampPushforward GroupApproximation.Full.NN04

/-- The vertical group `G_*` of the concrete doubling datum. -/
abbrev GStar : Type := Vertical conjD conjD_injective

/-- The height sites `G_* ⧸ ker(height)`, a model of `ℤ`. -/
abbrev HeightSites : Type :=
  GStar ⧸ (SemidirectProduct.rightHom : GStar →* Multiplicative ℤ).ker

/-- The visible quotient `P_K = (K_ab)^(ℤ) ⋊ G_*`. -/
abbrev heightLampQuotient (K : Type) [Group K] : Type :=
  Wreath (Abelianization K) GStar HeightSites

/-- The base copy of `Γ̄` has height zero. -/
theorem rightHom_iotaVertical (a : gammaBar) :
    (SemidirectProduct.rightHom : GStar →* Multiplicative ℤ)
      (iotaVertical conjD conjD_injective a) = 1 := by
  rw [iotaVertical, MonoidHom.comp_apply]
  exact SemidirectProduct.rightHom_inl _

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.rightHom_iotaVertical

theorem range_iotaVertical_le_ker :
    (iotaVertical conjD conjD_injective).range ≤
      (SemidirectProduct.rightHom : GStar →* Multiplicative ℤ).ker := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker]
  exact rightHom_iotaVertical a

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.range_iotaVertical_le_ker

/-- The site map `X → ℤ`: a coset goes to its height. -/
def heightSite : Cosets conjD conjD_injective → HeightSites :=
  Subgroup.quotientMapOfLE range_iotaVertical_le_ker

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightSite

theorem heightSite_mk (v : GStar) :
    heightSite (QuotientGroup.mk v : Cosets conjD conjD_injective) =
      (QuotientGroup.mk v : HeightSites) := rfl

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightSite_mk

/-- The site map is equivariant. -/
theorem heightSite_smul (g : GStar) (y : Cosets conjD conjD_injective) :
    heightSite (g • y) = g • heightSite y := by
  refine QuotientGroup.induction_on y fun v => ?_
  rfl

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightSite_smul

theorem heightSite_surjective : Function.Surjective heightSite := by
  intro y
  refine QuotientGroup.induction_on y fun v => ?_
  exact ⟨QuotientGroup.mk v, rfl⟩

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightSite_surjective

/-- **`Φ_K`.**  Abelianize the lamp values, then multiply them along the height
fibres. -/
noncomputable def heightAbelianization (K : Type) [Group K] :
    WFin K →* heightLampQuotient K :=
  (pushWreath (K := Abelianization K) heightSite heightSite_smul).comp
    (wreathValueHom (G := GStar) (X := Cosets conjD conjD_injective)
      Abelianization.of)

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightAbelianization

theorem abelianization_of_surjective (K : Type) [Group K] :
    Function.Surjective (Abelianization.of : K →* Abelianization K) := by
  intro x
  refine QuotientGroup.induction_on x fun k => ?_
  exact ⟨k, rfl⟩

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.abelianization_of_surjective

/-- `Φ_K` is onto. -/
theorem heightAbelianization_surjective (K : Type) [Group K] :
    Function.Surjective (heightAbelianization K) := by
  intro w
  obtain ⟨f, hf⟩ :=
    pushHom_surjective (A := Abelianization K) heightSite_surjective w.left
  obtain ⟨f', hf'⟩ := lampValueHom_surjective (X := Cosets conjD conjD_injective)
    (abelianization_of_surjective K) f
  refine ⟨⟨f', w.right⟩, SemidirectProduct.ext ?_ rfl⟩
  show pushHom (K := Abelianization K) heightSite
    (lampValueHom Abelianization.of f') = w.left
  rw [hf', hf]

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightAbelianization_surjective

/-- **Every height fibre has a second site.** -/
theorem exists_second_site (y : Cosets conjD conjD_injective) :
    ∃ y' : Cosets conjD conjD_injective, y' ≠ y ∧ heightSite y' = heightSite y := by
  refine QuotientGroup.induction_on y fun g => ?_
  refine ⟨(g * (tVertical conjD conjD_injective)⁻¹ *
      (iotaVertical conjD conjD_injective v1G * tVertical conjD conjD_injective)) •
        rootCoset conjD conjD_injective, ?_, ?_⟩
  · intro heq
    have hy : (QuotientGroup.mk g : Cosets conjD conjD_injective) =
        (g * (tVertical conjD conjD_injective)⁻¹) •
          (tVertical conjD conjD_injective • rootCoset conjD conjD_injective) := by
      rw [← mul_smul, inv_mul_cancel_right, smul_rootCoset]
    rw [hy, mul_smul, smul_left_cancel_iff] at heq
    exact moved_cosets_ne conjD conjD_injective v1G_not_mem_range heq.symm
  · rw [smul_rootCoset, heightSite_mk, heightSite_mk, QuotientGroup.eq,
      MonoidHom.mem_ker]
    simp only [map_mul, map_inv, rightHom_iotaVertical, one_mul, inv_mul_cancel_right,
      inv_mul_cancel]

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.exists_second_site

end GroupApproximation.SpectralPaper.IntroCarto13
