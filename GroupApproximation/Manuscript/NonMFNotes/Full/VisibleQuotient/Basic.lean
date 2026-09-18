import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.WreathStar
import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.IndexEight
import GroupApproximation.Manuscript.NonMFNotes.Full.VisibleQuotient.TorsionTelescope
import GroupApproximation.Manuscript.NonMFNotes.Full.VisibleQuotient.FibreCollapse
import GroupApproximation.Manuscript.NonMFNotes.Full.VisibleQuotient.LamplighterRF
import GroupApproximation.Sofic.FiveRadicalsCoincide
import GroupApproximation.Sofic.CompressionWreathFinitelyGenerated
import GroupApproximation.Sofic.PerfectLampCompressionRadical
import GroupApproximation.Analysis.PeterWeylSeparation
import Mathlib.GroupTheory.Abelianization.Finite
import GroupApproximation.Meta.AxiomGuard

/-!
# The visible quotient of `W_K`

Manuscript `non_mf_group_notes.tex`, **thm:notes-visible-quotient** (tex lines
1963--2050).  Let `K` be a finite group and

* `W_K = K^(X) ⋊ G_*`, with `X = G_*/Γ_*`;
* `P_K = (K_ab)^(ℤ) ⋊ G_*`, where `G_*` acts on `ℤ` through its height;
* `Φ_K : W_K → P_K`, which abelianizes every lamp value and sums the values over
  each height fibre.

Then `Φ_K` is onto, and its kernel is each of the five radicals of `W_K`: the
corona MF radical, the finite-dimensional unitary residual, the finite
residual, the all-fields linear residual and the Bohr residual.

The sites of `P_K` are `G_* ⧸ ker h`, where `h : G_* → ℤ` is the height.  This
is a copy of the image of `h`, so it is the printed `ℤ` up to relabelling.

The proof follows the notes.

1. *Spectral motion* (`TorsionTelescope`).  In every corona representation, a
   lamp value at two sites of equal height is identified.
2. *Fibre collapse* (`FibreCollapse`).  Each height fibre is infinite, so every
   element of `ker Φ_K` lies in the MF radical.
3. *`P_K` is residually finite* (`LamplighterRF`).
4. The five radicals then coincide with `ker Φ_K` (`five_radicals_eq`).

Main declarations:

* `height`, `HeightSites`, `heightSite` -- the height and the fibre map `X → ℤ`;
* `WK`, `PK`, `PhiK`, `phiK_surjective`;
* `ker_phiK_le_actualCoronaMFResidual`, `pk_isResiduallyFinite`;
* `notesVisibleQuotient` -- the theorem.
-/

namespace GroupApproximation.Full.NN04

open MarkedCompression ExplicitLinearModel MatricialStabilityRadical
open GroupApproximation.WreathLampPushforward GroupApproximation.Full.NN05

noncomputable section

/-! ## The height of `G_*` and the height fibres of `X` -/

/-- The height `h : G_* → ℤ`, sending `Γ_*` to `0` and the stable letter to `1`.
It is the vertical coordinate of `V(Γ̄, conjD) = Telescope ⋊ ℤ`. -/
def height : Gstar →* Multiplicative ℤ :=
  (SemidirectProduct.rightHom : Vertical conjD conjD_injective →* Multiplicative ℤ).comp
    gstarEquivVertical.toMonoidHom

theorem height_ofGamma (g : GammaStar) : height (ofGamma g) = 1 := by
  show (SemidirectProduct.rightHom : Vertical conjD conjD_injective →* Multiplicative ℤ)
    (gstarEquivVertical (ofGamma g)) = 1
  rw [gstarEquivVertical_ofGamma]
  rfl

theorem height_stableLetter : height stableLetter = Multiplicative.ofAdd 1 := by
  show (SemidirectProduct.rightHom : Vertical conjD conjD_injective →* Multiplicative ℤ)
    (gstarEquivVertical stableLetter) = Multiplicative.ofAdd 1
  rw [gstarEquivVertical_stableLetter]
  rfl

theorem ofGamma_range_le_ker_height : ofGamma.range ≤ height.ker := by
  rintro _ ⟨γ, rfl⟩
  exact MonoidHom.mem_ker.mpr (height_ofGamma γ)

/-- The sites of `P_K`: `G_* ⧸ ker h`, a copy of the image of the height. -/
abbrev HeightSites : Type := Gstar ⧸ height.ker

/-- The height of a site of `X = G_*/Γ_*`. -/
def heightSite : GstarCosets → HeightSites :=
  Subgroup.quotientMapOfLE ofGamma_range_le_ker_height

theorem heightSite_mk (g : Gstar) :
    heightSite (QuotientGroup.mk g) = (QuotientGroup.mk g : HeightSites) := rfl

theorem heightSite_smul (g : Gstar) (y : GstarCosets) :
    heightSite (g • y) = g • heightSite y := by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

theorem heightSite_surjective : Function.Surjective heightSite := by
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- **Every height fibre of `X` has at least two points.**  Take `γ ∈ Γ_*` with
`γ t Γ_* ≠ t Γ_*` (tex lines 2092--2094).  Translating it to the site `g Γ_*` gives
a second site of the same height. -/
theorem exists_ne_heightSite_eq (y : GstarCosets) :
    ∃ y' : GstarCosets, y' ≠ y ∧ heightSite y' = heightSite y := by
  obtain ⟨γ, hγ⟩ := exists_translate_ne
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hexp : (g * stableLetter⁻¹ * (ofGamma γ * stableLetter))⁻¹ * g
      = (ofGamma γ * stableLetter)⁻¹ * stableLetter := by
    group
  refine ⟨QuotientGroup.mk (g * stableLetter⁻¹ * (ofGamma γ * stableLetter)), ?_, ?_⟩
  · intro h
    apply hγ
    have h2 := QuotientGroup.eq.mp h
    rw [hexp] at h2
    exact QuotientGroup.eq.mpr h2
  · rw [heightSite_mk, heightSite_mk]
    apply QuotientGroup.eq.mpr
    rw [MonoidHom.mem_ker, hexp, map_mul, map_inv, map_mul, height_ofGamma, one_mul,
      inv_mul_cancel]

/-! ## The groups and the map -/

variable (K : Type) [Group K]

/-- **`W_K = K^(X) ⋊ G_*`** with `X = G_*/Γ_*` (tex lines 1945--1946). -/
abbrev WK : Type := Wreath K Gstar GstarCosets

/-- **`P_K = (K_ab)^(ℤ) ⋊ G_*`**, with sites `G_* ⧸ ker h`. -/
abbrev PK : Type := Wreath (Abelianization K) Gstar HeightSites

/-- **`Φ_K`**: abelianize each lamp value, then multiply the values over each
height fibre.  The `G_*`-coordinate is unchanged. -/
def PhiK : WK K →* PK K :=
  (pushWreath (K := Abelianization K) heightSite heightSite_smul).comp
    (wreathValueHom (K := K) (A := Abelianization K) (G := Gstar) (X := GstarCosets)
      Abelianization.of)

theorem abelianizationOf_surjective :
    Function.Surjective (Abelianization.of : K →* Abelianization K) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

/-- **thm:notes-visible-quotient, `Φ_K` is onto.** -/
theorem phiK_surjective : Function.Surjective (PhiK K) := by
  intro p
  obtain ⟨f, hf⟩ := pushHom_surjective (A := Abelianization K) heightSite_surjective p.left
  obtain ⟨f', hf'⟩ :=
    lampValueHom_surjective (X := GstarCosets) (abelianizationOf_surjective K) f
  refine ⟨⟨f', p.right⟩, SemidirectProduct.ext ?_ rfl⟩
  show pushHom heightSite (lampValueHom Abelianization.of f') = p.left
  rw [hf', hf]

/-! ## The kernel of `Φ_K` is invisible -/

/-- **Spectral motion, transported to `W_K`.**  For finite `K`, the lamp
difference between two sites of equal height lies in the corona MF radical. -/
theorem lampDiff_mem_of_heightSite_eq [Finite K] (y y' : GstarCosets) (k : K)
    (h : heightSite y = heightSite y') :
    (SemidirectProduct.inl (Lamp.single y k * (Lamp.single y' k)⁻¹) : WK K)
      ∈ actualCoronaMFResidual (WK K) := by
  obtain ⟨m, hm, hk⟩ := PerfectLampRadical.exists_pow_eq_one_of_finite k
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y'
  rw [heightSite_mk, heightSite_mk] at h
  have hheight :
      (SemidirectProduct.rightHom : Vertical conjD conjD_injective →* Multiplicative ℤ)
        (gstarEquivVertical g) = SemidirectProduct.rightHom (gstarEquivVertical g') := by
    have h2 : g⁻¹ * g' ∈ height.ker := QuotientGroup.eq.mp h
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hmod := lampDiff_mem_actualCoronaMFResidual_of_rightHom_eq_of_pow (K₀ := K)
    conjD conjD_injective CommutingLampCollapse.gammaBar_hasKazhdanPropertyT hm hk hheight
  rw [smul_rootCoset, smul_rootCoset] at hmod
  rw [mem_iff_of_map_eq (wreathCongr K gstarEquivVertical gstarCosetEquiv gstarCosetEquiv_smul)
      (map_actualCoronaMFResidual_mulEquiv
        (wreathCongr K gstarEquivVertical gstarCosetEquiv gstarCosetEquiv_smul)),
    wreathCongr_inl, map_mul, map_inv,
    lampCongr_single, lampCongr_single, gstarCosetEquiv_mk, gstarCosetEquiv_mk]
  exact hmod

/-- **thm:notes-visible-quotient, `ker Φ_K ≤ Rad_MF(W_K)`.** -/
theorem ker_phiK_le_actualCoronaMFResidual [Finite K] :
    (PhiK K).ker ≤ actualCoronaMFResidual (WK K) :=
  ker_pushWreath_comp_le (actualCoronaMFResidual (WK K)) heightSite heightSite_smul
    (fun y y' k h => lampDiff_mem_of_heightSite_eq K y y' k h) exists_ne_heightSite_eq

/-- **thm:notes-visible-quotient, `P_K` is residually finite.** -/
theorem pk_isResiduallyFinite [Finite K] : IsResiduallyFinite (PK K) :=
  wreath_quotient_isResiduallyFinite (A := Abelianization K) gstar_residuallyFinite height

/-- `W_K` is finitely generated for finite `K`. -/
theorem wk_fg [Finite K] : Group.FG (WK K) := by
  haveI : Group.FG (WreathV (K := K) conjD conjD_injective) :=
    MarkedCompression.fg_wreathV conjD conjD_injective AlternatingLampFamily.gammaBar_fg
      inferInstance
  exact Group.fg_of_surjective
    (f := (wreathCongr K gstarEquivVertical gstarCosetEquiv gstarCosetEquiv_smul).symm.toMonoidHom)
    (MulEquiv.surjective
      (wreathCongr K gstarEquivVertical gstarCosetEquiv gstarCosetEquiv_smul).symm)

/-- **thm:notes-visible-quotient.**  For a finite group `K`, the map
`Φ_K : W_K → P_K` is onto, `P_K` is residually finite, and

`ker Φ_K = Rad_MF(W_K) = Res_fdU(W_K) = Res_fin(W_K) = Res_lin(W_K) = Rad_Bohr(W_K)`. -/
theorem notesVisibleQuotient [Finite K] :
    Function.Surjective (PhiK K) ∧ IsResiduallyFinite (PK K) ∧
      actualCoronaMFResidual (WK K) = (PhiK K).ker ∧
      fdUnitaryResidual (WK K) = (PhiK K).ker ∧
      finiteResidual (WK K) = (PhiK K).ker ∧
      linearResidual (WK K) = (PhiK K).ker ∧
      PeterWeyl.bohrResidual (WK K) = (PhiK K).ker := by
  haveI : Group.FG (WK K) := wk_fg K
  exact ⟨phiK_surjective K, pk_isResiduallyFinite K,
    five_radicals_eq PeterWeyl.separatesPoints (PhiK K) (pk_isResiduallyFinite K)
      (ker_phiK_le_actualCoronaMFResidual K)⟩

end

#audit_axioms height_ofGamma
#audit_axioms heightSite_smul
#audit_axioms exists_ne_heightSite_eq
#audit_axioms phiK_surjective
#audit_axioms lampDiff_mem_of_heightSite_eq
#audit_axioms ker_phiK_le_actualCoronaMFResidual
#audit_axioms pk_isResiduallyFinite
#audit_axioms wk_fg
#audit_axioms notesVisibleQuotient

end GroupApproximation.Full.NN04
