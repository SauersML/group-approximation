import GroupApproximation.Algebra.SemidirectProductAssoc
import GroupApproximation.Monsters.ExplicitIntegralLinearModel
import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Sofic.MarkedCompressionGroup
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The split normal form `E = N_E ⋊ V` of the literal group

Source of the mathematics: `notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md`,
§1 (notation), §2 (the presentation without the centrality relators) and §3
(imposing centrality).  This module formalizes the *split* half of that
analysis and nothing else: the amalgam description of `N_E` (§5), the site
set (§4) and the block geometry are other modules' business.

## What is here

Write `E` for the literal forty-one-relator group
`LiteralNonMFPresentation.MarkedGroup` and

    V = Vertical conjD conjD_injective = Telescope(Γ̄, conj D) ⋊ ℤ

for the ascending HNN extension of the affine base `Γ̄ = gammaBar` along the
doubling `conjD`, i.e. the object `MarkedCompression.Vertical` already in the
repository.  This is `V ≅ ℤ[1/2]³ ⋊ SL₃(ℤ) ⋊ ℤ` of input (I3) of the source
document, presented as the telescope model rather than as a matrix group.

* `retraction : E →* V` kills the lamp generator `c` and is the identity on
  the base and on the stable letter.  It is surjective.
* `sect : V →* E` splits it: `retraction (sect v) = v`.
* `lampKernel = ⟨⟨c⟩⟩ ◁ E` is exactly `ker retraction`.
* `markedGroup_split` packages the internal splitting, and
  `markedGroupEquivSemidirect` upgrades it to
  `E ≃* lampKernel ⋊[lampKernelAction] V`.
* `markedGroupEquivCoreByInt` re-associates that to
  `E ≃* TelescopeCore ⋊[stableAction] Multiplicative ℤ`, where
  `TelescopeCore = lampKernel ⋊ Telescope` is the kernel of the
  stable-letter exponent.  This is the shape the soficity endpoint
  consumes, `ℤ` being the quotient.

## Why this is unconditional

The source document flags the identification of the literal base `B` with
`ℤ³ ⋊ SL₃(ℤ)` as a *literature* input (its `[audit-fix]` note on (I1)).  That
caveat is obsolete inside this repository: `LiteralBaseCompleteness`
proves `baseAffineEquiv : Base ≃* gammaBar` outright, so `α` really is
injective on the presented base and the telescope model really is the
ascending HNN extension of it.  Nothing here is hypothetical, and no
declaration in this file carries a hypothesis.

The only genuinely new work is the *section*: the retraction is a routine
`Realization`, but going back requires a homomorphism `Γ̄ →* E` implementing
`conjD` by conjugation with the stable letter, which is where completeness of
the twenty-relator presentation is consumed.
-/

namespace GroupApproximation
namespace LiteralLampKernelSplit

open LiteralNonMFPresentation LiteralNonMFLinearWitness
open LiteralBaseAffineQuotient ExplicitLinearModel MarkedCompression
open scoped commutatorElement

noncomputable section

/-! ## The vertical group `V` -/

/-- The ascending HNN extension `V` of the affine base along doubling: the
mapping telescope of `conj D` extended by its shift.  This is the group
called `V = T ⋊ ⟨τ⟩` in the source document. -/
abbrev V : Type := Vertical alpha conjD_injective

/-- The six literal base letters, evaluated at telescope level zero. -/
def verticalBaseGenerator (i : BaseGenerator) : V :=
  iotaVertical alpha conjD_injective (matrixBaseGenerator i)

/-- Free evaluation of a base word in `V` is the level-zero copy of its
value in the affine matrix group. -/
theorem vertical_eval_base (q : FreeGroup BaseGenerator) :
    FreeGroup.lift verticalBaseGenerator q =
      iotaVertical alpha conjD_injective
        (FreeGroup.lift matrixBaseGenerator q) := by
  change (FreeGroup.lift verticalBaseGenerator) q =
    ((iotaVertical alpha conjD_injective).comp
      (FreeGroup.lift matrixBaseGenerator)) q
  apply freeGroup_hom_eq_on_generators
  intro i
  simp [verticalBaseGenerator]

theorem verticalBaseGenerator_kills :
    ∀ r ∈ baseRelators, FreeGroup.lift verticalBaseGenerator r = 1 := by
  intro r hr
  rw [vertical_eval_base, matrixBaseGenerator_kills r hr, map_one]

/-- With a trivial lamp the marked compression word degenerates.  This is
what makes "kill `c`" respect the eight centrality relators. -/
theorem markedCompressionWord_lamp_one {G : Type*} [Group G] (t a : G) :
    markedCompressionWord t a 1 = 1 := by
  simp [markedCompressionWord]

/-- The lamp-killing realization of the literal presentation: base letters
and the stable letter go to the ascending HNN extension, and `c ↦ 1`. -/
def retractionRealization : Realization V where
  baseGenerator := verticalBaseGenerator
  stable := tVertical alpha conjD_injective
  lamp := 1
  base_relations := verticalBaseGenerator_kills
  stable_relations i := by
    simp only [verticalBaseGenerator]
    rw [vertical_compress]
    rw [conjD_matrixBaseGenerator]
    symm
    exact vertical_eval_base (compressedBaseWord i)
  lamp_sq := one_pow 2
  lamp_centralizes_base i := Commute.one_left _
  marked_central g := by
    rw [markedCompressionWord_lamp_one]
    exact Commute.one_left g

/-- **The retraction `E ↠ V`.**  It kills the lamp generator `c` and is the
identity on the base and on the stable letter. -/
def retraction : MarkedGroup →* V := realizationHom retractionRealization

@[simp] theorem retraction_base_generator (i : BaseGenerator) :
    retraction (baseMap (PresentedGroup.of i)) =
      iotaVertical alpha conjD_injective (matrixBaseGenerator i) :=
  realizationHom_base_generator retractionRealization i

@[simp] theorem retraction_stable :
    retraction stable = tVertical alpha conjD_injective :=
  realizationHom_stable retractionRealization

@[simp] theorem retraction_lamp : retraction lamp = 1 :=
  realizationHom_lamp retractionRealization

theorem retraction_comp_baseMap :
    retraction.comp baseMap =
      (iotaVertical alpha conjD_injective).comp affineQuotient := by
  refine PresentedGroup.ext ?_
  intro i
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, affineQuotient_generator,
    retraction_base_generator]

/-- On the base, the retraction is the level-zero copy of the affine
evaluation.  This is the statement that `E → V` restricts to the
identification `B ≅ Γ̄` on the base. -/
theorem retraction_baseMap (b : Base) :
    retraction (baseMap b) =
      iotaVertical alpha conjD_injective (affineQuotient b) := by
  have h := DFunLike.congr_fun retraction_comp_baseMap b
  simpa only [MonoidHom.comp_apply] using h

/-! ## The section `V → E`

Going back needs a homomorphism `Γ̄ →* E`.  It exists because the literal
base presentation is *complete*: `affineQuotient` is an isomorphism onto
`gammaBar` by `LiteralBaseCompleteness.affineQuotient_injective`. -/

theorem affineQuotient_mk (w : FreeGroup BaseGenerator) :
    affineQuotient (PresentedGroup.mk _ w) =
      FreeGroup.lift matrixBaseGenerator w := by
  change PresentedGroup.toGroup matrixBaseGenerator_kills
    (PresentedGroup.mk _ w) = _
  rw [presentedToGroup_mk]

@[simp] theorem baseAffineEquiv_apply (b : Base) :
    LiteralBaseCompleteness.baseAffineEquiv b = affineQuotient b := rfl

theorem affineQuotient_baseAffineEquiv_symm (γ : gammaBar) :
    affineQuotient (LiteralBaseCompleteness.baseAffineEquiv.symm γ) = γ := by
  rw [← baseAffineEquiv_apply, MulEquiv.apply_symm_apply]

theorem baseAffineEquiv_symm_affineQuotient (b : Base) :
    LiteralBaseCompleteness.baseAffineEquiv.symm (affineQuotient b) = b := by
  rw [← baseAffineEquiv_apply, MulEquiv.symm_apply_apply]

/-- The affine base, transported into `E` through the completeness
isomorphism.  Its image is exactly the image of the literal base. -/
def affineToMarked : gammaBar →* MarkedGroup :=
  baseMap.comp LiteralBaseCompleteness.baseAffineEquiv.symm.toMonoidHom

@[simp] theorem affineToMarked_apply (γ : gammaBar) :
    affineToMarked γ =
      baseMap (LiteralBaseCompleteness.baseAffineEquiv.symm γ) := rfl

@[simp] theorem affineToMarked_affineQuotient (b : Base) :
    affineToMarked (affineQuotient b) = baseMap b := by
  rw [affineToMarked_apply, baseAffineEquiv_symm_affineQuotient]

/-- The stable letter of `E` implements the doubling endomorphism on the
transported base.  This is the six displayed stable relations, upgraded from
the six generators to all of `Γ̄` through completeness. -/
theorem affineToMarked_comp_conjD :
    affineToMarked.comp (conjD.comp affineQuotient) =
      ((MulAut.conj stable).toMonoidHom).comp baseMap := by
  refine PresentedGroup.ext ?_
  intro i
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [affineQuotient_generator, conjD_matrixBaseGenerator, ← affineQuotient_mk,
    affineToMarked_affineQuotient, baseMap_mk]
  exact (stable_relation i).symm

theorem affineToMarked_conjD (γ : gammaBar) :
    affineToMarked (conjD γ) = stable * affineToMarked γ * stable⁻¹ := by
  obtain ⟨b, rfl⟩ := affineQuotient_surjective γ
  have h := DFunLike.congr_fun affineToMarked_comp_conjD b
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] at h
  rw [affineToMarked_affineQuotient]
  exact h

/-- The same statement, phrased with the name the ascending-HNN universal
property expects. -/
theorem affineToMarked_alpha (γ : gammaBar) :
    affineToMarked (alpha γ) = stable * affineToMarked γ * stable⁻¹ :=
  affineToMarked_conjD γ

/-- **The section `V ↪ E`.**  It is the universal property of the ascending
HNN extension applied to the transported base and the stable letter. -/
def sect : V →* MarkedGroup :=
  verticalLift alpha conjD_injective affineToMarked stable affineToMarked_alpha

@[simp] theorem sect_iota (γ : gammaBar) :
    sect (iotaVertical alpha conjD_injective γ) = affineToMarked γ :=
  verticalLift_iota alpha conjD_injective affineToMarked stable
    affineToMarked_alpha γ

@[simp] theorem sect_t : sect (tVertical alpha conjD_injective) = stable :=
  verticalLift_t alpha conjD_injective affineToMarked stable
    affineToMarked_alpha

@[simp] theorem retraction_affineToMarked (γ : gammaBar) :
    retraction (affineToMarked γ) = iotaVertical alpha conjD_injective γ := by
  rw [affineToMarked_apply, retraction_baseMap,
    affineQuotient_baseAffineEquiv_symm]

/-- **The splitting identity.**  `retraction ∘ sect = id`. -/
theorem retraction_sect (v : V) : retraction (sect v) = v := by
  have hmem : v ∈ (retraction.comp sect).eqLocus (MonoidHom.id V) := by
    apply vertical_mem_subgroup_of_iota_mem_of_t_mem alpha conjD_injective
    · intro γ
      show retraction (sect (iotaVertical alpha conjD_injective γ)) =
        iotaVertical alpha conjD_injective γ
      rw [sect_iota, retraction_affineToMarked]
    · show retraction (sect (tVertical alpha conjD_injective)) =
        tVertical alpha conjD_injective
      rw [sect_t, retraction_stable]
  exact hmem

theorem retraction_comp_sect : retraction.comp sect = MonoidHom.id V :=
  MonoidHom.ext retraction_sect

/-- The retraction onto the ascending HNN extension is surjective. -/
theorem retraction_surjective : Function.Surjective retraction :=
  fun v ↦ ⟨sect v, retraction_sect v⟩

theorem sect_injective : Function.Injective sect := by
  intro a b hab
  have h : retraction (sect a) = retraction (sect b) := by rw [hab]
  rwa [retraction_sect, retraction_sect] at h

/-! ## The lamp kernel -/

/-- The idempotent endomorphism of `E` which kills the lamp: `sect ∘
retraction`. -/
def lampCollapse : MarkedGroup →* MarkedGroup := sect.comp retraction

@[simp] theorem lampCollapse_apply (g : MarkedGroup) :
    lampCollapse g = sect (retraction g) := rfl

@[simp] theorem lampCollapse_baseMap (b : Base) :
    lampCollapse (baseMap b) = baseMap b := by
  rw [lampCollapse_apply, retraction_baseMap, sect_iota,
    affineToMarked_affineQuotient]

@[simp] theorem lampCollapse_stable : lampCollapse stable = stable := by
  rw [lampCollapse_apply, retraction_stable, sect_t]

@[simp] theorem lampCollapse_lamp : lampCollapse lamp = 1 := by
  rw [lampCollapse_apply, retraction_lamp, map_one]

theorem lampCollapse_idem (g : MarkedGroup) :
    lampCollapse (lampCollapse g) = lampCollapse g := by
  rw [lampCollapse_apply, lampCollapse_apply, retraction_sect]

/-- **The lamp kernel** `N ◁ E`: the normal closure of the lamp generator
`c`.  This is definitionally the same subgroup as
`AmalgamQuestionEndpoint.lampKernel`, which is stated there without proof
that it is the kernel of `E ↠ V`; `lampKernel_eq_ker` below supplies that. -/
def lampKernel : Subgroup MarkedGroup :=
  Subgroup.normalClosure ({lamp} : Set MarkedGroup)

@[simp] theorem lampKernel_def :
    lampKernel = Subgroup.normalClosure ({lamp} : Set MarkedGroup) := rfl

instance lampKernel_normal : lampKernel.Normal :=
  Subgroup.normalClosure_normal

theorem lamp_mem_lampKernel : lamp ∈ lampKernel :=
  Subgroup.subset_normalClosure (Set.mem_singleton _)

theorem lampKernel_le_ker : lampKernel ≤ retraction.ker := by
  apply Subgroup.normalClosure_le_normal
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  exact MonoidHom.mem_ker.mpr retraction_lamp

/-- Killing the lamp does not move anything modulo the lamp kernel.  Both
sides are homomorphisms out of the presented group, so it suffices to check
the eight letters. -/
theorem quotient_comp_lampCollapse :
    (QuotientGroup.mk' lampKernel).comp lampCollapse =
      QuotientGroup.mk' lampKernel := by
  refine PresentedGroup.ext ?_
  intro j
  match j with
  | .inl i =>
      have hof : (PresentedGroup.of (Sum.inl i : Generator) : MarkedGroup) =
          baseMap (PresentedGroup.of i) := (baseMap_generator i).symm
      rw [MonoidHom.comp_apply, hof, lampCollapse_baseMap]
  | .inr k =>
      have hk : (Sum.inr k : Generator) = Generator.stable ∨
          (Sum.inr k : Generator) = Generator.lamp := by
        fin_cases k
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hk with hk | hk
      · have hof : (PresentedGroup.of Generator.stable : MarkedGroup) =
            stable := rfl
        rw [MonoidHom.comp_apply, hk, hof, lampCollapse_stable]
      · have hof : (PresentedGroup.of Generator.lamp : MarkedGroup) =
            lamp := rfl
        rw [MonoidHom.comp_apply, hk, hof, lampCollapse_lamp, map_one,
          QuotientGroup.mk'_apply]
        exact ((QuotientGroup.eq_one_iff lamp).mpr lamp_mem_lampKernel).symm

theorem ker_le_lampKernel : retraction.ker ≤ lampKernel := by
  intro g hg
  have h1 : lampCollapse g = 1 := by
    rw [lampCollapse_apply, MonoidHom.mem_ker.mp hg, map_one]
  have h2 := DFunLike.congr_fun quotient_comp_lampCollapse g
  rw [MonoidHom.comp_apply, h1, map_one, QuotientGroup.mk'_apply] at h2
  exact (QuotientGroup.eq_one_iff g).mp h2.symm

/-- **The lamp kernel is the kernel of the retraction**, i.e. the sequence
`1 → N_E → E → V → 1` of (3.1) is exact. -/
theorem lampKernel_eq_ker : lampKernel = retraction.ker :=
  le_antisymm lampKernel_le_ker ker_le_lampKernel

theorem mem_lampKernel_iff (g : MarkedGroup) :
    g ∈ lampKernel ↔ retraction g = 1 := by
  rw [lampKernel_eq_ker]
  exact MonoidHom.mem_ker

/-- The marked central involution `w` lies in the lamp kernel: it is a word
in conjugates of `c`. -/
theorem retraction_mark : retraction mark = 1 := by
  rw [mark_eq_markedCompressionWord, map_markedCompressionWord,
    retraction_lamp, markedCompressionWord_lamp_one]

theorem mark_mem_lampKernel : mark ∈ lampKernel :=
  (mem_lampKernel_iff mark).mpr retraction_mark

/-! ## Site lamps

The conjugates `c_ξ = g c g⁻¹` of the source document's §2, indexed here by
`V` rather than by the coset space `X = V/B`.

**Read this before using them.**  `Sofic/LiteralBlockNormalForm.lean` carries
a parallel site-indexed development — `siteLamp : Site → MarkedGroup` by
`Quotient.liftOn'` over its `Site = Vertical ⧸ baseSubgroup`, with
`siteLamp_sq`, `siteLamp_origin` and the braiding — but over the *presented*
seven-letter model of `E/⟨⟨c⟩⟩`, not over the telescope.  The two are about
the same elements of `E` and nothing yet identifies the two models.

The descent below is to the telescope's own site set
`Cosets alpha conjD_injective`, which is the site set
`Sofic/LiteralBlockGeometry.lean` already uses (it opens `MarkedCompression`
and states `blockOf`, `Block` and `blockOf_smul` for exactly this `Vertical`).
So this is not a third indexing: it is the coordinate system that the block
geometry, the telescope filtration and the soficity endpoint all share. -/

/-- The lamp carried to the site indexed by `v ∈ V`. -/
def siteLamp (v : V) : MarkedGroup := sect v * lamp * (sect v)⁻¹

@[simp] theorem siteLamp_one : siteLamp 1 = lamp := by
  simp [siteLamp]

theorem siteLamp_mem_lampKernel (v : V) : siteLamp v ∈ lampKernel :=
  lampKernel_normal.conj_mem lamp lamp_mem_lampKernel (sect v)

theorem siteLamp_sq (v : V) : siteLamp v ^ 2 = 1 := by
  have h : lamp * lamp = 1 := by
    have hsq := lamp_sq
    rwa [pow_two] at hsq
  simp only [siteLamp, pow_two]
  calc sect v * lamp * (sect v)⁻¹ * (sect v * lamp * (sect v)⁻¹)
      = sect v * (lamp * lamp) * (sect v)⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem sect_conj_siteLamp (w v : V) :
    sect w * siteLamp v * (sect w)⁻¹ = siteLamp (w * v) := by
  simp only [siteLamp, map_mul]
  group

@[simp] theorem retraction_siteLamp (v : V) : retraction (siteLamp v) = 1 :=
  (mem_lampKernel_iff _).mp (siteLamp_mem_lampKernel v)

/-! ### Descent to the site set `X = V/B`

The site lamp depends only on the coset `vB`, because the base centralises the
lamp letter — dossier §2, the well-definedness of `c_{gB} := g c g⁻¹`. -/

/-- The site set `X = V/B` of the dossier, in the telescope's coordinates. -/
abbrev Site : Type := Cosets alpha conjD_injective

/-- Right translation by the level-zero base does not move a site lamp. -/
theorem siteLamp_mul_iota (v : V) (γ : gammaBar) :
    siteLamp (v * iotaVertical alpha conjD_injective γ) = siteLamp v := by
  have hcomm : affineToMarked γ * lamp * (affineToMarked γ)⁻¹ = lamp := by
    rw [affineToMarked_apply,
      ← (lamp_commutes_base (LiteralBaseCompleteness.baseAffineEquiv.symm γ)).eq]
    group
  simp only [siteLamp, map_mul, sect_iota]
  calc sect v * affineToMarked γ * lamp * (sect v * affineToMarked γ)⁻¹
      = sect v * (affineToMarked γ * lamp * (affineToMarked γ)⁻¹) *
          (sect v)⁻¹ := by group
    _ = sect v * lamp * (sect v)⁻¹ := by rw [hcomm]

/-- The lamp attached to a site. -/
def cosetLamp (ξ : Site) : MarkedGroup :=
  Quotient.liftOn' ξ siteLamp
    (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab
      obtain ⟨γ, hγ⟩ := hab
      have hb : b = a * iotaVertical alpha conjD_injective γ := by
        rw [hγ]; group
      rw [hb, siteLamp_mul_iota])

@[simp] theorem cosetLamp_mk (v : V) :
    cosetLamp (QuotientGroup.mk v : Site) = siteLamp v := rfl

@[simp] theorem cosetLamp_rootCoset :
    cosetLamp (rootCoset alpha conjD_injective) = lamp := by
  show cosetLamp (QuotientGroup.mk 1 : Site) = lamp
  rw [cosetLamp_mk, siteLamp_one]

/-- **Equivariance of the site lamps.**  This is the field a bundled
telescope-core instantiation needs in order to see the base permuting the
block groups; with the block lane's `blockOf_smul` it is the site-level half
of block equivariance. -/
theorem cosetLamp_smul (v : V) (ξ : Site) :
    cosetLamp (v • ξ) = sect v * cosetLamp ξ * (sect v)⁻¹ := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective ξ
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, cosetLamp_mk, cosetLamp_mk,
    sect_conj_siteLamp]

theorem cosetLamp_mem_lampKernel (ξ : Site) : cosetLamp ξ ∈ lampKernel := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective ξ
  rw [cosetLamp_mk]
  exact siteLamp_mem_lampKernel u

theorem cosetLamp_sq (ξ : Site) : cosetLamp ξ ^ 2 = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective ξ
  rw [cosetLamp_mk]
  exact siteLamp_sq u

/-! ## The internal split -/

theorem lampKernel_sup_sectRange : lampKernel ⊔ sect.range = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hleft : g * (sect (retraction g))⁻¹ ∈ lampKernel := by
    rw [mem_lampKernel_iff, map_mul, map_inv, retraction_sect, mul_inv_cancel]
  have hright : sect (retraction g) ∈ sect.range := ⟨retraction g, rfl⟩
  have h1 : lampKernel ≤ lampKernel ⊔ sect.range := le_sup_left
  have h2 : sect.range ≤ lampKernel ⊔ sect.range := le_sup_right
  have hprod :
      (g * (sect (retraction g))⁻¹) * sect (retraction g) ∈
        lampKernel ⊔ sect.range :=
    Subgroup.mul_mem _ (h1 hleft) (h2 hright)
  have hg : (g * (sect (retraction g))⁻¹) * sect (retraction g) = g := by
    group
  rwa [hg] at hprod

theorem lampKernel_inf_sectRange : lampKernel ⊓ sect.range = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hker, hrange⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨v, rfl⟩ := hrange
  rw [mem_lampKernel_iff, retraction_sect] at hker
  rw [hker, map_one]
  exact Subgroup.one_mem _

/-- The `V`-coordinate of an element of `E` is unique. -/
theorem exists_unique_sect_factor (g : MarkedGroup) :
    ∃! v : V, g * (sect v)⁻¹ ∈ lampKernel := by
  refine ⟨retraction g, ?_, ?_⟩
  -- `refine` leaves the first goal as a beta-redex, which `rw` cannot see
  -- through; `show` reduces it before the rewrite chain starts.
  · show g * (sect (retraction g))⁻¹ ∈ lampKernel
    rw [mem_lampKernel_iff, map_mul, map_inv, retraction_sect, mul_inv_cancel]
  · intro v hv
    rw [mem_lampKernel_iff, map_mul, map_inv, retraction_sect,
      mul_inv_eq_one] at hv
    exact hv.symm

/-- **The split normal form `E = N_E ⋊ V`.**  The lamp kernel is normal and
is exactly the kernel of the retraction onto the ascending HNN extension; it
meets the image of the section trivially and together they generate `E`; and
the section really is a section.

This is (3.1) of `notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md`,
with `V` the telescope model of the ascending HNN extension of the affine
base along doubling. -/
theorem markedGroup_split :
    lampKernel.Normal ∧
      lampKernel = MonoidHom.ker retraction ∧
      lampKernel ⊔ sect.range = ⊤ ∧
      lampKernel ⊓ sect.range = ⊥ ∧
      (∀ v : V, retraction (sect v) = v) ∧
      Function.Surjective retraction ∧
      Function.Injective sect :=
  ⟨lampKernel_normal, lampKernel_eq_ker, lampKernel_sup_sectRange,
    lampKernel_inf_sectRange, retraction_sect, retraction_surjective,
    sect_injective⟩

/-! ## The semidirect product

The internal split above is upgraded to an isomorphism with the abstract
semidirect product.  Everything below is bookkeeping on top of
`markedGroup_split`; a consumer who only needs the internal statement can
ignore it. -/

/-- The action of `V` on the lamp kernel: conjugation through the section. -/
def lampKernelAction : V →* MulAut lampKernel :=
  (MulAut.conjNormal (H := lampKernel)).comp sect

theorem lampKernelAction_coe (v : V) (n : lampKernel) :
    (lampKernelAction v n : MarkedGroup) =
      sect v * (n : MarkedGroup) * (sect v)⁻¹ :=
  MulAut.conjNormal_apply (sect v) n

/-- The comparison map out of the abstract semidirect product. -/
def fromSemidirect : lampKernel ⋊[lampKernelAction] V →* MarkedGroup :=
  SemidirectProduct.lift lampKernel.subtype sect (by
    intro v
    ext n
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    exact lampKernelAction_coe v n)

@[simp] theorem fromSemidirect_apply (p : lampKernel ⋊[lampKernelAction] V) :
    fromSemidirect p = (p.left : MarkedGroup) * sect p.right := rfl

theorem fromSemidirect_bijective : Function.Bijective fromSemidirect := by
  constructor
  · refine (injective_iff_map_eq_one fromSemidirect).mpr ?_
    intro p hp
    rw [fromSemidirect_apply] at hp
    have h1 : retraction ((p.left : MarkedGroup) * sect p.right) = 1 := by
      rw [hp, map_one]
    rw [map_mul, retraction_sect] at h1
    have h2 : retraction (p.left : MarkedGroup) = 1 :=
      (mem_lampKernel_iff _).mp p.left.2
    rw [h2, one_mul] at h1
    have h3 : (p.left : MarkedGroup) = 1 := by
      rw [h1, map_one, mul_one] at hp
      exact hp
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.one_left]
      exact Subtype.ext h3
    · rw [SemidirectProduct.one_right]
      exact h1
  · intro g
    refine ⟨⟨⟨g * (sect (retraction g))⁻¹, ?_⟩, retraction g⟩, ?_⟩
    · rw [mem_lampKernel_iff, map_mul, map_inv, retraction_sect,
        mul_inv_cancel]
    · rw [fromSemidirect_apply]
      show g * (sect (retraction g))⁻¹ * sect (retraction g) = g
      group

/-- **`E ≃* N_E ⋊ V`.**  The literal group is the semidirect product of its
lamp kernel by the ascending HNN extension of the affine base. -/
def markedGroupEquivSemidirect :
    (lampKernel ⋊[lampKernelAction] V) ≃* MarkedGroup :=
  MulEquiv.ofBijective fromSemidirect fromSemidirect_bijective

@[simp] theorem markedGroupEquivSemidirect_apply
    (p : lampKernel ⋊[lampKernelAction] V) :
    markedGroupEquivSemidirect p = (p.left : MarkedGroup) * sect p.right :=
  fromSemidirect_apply p

theorem markedGroupEquivSemidirect_inl (n : lampKernel) :
    markedGroupEquivSemidirect (SemidirectProduct.inl n) =
      (n : MarkedGroup) := by
  rw [markedGroupEquivSemidirect_apply]
  show (n : MarkedGroup) * sect 1 = (n : MarkedGroup)
  rw [map_one, mul_one]

theorem markedGroupEquivSemidirect_inr (v : V) :
    markedGroupEquivSemidirect (SemidirectProduct.inr v) = sect v := by
  rw [markedGroupEquivSemidirect_apply]
  show ((1 : lampKernel) : MarkedGroup) * sect v = sect v
  rw [Subgroup.coe_one, one_mul]

/-! ## Re-association: the telescope core

`V` is itself `T ⋊ ℤ` with `T` the mapping telescope, so the split above
re-associates to `E = (N_E ⋊ T) ⋊ ℤ`.  The inner factor `N_E ⋊ T` is the
*telescope core* `E_T`, the kernel of the stable-letter exponent
`E ↠ V ↠ ℤ`; the outer `ℤ` is the stable letter.  This is the shape the
soficity endpoint wants, since it is the one with `ℤ` as a quotient.

Both halves are already in the repository: `SemidirectAssoc.assocEquiv`
supplies the re-association and `markedGroupEquivSemidirect` the split. -/

/-- The mapping telescope `T = lim→(Γ̄, conj D)` of the affine base. -/
abbrev Telescope : Type := MappingTelescope.Telescope alpha conjD_injective

/-- The action of the telescope on the lamp kernel, obtained from the
`V`-action by restriction to the level-zero copy. -/
abbrev telescopeAction : Telescope →* MulAut lampKernel :=
  SemidirectAssoc.baseAction (shiftHom alpha conjD_injective) lampKernelAction

/-! ### The telescope filtration

The levels `Γ_n` of the telescope, as an increasing exhausting chain of
subgroups each isomorphic to the affine base.  Residual finiteness of every
level is *unconditional* here and needs no conjugation argument: in the
telescope model level `n` is the range of the injective `level α hα n`, so it
is isomorphic to `gammaBar` on the nose.  This is the shape the local-embedding
lane consumes. -/

/-- The `n`-th telescope level, i.e. the `n`-th copy of the affine base. -/
abbrev telescopeLevel (n : ℕ) : Subgroup Telescope :=
  (MappingTelescope.level alpha conjD_injective n).range

theorem telescopeLevel_succ (n : ℕ) :
    telescopeLevel n ≤ telescopeLevel (n + 1) := by
  rintro g ⟨q, rfl⟩
  exact ⟨alpha q, MappingTelescope.level_succ_apply_hom alpha conjD_injective n q⟩

theorem telescopeLevel_mono : Monotone telescopeLevel :=
  monotone_nat_of_le_succ telescopeLevel_succ

theorem telescopeLevel_exhausts (g : Telescope) :
    ∃ n, g ∈ telescopeLevel n := by
  obtain ⟨⟨n, q⟩, rfl⟩ := MappingTelescope.mk_surjective alpha conjD_injective g
  exact ⟨n, q, rfl⟩

/-- Every telescope level is the affine base. -/
noncomputable def telescopeLevelEquiv (n : ℕ) : gammaBar ≃* telescopeLevel n :=
  MonoidHom.ofInjective
    (MappingTelescope.level_injective alpha conjD_injective n)

/-- **Every telescope level is residually finite**, unconditionally: the
level is the affine base, and `gammaBar` is residually finite through its
integral matrix realization. -/
theorem telescopeLevel_residuallyFinite (n : ℕ) :
    Group.ResiduallyFinite (telescopeLevel n) := by
  letI : Group.ResiduallyFinite gammaBar :=
    ExplicitIntegralLinearModel.gammaBar_residuallyFinite
  exact ExplicitIntegralLinearModel.residuallyFinite_of_mulEquiv
    (telescopeLevelEquiv n)

/-- **The telescope core** `E_T = N_E ⋊ T`: the kernel of the stable-letter
exponent of `E`. -/
abbrev TelescopeCore : Type := lampKernel ⋊[telescopeAction] Telescope

/-- The conjugation action of the stable letter on the telescope core. -/
abbrev stableAction : Multiplicative ℤ →* MulAut TelescopeCore :=
  SemidirectAssoc.outerAction (shiftHom alpha conjD_injective) lampKernelAction

/-- **`E ≃* E_T ⋊ ℤ`.**  The literal group is the telescope core extended by
the stable letter.  Composing `markedGroupEquivSemidirect` with the
re-association of `SemidirectAssoc.assocEquiv`. -/
def markedGroupEquivCoreByInt :
    MarkedGroup ≃* (TelescopeCore ⋊[stableAction] Multiplicative ℤ) :=
  markedGroupEquivSemidirect.symm.trans
    (SemidirectAssoc.assocEquiv (shiftHom alpha conjD_injective)
      lampKernelAction).symm

end

end LiteralLampKernelSplit
end GroupApproximation
