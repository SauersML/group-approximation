import GroupApproximation.Sofic.TorsionFreeFullMFConsequences

/-!
# Hereditary nonsoficity: the abstract descent

The routed quotient of the Fournier--Facio construction has full MF
radical, and that property passes to every quotient.  This module
isolates how much of the NONSOFICITY conclusion descends abstractly —
with no small cancellation and no geometry, only simplicity and
saturation.

Three layers, in decreasing strength of what is proved outright.

* **Exactness.**  The hidden compression defect of a Fournier--Facio
  datum is EXACTLY the normal closure of the embedded simple factor:
  one inclusion is the formalized defect saturation, and conversely
  every displayed commutator `[s, ι(p)]` is a product of two conjugates
  of elements of the simple factor.  No hypotheses.

* **Survival.**  In every nontrivial quotient of the routed group, the
  simple factor injects.  Its image cannot die: killing it kills its
  normal closure, hence by exactness the whole defect, whose image is
  the whole routed quotient by the routing datum — so the quotient
  would be trivial.  Simplicity then forces the restriction to be
  injective.  Consequently, if the simple factor is itself nonsofic,
  EVERY nontrivial quotient of the routed group is nonsofic, because
  soficity passes to subgroups.  No hypotheses beyond the routing.

* **Descent of the criterion.**  The Fournier--Facio nonsoficity
  criterion consumes a `CompressionSetup`.  All of its fields descend
  along a surjection except two injectivity constraints: that the
  Kazhdan copy stays injective, and that the compressed copy and the
  commuting copy stay disjoint.  Those two facts are genuinely
  construction-dependent — a further quotient may fold the Kazhdan
  base — so they are packaged as the retention fields of
  `HereditaryNonsoficData`, proof-carrying data in the sense of the
  routing interfaces, never axioms.  Given retention, every nontrivial
  quotient of the routed group is nonsofic.

The three layers make the trusted boundary exact: hereditary
non-MF-ness is unconditional (proved elsewhere from the routing datum),
hereditary nonsoficity is unconditional once the simple factor is
nonsofic, and otherwise costs precisely the retention of the two
injectivity constraints of the compression configuration.
-/

namespace GroupApproximation
namespace HereditaryNonsoficDescent

open scoped commutatorElement

universe u v

/-! ## Exactness: the defect is the normal closure of the simple factor -/

section Exactness

variable {P : Type} {E : Type u} [Group P] [Group E]
    (D : FournierFacioDefectData P E)

/-- **Exactness.**  The hidden compression defect of a Fournier--Facio
datum is precisely the normal closure of the embedded simple factor.
Saturation gives one inclusion; for the other, each displayed
commutator `[s, ι(p)] = s · (ι(p) s⁻¹ ι(p)⁻¹)` is a product of two
conjugates of simple-factor elements. -/
theorem defectNormal_eq_normalClosure_simpleSubgroup :
    D.core.defectNormal =
      Subgroup.normalClosure (D.simpleSubgroup : Set E) := by
  refine le_antisymm ?_ ?_
  · rw [D.core_defectNormal_eq]
    refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨p, rfl⟩
    have hs : D.s ∈ Subgroup.normalClosure (D.simpleSubgroup : Set E) :=
      Subgroup.subset_normalClosure D.s_mem
    have hconj : D.iota p * D.s⁻¹ * (D.iota p)⁻¹ ∈
        Subgroup.normalClosure (D.simpleSubgroup : Set E) :=
      Subgroup.normalClosure_normal.conj_mem _ (inv_mem hs) (D.iota p)
    have hsplit : ⁅D.s, D.iota p⁆ =
        D.s * (D.iota p * D.s⁻¹ * (D.iota p)⁻¹) := by
      rw [commutatorElement_def]
      group
    simp only [hsplit]
    exact mul_mem hs hconj
  · refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    exact D.simpleSubgroup_le_defectNormal hx

end Exactness

/-! ## Survival: the simple factor injects into every nontrivial quotient -/

section Survival

variable {P : Type} {E : Type u} [Group P] [Group E]
    {D : FournierFacioDefectData P E}
    (R : DefectRoutingData.{u} D)

local instance survivalQuotientGroup : Group R.Quotient := R.groupQuotient

/-- The simple factor cannot map into the kernel of a nontrivial quotient
of the routed group: its normal closure is the defect, and the defect
maps onto everything. -/
theorem simpleSubgroup_not_le_ker {H : Type v} [Group H] [Nontrivial H]
    (q : R.Quotient →* H) (hq : Function.Surjective q) :
    ¬ D.simpleSubgroup ≤ (q.comp R.quotient).ker := by
  intro hle
  have hncl : Subgroup.normalClosure (D.simpleSubgroup : Set E) ≤
      (q.comp R.quotient).ker :=
    Subgroup.normalClosure_le_normal fun x hx => hle hx
  have hker : D.core.defectNormal ≤ (q.comp R.quotient).ker := by
    rw [defectNormal_eq_normalClosure_simpleSubgroup D]
    exact hncl
  obtain ⟨h, hne⟩ := exists_ne (1 : H)
  obtain ⟨y, rfl⟩ := hq h
  have hy : y ∈ Subgroup.map R.quotient D.core.defectNormal := by
    rw [R.defect_surjective]
    exact Subgroup.mem_top y
  obtain ⟨x, hx, rfl⟩ := hy
  apply hne
  exact MonoidHom.mem_ker.mp (hker hx)

/-- **Survival.**  In every nontrivial quotient of the routed group, the
embedded simple factor injects: its restriction has a normal kernel,
simplicity leaves only bottom or top, and top is excluded by
saturation. -/
theorem simpleSubgroup_hom_injective {H : Type v} [Group H] [Nontrivial H]
    (q : R.Quotient →* H) (hq : Function.Surjective q) :
    Function.Injective
      ⇑((q.comp R.quotient).comp D.simpleSubgroup.subtype) := by
  letI : IsSimpleGroup D.simpleSubgroup := D.simple
  set φ := (q.comp R.quotient).comp D.simpleSubgroup.subtype with hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker inferInstance with
    hbot | htop
  · intro a b hab
    have hmem : a * b⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    rw [hbot] at hmem
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)
  · exfalso
    refine simpleSubgroup_not_le_ker R q hq ?_
    intro y hy
    have hyk : (⟨y, hy⟩ : D.simpleSubgroup) ∈ φ.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hyk)

/-- The simple factor embeds into every nontrivial quotient of the
routed group. -/
theorem exists_simpleSubgroup_embedding {H : Type v} [Group H]
    [Nontrivial H] (q : R.Quotient →* H) (hq : Function.Surjective q) :
    ∃ f : D.simpleSubgroup →* H, Function.Injective f :=
  ⟨(q.comp R.quotient).comp D.simpleSubgroup.subtype,
    simpleSubgroup_hom_injective R q hq⟩

/-- **Unconditional hereditary nonsoficity from a nonsofic simple
factor.**  Soficity passes to subgroups, and the simple factor embeds
into every nontrivial quotient of the routed group. -/
theorem quotient_not_isSofic_of_simpleSubgroup_not_isSofic
    (hS : ¬ IsSofic D.simpleSubgroup) {H : Type v} [Group H] [Nontrivial H]
    (q : R.Quotient →* H) (hq : Function.Surjective q) :
    ¬ IsSofic H :=
  fun hH => hS (isSofic_of_injective _
    (simpleSubgroup_hom_injective R q hq) hH)

end Survival

/-! ## Descent of the compression setup along a surjection -/

section Descend

variable {G H Γ J : Type*} [Group G] [Group H] [Group Γ] [Group J]

/-- Push a compression setup through a surjective homomorphism.  Every
field descends by functoriality except the two injectivity constraints,
which are consumed as hypotheses: the descended Kazhdan copy must stay
injective, and the compressed copy must stay disjoint from the
commuting copy.  Compressors descend to their images; the compressing
endomorphisms are chosen through preimages, and the defining equation
holds for any choice. -/
noncomputable def descendSetup (C : CompressionSetup G Γ J) (q : G →* H)
    (hq : Function.Surjective q)
    (hinj : Function.Injective ⇑(q.comp C.embedΓ))
    (hdisj : ∀ (g : Γ) (j : J),
      q (C.distinguished * C.embedΓ g * C.distinguished⁻¹) =
        q (C.embedΓ (C.embedJ j)) → g = 1 ∧ j = 1) :
    CompressionSetup H Γ J :=
  letI : DecidableEq H := Classical.decEq H
  { embedΓ := q.comp C.embedΓ
    embedΓ_injective := hinj
    embedJ := C.embedJ
    embedJ_injective := C.embedJ_injective
    generatorsΓ := C.generatorsΓ
    generatorsΓ_one := C.generatorsΓ_one
    generatorsΓ_symmetric := C.generatorsΓ_symmetric
    generatorsΓ_generate := C.generatorsΓ_generate
    generatorsJ := C.generatorsJ
    generatorsJ_generate := C.generatorsJ_generate
    infiniteΓ := C.infiniteΓ
    compressors := C.compressors.image ⇑q
    distinguished := q C.distinguished
    distinguished_mem := Finset.mem_image_of_mem ⇑q C.distinguished_mem
    compressedEnd := fun r hr =>
      C.compressedEnd (Finset.mem_image.mp hr).choose
        (Finset.mem_image.mp hr).choose_spec.1
    compressedEnd_spec := by
      intro r hr g
      obtain ⟨hmem, hqr⟩ := (Finset.mem_image.mp hr).choose_spec
      have happ := congrArg q (C.compressedEnd_spec
        (Finset.mem_image.mp hr).choose hmem g)
      rw [map_mul, map_mul, map_inv, hqr] at happ
      exact happ
    generates := by
      have htop : Subgroup.map q (⊤ : Subgroup G) = ⊤ := by
        apply top_unique
        intro y _
        obtain ⟨x, rfl⟩ := hq y
        exact ⟨x, Subgroup.mem_top x, rfl⟩
      have hmap : Subgroup.closure
          (⇑q '' (Set.range ⇑C.embedΓ ∪ ↑C.compressors)) = ⊤ := by
        rw [← MonoidHom.map_closure, C.generates, htop]
      rw [Set.image_union] at hmap
      have hr : ⇑q '' Set.range ⇑C.embedΓ =
          Set.range ⇑(q.comp C.embedΓ) := by
        rw [MonoidHom.coe_comp]
        exact (Set.range_comp ⇑q ⇑C.embedΓ).symm
      rw [hr, ← Finset.coe_image] at hmap
      exact hmap
    centralizes := by
      intro g j
      have h := (C.centralizes g j).map q
      rw [map_mul, map_mul, map_inv] at h
      exact h
    disjoint := by
      intro g j h
      apply hdisj g j
      rw [map_mul, map_mul, map_inv]
      exact h }

end Descend

/-! ## The retained-configuration interface and hereditary nonsoficity -/

section Hereditary

variable {P : Type} {E : Type u} [Group P] [Group E]
    {D : FournierFacioDefectData P E}
    (R : DefectRoutingData.{u} D)

local instance hereditaryQuotientGroup : Group R.Quotient := R.groupQuotient

/-- The nonsoficity input of the routed group, together with the exact
residue of construction-dependent information needed for descent: in
every nontrivial quotient, the Kazhdan copy of the compression setup
stays injective, and the compressed copy stays disjoint from the
commuting copy.  These are the only two fields of `CompressionSetup`
which do not descend by functoriality; everything else — property
`(T)` of the ambient group and of the Kazhdan copy, generation, the
compressing endomorphisms, the non-LEF witness — is proved to descend.
In the intended application both retention fields are conclusions of
the relative small-cancellation construction, recorded here as
proof-carrying data rather than assumed as axioms. -/
structure HereditaryNonsoficData extends
    DefectRoutingData.NonsoficCriterionData R where
  retainsInjective : ∀ (H : Type) [Group H] (q : R.Quotient →* H),
    Function.Surjective q → Nontrivial H →
      Function.Injective ⇑(q.comp setup.embedΓ)
  retainsDisjoint : ∀ (H : Type) [Group H] (q : R.Quotient →* H),
    Function.Surjective q → Nontrivial H →
      ∀ (g : Gamma) (j : J),
        q (setup.distinguished * setup.embedΓ g *
            setup.distinguished⁻¹) =
          q (setup.embedΓ (setup.embedJ j)) → g = 1 ∧ j = 1

namespace HereditaryNonsoficData

variable (N : HereditaryNonsoficData R)

include N

/-- The routed group itself is nonsofic. -/
theorem not_isSofic_routed : ¬ IsSofic R.Quotient :=
  N.toNonsoficCriterionData.not_isSofic

/-- **Hereditary nonsoficity.**  Under retention, every nontrivial
quotient of the routed group is nonsofic: the compression setup
descends, property `(T)` passes to the quotient, and the non-LEF
witness is unchanged. -/
theorem quotient_not_isSofic {H : Type} [Group H] [Nontrivial H]
    (q : R.Quotient →* H) (hq : Function.Surjective q) :
    ¬ IsSofic H := by
  letI : Group N.Gamma := N.groupGamma
  letI : Group N.J := N.groupJ
  letI : Countable N.Gamma := N.countableGamma
  letI : Countable N.J := N.countableJ
  letI : Countable R.Quotient := R.quotientCountable
  letI : Countable H := hq.countable
  have hTH : HasKazhdanPropertyT.{0, 0} H :=
    HasKazhdanPropertyT.of_surjective q hq R.kazhdan
  exact not_isSofic_of_not_isLEF
    (descendSetup N.setup q hq
      (N.retainsInjective H q hq inferInstance)
      (N.retainsDisjoint H q hq inferInstance))
    hTH N.gammaKazhdan N.witness_not_isLEF

/-- The full hereditary package for a nontrivial quotient: full corona
MF radical, failure of both MF conventions, and nonsoficity. -/
theorem hereditary_package {H : Type} [Group H] [Countable H]
    [Nontrivial H]
    (q : R.Quotient →* H) (hq : Function.Surjective q) :
    coronaMFResidual H = ⊤ ∧
      ¬ IsOperatorMF H ∧
      ¬ IsCDEOperatorMF H ∧
      ¬ IsSofic H := by
  letI : Countable R.Quotient := R.quotientCountable
  exact ⟨R.quotient_coronaMFResidual_eq_top q hq,
    R.quotient_not_isOperatorMF q hq,
    R.quotient_not_isCDEOperatorMF q hq,
    N.quotient_not_isSofic R q hq⟩

end HereditaryNonsoficData

end Hereditary

end HereditaryNonsoficDescent
end GroupApproximation
