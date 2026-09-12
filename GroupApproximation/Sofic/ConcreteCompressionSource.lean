import Mathlib.GroupTheory.HNNExtension
import GroupApproximation.Sofic.TorsionFreeFullMFRadical

/-!
# A concrete torsion-free-flavoured compression source

The routing program consumes remarkably little from its source group: a
copy of a group compressed by a stable letter, a witness centralized by
the compressed copy, and one nontrivial marked commutator to protect.
This module isolates that interface as `CompressionSourceData` — the
Fournier--Facio defect datum with the simple-subgroup fields removed and
no property-(T) obligation — and then constructs it unconditionally.

The construction is the bare affine HNN skeleton.  Over any injective
endomorphism `α` of a group `Γ`, form the base `Γ × ℤ`, let the stable
letter conjugate the `Γ`-copy onto its `α`-image, and take the witness
to be the generator of the central `ℤ`-factor.  The witness commutes
with the whole base, so the compressed copy centralizes its transport;
and for any base element outside the image of `α`, the marked commutator
is a reduced word of length four in the stable letter, so Britton's
lemma — available in Mathlib as
`HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range` — keeps it
nontrivial.  No Clifford kernel, no torsion, and no simple subgroup are
involved; instantiating at the doubling map of `ℤ` gives a completely
explicit two-relator-flavoured source.

The base of the integer instance is torsion-free, and the extension is
torsion-free by the standard HNN torsion theorem (finite-order elements
are conjugate into the base).  That theorem **is** formalized, as
`HNNBritton.isPowerTorsionFree_hnn`, and it has been cashed at this very
group: `HNNBritton.isPowerTorsionFree_integerSourceGroup`, recorded in
`Sofic/BareDefectSource.lean` as
`BareDefectSourceData.integerSourceGroup_isPowerTorsionFree`.  So nothing
is missing between `integerSource` and a torsion-free certified source.
What keeps this source out of the endpoint is a different obstruction
entirely, recorded in that same file: the slimmed datum keeps property
`(T)` of the base, and this base is `ℤ`.  Property (T) is deliberately
absent here: in the routing
architecture the routed quotient receives (T) from the common-quotient
partner, and saturation makes the normal-Kazhdan hypothesis hold with
the whole quotient as the normal subgroup, so the source itself never
needs it.
-/

namespace GroupApproximation
namespace ConcreteCompressionSource

open scoped commutatorElement

universe u

noncomputable section

/-! ## The defect-only source datum -/

/-- The part of a Fournier--Facio defect datum that the compression
defect actually uses: a source mapped into an ambient group, a stable
letter compressing the image, a witness centralized by the compressed
copy, and one protected nontrivial marked commutator.  There is no
property-(T) field and no simple subgroup. -/
structure CompressionSourceData (P : Type) (E : Type u)
    [Group P] [Group E] where
  /-- The source map. -/
  iota : P →* E
  /-- The stable letter. -/
  u : E
  /-- The transported witness. -/
  s : E
  /-- Conjugation by `u` compresses the source copy into itself. -/
  compresses : ∀ p : P, ∃ q : P, u * iota p * u⁻¹ = iota q
  /-- The witness commutes with the compressed copy. -/
  commutesAfterCompression :
    ∀ p : P, Commute s (u * iota p * u⁻¹)
  /-- The protected source element. -/
  witness : P
  /-- The protected marked commutator is nontrivial. -/
  witness_commutator_ne_one : ⁅s, iota witness⁆ ≠ 1

namespace CompressionSourceData

variable {P : Type} {E : Type u} [Group P] [Group E]
    (d : CompressionSourceData P E)

/-- The transported witness is nontrivial. -/
theorem s_ne_one : d.s ≠ 1 := by
  intro hs
  apply d.witness_commutator_ne_one
  rw [hs]
  simp

/-- Supplying property (T) of the source upgrades the datum to the
marker-free Kazhdan-compression core, with root `u⁻¹ s u`. -/
def core (hT : HasKazhdanPropertyT.{0, 0} P) :
    KazhdanCompressionCore P E where
  iota := d.iota
  t := d.u
  c := d.u⁻¹ * d.s * d.u
  kazhdan := hT
  compresses := d.compresses
  comm_c p := by
    show d.u⁻¹ * d.s * d.u * d.iota p =
      d.iota p * (d.u⁻¹ * d.s * d.u)
    have h := (d.commutesAfterCompression p).eq
    calc
      d.u⁻¹ * d.s * d.u * d.iota p =
          d.u⁻¹ * (d.s * (d.u * d.iota p * d.u⁻¹)) * d.u := by
            group
      _ = d.u⁻¹ * ((d.u * d.iota p * d.u⁻¹) * d.s) * d.u := by
            rw [h]
      _ = d.iota p * (d.u⁻¹ * d.s * d.u) := by
            group

/-- The transported root of the upgraded core is the witness `s`. -/
@[simp] theorem core_transported (hT : HasKazhdanPropertyT.{0, 0} P) :
    (d.core hT).transported = d.s := by
  unfold core KazhdanCompressionCore.transported
  dsimp
  group

/-- The defect of the upgraded core is the normal closure of the marked
commutators `[s, ι(p)]`. -/
theorem core_defectNormal_eq (hT : HasKazhdanPropertyT.{0, 0} P) :
    (d.core hT).defectNormal =
      Subgroup.normalClosure
        (Set.range fun p : P ↦ ⁅d.s, d.iota p⁆) := by
  unfold KazhdanCompressionCore.defectNormal
    KazhdanCompressionCore.defectSet
  rw [d.core_transported hT]
  rfl

/-- The protected commutator lies in the compression defect of the
upgraded core. -/
theorem witness_commutator_mem_defectNormal
    (hT : HasKazhdanPropertyT.{0, 0} P) :
    ⁅d.s, d.iota d.witness⁆ ∈ (d.core hT).defectNormal := by
  rw [← d.core_transported hT]
  exact (d.core hT).defect_mem_defectNormal d.witness

end CompressionSourceData

/-- Forgetting the simple subgroup and property (T) of a Fournier--Facio
defect datum leaves a compression source datum. -/
def ofFournierFacio {P : Type} {E : Type u} [Group P] [Group E]
    (D : FournierFacioDefectData P E) : CompressionSourceData P E where
  iota := D.iota
  u := D.u
  s := D.s
  compresses := D.compresses
  commutesAfterCompression := D.commutesAfterCompression
  witness := D.witness
  witness_commutator_ne_one := D.witness_commutator_ne_one

/-- The forgetful map is compatible with the hidden compression cores. -/
@[simp] theorem ofFournierFacio_core {P : Type} {E : Type u} [Group P] [Group E]
    (D : FournierFacioDefectData P E) :
    (ofFournierFacio D).core D.kazhdan = D.core := rfl

/-! ## The affine HNN source over an injective endomorphism -/

section AffineHNN

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The base of the affine HNN skeleton: the source times a central
infinite cyclic witness direction. -/
abbrev Base (Γ : Type) : Type := Γ × Multiplicative ℤ

/-- The base copy of the source. -/
def baseInl : Γ →* Base Γ := MonoidHom.inl Γ (Multiplicative ℤ)

@[simp] theorem baseInl_apply (γ : Γ) :
    baseInl γ = (γ, (1 : Multiplicative ℤ)) := rfl

theorem baseInl_injective :
    Function.Injective (baseInl (Γ := Γ)) := fun _ _ h =>
  congrArg Prod.fst h

include hα in
theorem baseInlComp_injective :
    Function.Injective ⇑((baseInl (Γ := Γ)).comp α) := fun _ _ h =>
  hα (baseInl_injective h)

/-- The unmoved associated subgroup: the base copy of the source. -/
abbrev sourceA : Subgroup (Base Γ) := (baseInl (Γ := Γ)).range

/-- The moved associated subgroup: the base copy of the `α`-image. -/
abbrev sourceB : Subgroup (Base Γ) := ((baseInl (Γ := Γ)).comp α).range

/-- The associated-subgroup isomorphism induced by `α`. -/
def sourceEquiv : (sourceA (Γ := Γ)) ≃* sourceB α :=
  (MonoidHom.ofInjective (baseInl_injective (Γ := Γ))).symm.trans
    (MonoidHom.ofInjective (baseInlComp_injective α hα))

/-- The affine HNN skeleton of the endomorphism `α`. -/
abbrev SourceGroup : Type :=
  HNNExtension (Base Γ) (sourceA (Γ := Γ)) (sourceB α) (sourceEquiv α hα)

/-- The central witness of the base: the generator of the cyclic
direction. -/
def cZ : Base Γ := ((1 : Γ), Multiplicative.ofAdd (1 : ℤ))

theorem cZ_mul_comm (g : Base Γ) : cZ * g = g * cZ := by
  obtain ⟨x, y⟩ := g
  show ((1 : Γ) * x, Multiplicative.ofAdd (1 : ℤ) * y) =
    (x * 1, y * Multiplicative.ofAdd (1 : ℤ))
  rw [one_mul, mul_one]
  exact congrArg (Prod.mk x) (mul_comm _ y)

theorem cZ_not_mem_sourceA : (cZ : Base Γ) ∉ sourceA (Γ := Γ) := by
  intro hmem
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp hmem
  have h2 : (1 : Multiplicative ℤ) = Multiplicative.ofAdd (1 : ℤ) :=
    congrArg Prod.snd hγ
  have h3 : (0 : ℤ) = 1 :=
    congrArg (fun z : Multiplicative ℤ => z.toAdd) h2
  exact zero_ne_one h3

theorem cZ_inv_not_mem_sourceA :
    (cZ : Base Γ)⁻¹ ∉ sourceA (Γ := Γ) := by
  intro hmem
  have h2 := (sourceA (Γ := Γ)).inv_mem hmem
  rw [inv_inv] at h2
  exact cZ_not_mem_sourceA h2

theorem baseInl_not_mem_sourceB {γ₀ : Γ}
    (hγ₀ : γ₀ ∉ Set.range α) : baseInl γ₀ ∉ sourceB α := by
  intro hmem
  obtain ⟨δ, hδ⟩ := MonoidHom.mem_range.mp hmem
  exact hγ₀ ⟨δ, baseInl_injective hδ⟩

/-- **The compression relation.**  The stable letter conjugates the base
copy of the source onto the base copy of its `α`-image. -/
theorem stable_compress (γ : Γ) :
    (HNNExtension.t : SourceGroup α hα) *
      HNNExtension.of (baseInl γ) * HNNExtension.t⁻¹ =
      HNNExtension.of (baseInl (α γ)) := by
  have h := HNNExtension.equiv_eq_conj (φ := sourceEquiv α hα)
    ((MonoidHom.ofInjective (baseInl_injective (Γ := Γ))) γ)
  have hcoe1 : (((MonoidHom.ofInjective
      (baseInl_injective (Γ := Γ))) γ : sourceA (Γ := Γ)) : Base Γ) =
      baseInl γ :=
    MonoidHom.ofInjective_apply _
  have hcoe2 : ((sourceEquiv α hα
      ((MonoidHom.ofInjective (baseInl_injective (Γ := Γ))) γ) :
      sourceB α) : Base Γ) = baseInl (α γ) := by
    show ((((MonoidHom.ofInjective
        (baseInl_injective (Γ := Γ))).symm.trans
        (MonoidHom.ofInjective (baseInlComp_injective α hα)))
        ((MonoidHom.ofInjective (baseInl_injective (Γ := Γ))) γ) :
        sourceB α) : Base Γ) = baseInl (α γ)
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MonoidHom.ofInjective_apply]
    rfl
  rw [hcoe1, hcoe2] at h
  exact h.symm

/-- **W2 for the affine skeleton.**  The transported witness commutes
with the whole compressed copy, because the witness is central in the
base. -/
theorem commute_tct_compressed (γ : Γ) :
    Commute
      ((HNNExtension.t : SourceGroup α hα) * HNNExtension.of cZ *
        HNNExtension.t⁻¹)
      (HNNExtension.t * HNNExtension.of (baseInl γ) *
        HNNExtension.t⁻¹) := by
  have hbase : (cZ : Base Γ) * baseInl γ = baseInl γ * cZ :=
    cZ_mul_comm (baseInl γ)
  have hmain :
      ((HNNExtension.t : SourceGroup α hα) * HNNExtension.of cZ *
        HNNExtension.t⁻¹) *
      (HNNExtension.t * HNNExtension.of (baseInl γ) *
        HNNExtension.t⁻¹) =
      (HNNExtension.t * HNNExtension.of (baseInl γ) *
        HNNExtension.t⁻¹) *
      (HNNExtension.t * HNNExtension.of cZ * HNNExtension.t⁻¹) := by
    calc ((HNNExtension.t : SourceGroup α hα) * HNNExtension.of cZ *
          HNNExtension.t⁻¹) *
        (HNNExtension.t * HNNExtension.of (baseInl γ) *
          HNNExtension.t⁻¹) =
        HNNExtension.t *
          (HNNExtension.of cZ * HNNExtension.of (baseInl γ)) *
          HNNExtension.t⁻¹ := by
          group
      _ = HNNExtension.t * HNNExtension.of (cZ * baseInl γ) *
          HNNExtension.t⁻¹ := by
          rw [← map_mul]
      _ = HNNExtension.t * HNNExtension.of (baseInl γ * cZ) *
          HNNExtension.t⁻¹ := by
          rw [hbase]
      _ = HNNExtension.t *
          (HNNExtension.of (baseInl γ) * HNNExtension.of cZ) *
          HNNExtension.t⁻¹ := by
          rw [map_mul]
      _ = (HNNExtension.t * HNNExtension.of (baseInl γ) *
          HNNExtension.t⁻¹) *
          (HNNExtension.t * HNNExtension.of cZ *
            HNNExtension.t⁻¹) := by
          group
  exact hmain

/-! ## The Britton certificate -/

/-- The length-four reduced word certifying the protected commutator:
`t · cZ · t⁻¹ · γ₀ · t · cZ⁻¹ · t⁻¹ · γ₀⁻¹`.  The chain condition holds
because `cZ` and its inverse are outside the unmoved subgroup and `γ₀`
is outside the moved subgroup. -/
def brittonWord {γ₀ : Γ} (hγ₀ : γ₀ ∉ Set.range α) :
    HNNExtension.NormalWord.ReducedWord (Base Γ) (sourceA (Γ := Γ)) (sourceB α) where
  head := 1
  toList :=
    [((1 : ℤˣ), cZ), (-1, baseInl γ₀), (1, cZ⁻¹), (-1, (baseInl γ₀)⁻¹)]
  chain := by
    refine List.isChain_cons.2 ⟨?_, List.isChain_cons.2 ⟨?_,
      List.isChain_cons.2 ⟨?_, List.isChain_singleton _⟩⟩⟩
    · intro y _ hmem
      exact absurd hmem cZ_not_mem_sourceA
    · intro y _ hmem
      exact absurd hmem (baseInl_not_mem_sourceB α hγ₀)
    · intro y _ hmem
      exact absurd hmem cZ_inv_not_mem_sourceA

@[simp] theorem brittonWord_toList {γ₀ : Γ} (hγ₀ : γ₀ ∉ Set.range α) :
    (brittonWord α hγ₀).toList =
      [((1 : ℤˣ), cZ), (-1, baseInl γ₀), (1, cZ⁻¹),
        (-1, (baseInl γ₀)⁻¹)] := rfl

/-- The Britton word multiplies out to the protected commutator. -/
theorem brittonWord_prod {γ₀ : Γ} (hγ₀ : γ₀ ∉ Set.range α) :
    (brittonWord α hγ₀).prod (sourceEquiv α hα) =
      ⁅(HNNExtension.t : SourceGroup α hα) * HNNExtension.of cZ *
        HNNExtension.t⁻¹, HNNExtension.of (baseInl γ₀)⁆ := by
  have hval1 : ((1 : ℤˣ) : ℤ) = 1 := rfl
  have hvalm : (((-1 : ℤˣ)) : ℤ) = -1 := rfl
  rw [commutatorElement_def]
  simp only [brittonWord, HNNExtension.NormalWord.ReducedWord.prod, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, hval1, hvalm, map_one,
    map_inv]
  group

/-- **Britton nontriviality.**  For any base element outside the image
of `α`, the protected commutator of the affine skeleton survives. -/
theorem commutator_tct_ne_one {γ₀ : Γ} (hγ₀ : γ₀ ∉ Set.range α) :
    ⁅(HNNExtension.t : SourceGroup α hα) * HNNExtension.of cZ *
      HNNExtension.t⁻¹,
      (HNNExtension.of (baseInl γ₀) : SourceGroup α hα)⁆ ≠ 1 := by
  intro hone
  have hmem : (brittonWord α hγ₀).prod (sourceEquiv α hα) ∈
      (HNNExtension.of.range : Subgroup (SourceGroup α hα)) := by
    rw [brittonWord_prod α hα hγ₀, hone]
    exact ⟨1, map_one _⟩
  have hnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    (φ := sourceEquiv α hα) (brittonWord α hγ₀) hmem
  rw [brittonWord_toList α hγ₀] at hnil
  exact List.cons_ne_nil _ _ hnil

/-- **The affine HNN skeleton is an unconditional compression source.**
Any injective endomorphism with an element outside its image yields a
source datum: no property (T), no simple subgroup, no torsion in the
witness. -/
def sourceData {γ₀ : Γ} (hγ₀ : γ₀ ∉ Set.range α) :
    CompressionSourceData Γ (SourceGroup α hα) where
  iota := HNNExtension.of.comp (baseInl (Γ := Γ))
  u := HNNExtension.t
  s := HNNExtension.t * HNNExtension.of cZ * HNNExtension.t⁻¹
  compresses := fun p => ⟨α p, stable_compress α hα p⟩
  commutesAfterCompression := fun p => commute_tct_compressed α hα p
  witness := γ₀
  witness_commutator_ne_one := commutator_tct_ne_one α hα hγ₀

end AffineHNN

/-! ## The integer doubling instance -/

section IntegerInstance

/-- The doubling endomorphism of the infinite cyclic group. -/
def doubling : Multiplicative ℤ →* Multiplicative ℤ :=
  zpowGroupHom 2

theorem doubling_injective : Function.Injective ⇑doubling := by
  intro a b h
  have h1 := congrArg (fun z : Multiplicative ℤ => z.toAdd) h
  simp only [doubling, zpowGroupHom_apply, toAdd_zpow, zsmul_eq_mul,
    Int.cast_id] at h1
  exact Multiplicative.toAdd.injective
    (mul_left_cancel₀ (two_ne_zero (α := ℤ)) h1)

theorem ofAdd_one_not_mem_range_doubling :
    Multiplicative.ofAdd (1 : ℤ) ∉ Set.range doubling := by
  rintro ⟨x, hx⟩
  have h1 := congrArg (fun z : Multiplicative ℤ => z.toAdd) hx
  simp only [doubling, zpowGroupHom_apply, toAdd_zpow, zsmul_eq_mul,
    Int.cast_id, toAdd_ofAdd] at h1
  omega

/-- The infinite cyclic group is torsion-free in the power sense. -/
theorem isPowerTorsionFree_multiplicative_int :
    IsPowerTorsionFree (Multiplicative ℤ) := by
  intro g n hn hpow
  have h1 := congrArg (fun z : Multiplicative ℤ => z.toAdd) hpow
  simp only [toAdd_pow, toAdd_one, nsmul_eq_mul] at h1
  have h3 : Multiplicative.toAdd g = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (Int.natCast_eq_zero.mp h) hn.ne'
    · exact h
  apply Multiplicative.toAdd.injective
  rw [h3, toAdd_one]

/-- The base of the integer instance is torsion-free. -/
theorem base_isPowerTorsionFree :
    IsPowerTorsionFree (Base (Multiplicative ℤ)) :=
  isPowerTorsionFree_multiplicative_int.prod
    isPowerTorsionFree_multiplicative_int

/-- **The explicit integer source.**  The affine HNN skeleton of the
doubling map on `ℤ`, with the generator as protected element, is a
completely explicit unconditional compression source datum.  Its base is
torsion-free; torsion-freeness of the whole skeleton awaits the HNN
torsion theorem. -/
def integerSource :
    CompressionSourceData (Multiplicative ℤ)
      (SourceGroup doubling doubling_injective) :=
  sourceData doubling doubling_injective ofAdd_one_not_mem_range_doubling

/-- The protected commutator of the integer source is nontrivial. -/
theorem integerSource_witness_commutator_ne_one :
    ⁅integerSource.s, integerSource.iota integerSource.witness⁆ ≠ 1 :=
  integerSource.witness_commutator_ne_one

end IntegerInstance

end
end ConcreteCompressionSource
end GroupApproximation
