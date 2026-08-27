import GroupApproximation.Sofic.MappingTelescopeFiniteOrbits
import GroupApproximation.Monsters.AffineSL3Doubling
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Group

/-!
# The site set and its orbital block geometry

This file formalises §4 of `notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md`
("The site set and the orbital graph") for the ascending-HNN model
`V = Vertical α hα` of an arbitrary injective endomorphism `α : Γ →* Γ`.

The manuscript coordinatises the site set as

    X = V/B ≅ ⨆_{n ∈ ℤ} ℤ[1/2]³ / 2ⁿℤ³ ,

the class of `t τⁿ B` being `(n, [u] mod 2ⁿℤ³)`.  We do not build that
coordinate type: everything §4 asserts is a statement about the *subgroup
tower* `B ≤ B₁ = τ⁻¹Bτ ≤ V`, and stating it there keeps the whole
development free of any identification of the base with a matrix group.
The dictionary is:

* a site is a coset in `Cosets α hα = V ⧸ B` (the repo's existing site type);
* `levelOf` is the coordinate `n`, the `τ`-exponent (Proposition 4.1);
* a *block* is a coset in `Block = V ⧸ B₁`, and `blockOf` is the projection
  `V/B → V/B₁`, whose fibres are exactly the manuscript's cosets of
  `2^{n-1}ℤ³/2ⁿℤ³` (Proposition 4.2);
* `blockEquivCosets : Block ≃ Cosets` is the `V`-isomorphism `I ≅ X`,
  right translation by `τ⁻¹`, which lowers the level by one;
* `blockStabilizer_eq_level` identifies the stabiliser of the base block
  with the telescope level `B₁`, and `blockSiteAction` is its action on the
  eight sites of that block;
* `baseBlockEquiv` identifies those eight sites `V`-equivariantly with
  `Γ ⧸ α.range`; in the concrete affine model `Γ ⧸ α.range ≅ ℤ³/2ℤ³` by
  `AffineSL3Doubling.cosetEquiv`, which is the manuscript's `AGL₃(𝔽₂)`
  picture.

The orbital graph `𝒢` of §3 is `Adj`: the `V`-orbit of the marked pair
`{τo, v₁τo}`.  Its edges always stay inside a block (`adj_blockOf_eq`,
unconditional).  That each block is a *complete* graph — equivalently that
`𝒢` is `7`-regular — is the manuscript's `[audit-fix]` finite computation
that `⟨x̄,ȳ,z̄⟩ ≤ GL₃(𝔽₂)` is transitive on the seven nonzero classes; here it
appears as the explicit hypothesis `AlphaCosetTransitive`, which is proved
outright for the concrete affine doubling in the final section.
-/

universe u

namespace GroupApproximation
namespace LiteralBlockGeometry

open MappingTelescope MarkedCompression MappingTelescopeFiniteOrbits
open SemidirectProduct

section Abstract

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-! ## The block subgroup `B₁ = τ⁻¹Bτ` -/

/-- The stabiliser of a block: telescope level one, i.e. `B₁ = τ⁻¹Bτ`. -/
abbrev blockSubgroup : Subgroup (Vertical α hα) := verticalLevel α hα 1

/-- Level one is exactly the `τ`-conjugate of the base copy. -/
theorem mem_blockSubgroup_iff (v : Vertical α hα) :
    v ∈ blockSubgroup α hα ↔
      ∃ x : Γ, (tVertical α hα)⁻¹ * iotaVertical α hα x * tVertical α hα = v := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, tVertical_inv_conj α hα x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, (tVertical_inv_conj α hα x).symm⟩

/-- The base copy sits inside level one, because `α` compresses it. -/
theorem iotaVertical_mem_blockSubgroup (γ : Γ) :
    iotaVertical α hα γ ∈ blockSubgroup α hα := by
  refine (mem_blockSubgroup_iff α hα _).mpr ⟨α γ, ?_⟩
  rw [← vertical_compress α hα γ]
  group

/-- `B ≤ B₁`. -/
theorem baseSubgroup_le_blockSubgroup :
    baseSubgroup α hα ≤ blockSubgroup α hα := by
  rintro v ⟨γ, rfl⟩
  exact iotaVertical_mem_blockSubgroup α hα γ

/-- A `τ`-conjugate of a base element lands back in the base exactly on the
range of `α`.  This is the one arithmetic fact the whole block geometry
rests on. -/
theorem tconj_mem_base_iff (z : Γ) :
    (tVertical α hα)⁻¹ * iotaVertical α hα z * tVertical α hα ∈ baseSubgroup α hα ↔
      z ∈ Set.range α := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply iotaVertical_injective α hα
    rw [← vertical_compress α hα y, hy]
    group
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [← vertical_compress α hα y]
    group

/-- Membership in level one is detected after conjugating back down. -/
theorem mem_blockSubgroup_conj_iff (v : Vertical α hα) :
    v ∈ blockSubgroup α hα ↔
      tVertical α hα * v * (tVertical α hα)⁻¹ ∈ baseSubgroup α hα := by
  rw [mem_blockSubgroup_iff]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    group
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hx]
    group

/-! ## Blocks -/

/-- The block set `I = V ⧸ B₁`.  By `blockEquivCosets` it is `V`-isomorphic
to the site set itself, a block at level `n` corresponding to a site at
level `n - 1`. -/
abbrev Block : Type u := Vertical α hα ⧸ blockSubgroup α hα

instance : MulAction (Vertical α hα) (Block α hα) :=
  inferInstanceAs (MulAction (Vertical α hα)
    (Vertical α hα ⧸ blockSubgroup α hα))

/-- The block containing a site. -/
def blockOf : Cosets α hα → Block α hα :=
  Subgroup.quotientMapOfLE (baseSubgroup_le_blockSubgroup α hα)

@[simp] theorem blockOf_mk (g : Vertical α hα) :
    blockOf α hα (QuotientGroup.mk g) = QuotientGroup.mk g := rfl

theorem blockOf_surjective : Function.Surjective (blockOf α hα) := by
  intro i
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective i
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- `blockOf` is `V`-equivariant. -/
theorem blockOf_smul (v : Vertical α hα) (x : Cosets α hα) :
    blockOf α hα (v • x) = v • blockOf α hα x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, blockOf_mk]

/-! ## The block set is `V`-isomorphic to the site set

Right translation by `τ⁻¹` carries `V ⧸ B₁ = V ⧸ τ⁻¹Bτ` onto `V ⧸ B`.  In
the manuscript's coordinates this is the level shift `n ↦ n - 1` of
Proposition 4.2. -/

/-- The `V`-isomorphism `I ≅ X` of Proposition 4.2. -/
def blockEquivCosets : Block α hα ≃ Cosets α hα where
  toFun :=
    Quotient.map' (fun g => g * (tVertical α hα)⁻¹) (by
      intro p q hpq
      rw [QuotientGroup.leftRel_apply] at hpq
      apply QuotientGroup.leftRel_apply.mpr
      have h := (mem_blockSubgroup_conj_iff α hα (p⁻¹ * q)).mp hpq
      have heq : (p * (tVertical α hα)⁻¹)⁻¹ * (q * (tVertical α hα)⁻¹) =
          tVertical α hα * (p⁻¹ * q) * (tVertical α hα)⁻¹ := by group
      rw [heq]
      exact h)
  invFun :=
    Quotient.map' (fun g => g * tVertical α hα) (by
      intro p q hpq
      rw [QuotientGroup.leftRel_apply] at hpq
      apply QuotientGroup.leftRel_apply.mpr
      refine (mem_blockSubgroup_conj_iff α hα _).mpr ?_
      have heq : tVertical α hα *
          ((p * tVertical α hα)⁻¹ * (q * tVertical α hα)) *
          (tVertical α hα)⁻¹ = p⁻¹ * q := by group
      rw [heq]
      exact hpq)
  left_inv := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    show (QuotientGroup.mk (g * (tVertical α hα)⁻¹ * tVertical α hα) :
        Block α hα) = QuotientGroup.mk g
    rw [inv_mul_cancel_right]
  right_inv := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    show (QuotientGroup.mk (g * tVertical α hα * (tVertical α hα)⁻¹) :
        Cosets α hα) = QuotientGroup.mk g
    rw [mul_inv_cancel_right]

@[simp] theorem blockEquivCosets_mk (g : Vertical α hα) :
    blockEquivCosets α hα (QuotientGroup.mk g) =
      QuotientGroup.mk (g * (tVertical α hα)⁻¹) := rfl

@[simp] theorem blockEquivCosets_symm_mk (g : Vertical α hα) :
    (blockEquivCosets α hα).symm (QuotientGroup.mk g) =
      QuotientGroup.mk (g * tVertical α hα) := rfl

/-- The isomorphism `I ≅ X` is `V`-equivariant. -/
theorem blockEquivCosets_smul (v : Vertical α hα) (i : Block α hα) :
    blockEquivCosets α hα (v • i) = v • blockEquivCosets α hα i := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective i
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, blockEquivCosets_mk, mul_assoc]

/-! ## The level coordinate

The first coordinate of Proposition 4.1: the `τ`-exponent.  It is defined on
sites because the base copy lies in the kernel of the projection `V ↠ ℤ`. -/

theorem rightHom_iotaVertical (γ : Γ) :
    SemidirectProduct.rightHom (iotaVertical α hα γ) = 1 :=
  SemidirectProduct.rightHom_inl _

/-- The level of a site: the manuscript's index `n` in
`X ≅ ⨆_{n ∈ ℤ} ℤ[1/2]³/2ⁿℤ³`. -/
def levelOf (x : Cosets α hα) : ℤ :=
  Quotient.liftOn' x
    (fun g => Multiplicative.toAdd (SemidirectProduct.rightHom g))
    (by
      intro p q hpq
      rw [QuotientGroup.leftRel_apply] at hpq
      obtain ⟨y, hy⟩ := hpq
      have h : SemidirectProduct.rightHom (p⁻¹ * q) = 1 := by
        rw [← hy]
        exact rightHom_iotaVertical α hα y
      rw [map_mul, map_inv] at h
      have hpq' : SemidirectProduct.rightHom p = SemidirectProduct.rightHom q :=
        inv_mul_eq_one.mp h
      rw [hpq'])

@[simp] theorem levelOf_mk (g : Vertical α hα) :
    levelOf α hα (QuotientGroup.mk g) = Multiplicative.toAdd g.right := rfl

theorem levelOf_smul (v : Vertical α hα) (x : Cosets α hα) :
    levelOf α hα (v • x) =
      Multiplicative.toAdd v.right + levelOf α hα x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, levelOf_mk, levelOf_mk]
  rfl

theorem levelOf_surjective : Function.Surjective (levelOf α hα) := by
  intro n
  exact ⟨QuotientGroup.mk (SemidirectProduct.inr (Multiplicative.ofAdd n)), rfl⟩

/-- A block at level `n` corresponds to a site at level `n - 1`. -/
theorem levelOf_blockEquivCosets_mk (g : Vertical α hα) :
    levelOf α hα (blockEquivCosets α hα (QuotientGroup.mk g)) =
      Multiplicative.toAdd g.right - 1 := by
  rw [blockEquivCosets_mk, levelOf_mk]
  rfl

instance : Infinite (Cosets α hα) :=
  Infinite.of_surjective (levelOf α hα) (levelOf_surjective α hα)

instance : Infinite (Block α hα) :=
  Infinite.of_surjective (blockEquivCosets α hα)
    (blockEquivCosets α hα).surjective

instance [Countable Γ] : Countable (Block α hα) :=
  Function.Surjective.countable
    (Quotient.mk_surjective (α := Vertical α hα))

/-! ## Fibres of `blockOf`: the sites of a block -/

/-- The set of sites lying in a given block. -/
def blockFibre (i : Block α hα) : Set (Cosets α hα) :=
  {x | blockOf α hα x = i}

@[simp] theorem mem_blockFibre {i : Block α hα} {x : Cosets α hα} :
    x ∈ blockFibre α hα i ↔ blockOf α hα x = i := Iff.rfl

/-- The block of the root site; the manuscript's block of `c = c_o`. -/
abbrev baseBlock : Set (Cosets α hα) :=
  blockFibre α hα (blockOf α hα (rootCoset α hα))

@[simp] theorem blockOf_rootCoset :
    blockOf α hα (rootCoset α hα) = (QuotientGroup.mk 1 : Block α hα) := rfl

/-- Translating a block translates its site set. -/
def fibreSmulEquiv (v : Vertical α hα) (i : Block α hα) :
    ↥(blockFibre α hα i) ≃ ↥(blockFibre α hα (v • i)) where
  toFun x := ⟨v • (x : Cosets α hα), by
    show blockOf α hα (v • (x : Cosets α hα)) = v • i
    rw [blockOf_smul]
    exact congrArg (fun j => v • j) x.2⟩
  invFun y := ⟨v⁻¹ • (y : Cosets α hα), by
    show blockOf α hα (v⁻¹ • (y : Cosets α hα)) = i
    rw [blockOf_smul]
    have hy : blockOf α hα (y : Cosets α hα) = v • i := y.2
    rw [hy, inv_smul_smul]⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

/-! ### The base block is `Γ ⧸ α.range`

This is the manuscript's statement that `B₁` acts on the eight sites of the
base block through the finite affine group `AGL₃(𝔽₂)`: the eight sites are
`B₁/B`, which the `τ`-conjugation isomorphism `Γ ≅ B₁` identifies with
`Γ ⧸ α.range`.  In the concrete affine model `Γ ⧸ α.range ≅ ℤ³/2ℤ³ = 𝔽₂³`
(`AffineSL3Doubling.cosetEquiv`) and the left-translation action below is
the affine action. -/

/-- The chart `Γ ⧸ α.range → X` onto the sites of the base block. -/
def baseBlockMap (c : Γ ⧸ α.range) : Cosets α hα :=
  Quotient.liftOn' c
    (fun x => (QuotientGroup.mk
      ((tVertical α hα)⁻¹ * iotaVertical α hα x * tVertical α hα) : Cosets α hα))
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy
      rw [QuotientGroup.eq]
      have heq : ((tVertical α hα)⁻¹ * iotaVertical α hα x * tVertical α hα)⁻¹ *
          ((tVertical α hα)⁻¹ * iotaVertical α hα y * tVertical α hα) =
          (tVertical α hα)⁻¹ * iotaVertical α hα (x⁻¹ * y) * tVertical α hα := by
        rw [map_mul, map_inv]
        group
      rw [heq]
      exact (tconj_mem_base_iff α hα _).mpr hxy)

@[simp] theorem baseBlockMap_mk (x : Γ) :
    baseBlockMap α hα (QuotientGroup.mk x) =
      QuotientGroup.mk
        ((tVertical α hα)⁻¹ * iotaVertical α hα x * tVertical α hα) := rfl

theorem baseBlockMap_mem (c : Γ ⧸ α.range) :
    baseBlockMap α hα c ∈ baseBlock α hα := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  show blockOf α hα _ = blockOf α hα (rootCoset α hα)
  rw [baseBlockMap_mk, blockOf_mk, blockOf_rootCoset, QuotientGroup.eq, mul_one,
    Subgroup.inv_mem_iff]
  exact (mem_blockSubgroup_iff α hα _).mpr ⟨x, rfl⟩

theorem baseBlockMap_injective : Function.Injective (baseBlockMap α hα) := by
  refine Quotient.ind₂' fun x y hxy => ?_
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  rw [baseBlockMap_mk, baseBlockMap_mk, QuotientGroup.eq] at hxy
  have heq : ((tVertical α hα)⁻¹ * iotaVertical α hα x * tVertical α hα)⁻¹ *
      ((tVertical α hα)⁻¹ * iotaVertical α hα y * tVertical α hα) =
      (tVertical α hα)⁻¹ * iotaVertical α hα (x⁻¹ * y) * tVertical α hα := by
    rw [map_mul, map_inv]
    group
  rw [heq] at hxy
  exact (tconj_mem_base_iff α hα _).mp hxy

theorem baseBlockMap_surjOn {s : Cosets α hα} (hs : s ∈ baseBlock α hα) :
    ∃ c : Γ ⧸ α.range, baseBlockMap α hα c = s := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective s
  have hp : p ∈ blockSubgroup α hα := by
    have h : blockOf α hα (QuotientGroup.mk p) =
        blockOf α hα (rootCoset α hα) := hs
    rw [blockOf_mk, blockOf_rootCoset, QuotientGroup.eq, mul_one,
      Subgroup.inv_mem_iff] at h
    exact h
  obtain ⟨x, hx⟩ := (mem_blockSubgroup_iff α hα p).mp hp
  exact ⟨QuotientGroup.mk x, by rw [baseBlockMap_mk, hx]⟩

/-- **The eight sites of the base block are `Γ ⧸ α.range`.** -/
noncomputable def baseBlockEquiv : (Γ ⧸ α.range) ≃ ↥(baseBlock α hα) :=
  Equiv.ofBijective (fun c => ⟨baseBlockMap α hα c, baseBlockMap_mem α hα c⟩)
    ⟨fun _ _ h => baseBlockMap_injective α hα (congrArg Subtype.val h),
      fun s => by
        obtain ⟨c, hc⟩ := baseBlockMap_surjOn α hα s.2
        exact ⟨c, Subtype.ext hc⟩⟩

/-- The chart is equivariant: `B₁ ≅ Γ` acts on the base block by left
translation on `Γ ⧸ α.range`. -/
theorem smul_baseBlockMap (y : Γ) (c : Γ ⧸ α.range) :
    ((tVertical α hα)⁻¹ * iotaVertical α hα y * tVertical α hα) •
        baseBlockMap α hα c =
      baseBlockMap α hα (y • c) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [baseBlockMap_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
    MulAction.Quotient.smul_mk, smul_eq_mul, baseBlockMap_mk]
  congr 1
  rw [map_mul]
  group

/-! ### Every block has exactly `[Γ : α(Γ)]` sites -/

theorem exists_smul_baseBlock (i : Block α hα) :
    ∃ g : Vertical α hα, i = g • blockOf α hα (rootCoset α hα) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective i
  refine ⟨g, ?_⟩
  show (QuotientGroup.mk g : Block α hα) = g • (QuotientGroup.mk 1 : Block α hα)
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- **Each block carries exactly `[Γ : α(Γ)]` sites.** -/
theorem blockFibre_card (i : Block α hα) :
    Nat.card ↥(blockFibre α hα i) = α.range.index := by
  obtain ⟨g, hg⟩ := exists_smul_baseBlock α hα i
  rw [hg,
    Nat.card_congr
      (fibreSmulEquiv α hα g (blockOf α hα (rootCoset α hα))).symm,
    Nat.card_congr (baseBlockEquiv α hα).symm, ← Subgroup.index_eq_card]

/-- Proposition 4.2: each block is a set of **eight** sites. -/
theorem blockCard_eq_eight (hindex : α.range.index = 8) (i : Block α hα) :
    Nat.card ↥(blockFibre α hα i) = 8 := by
  rw [blockFibre_card, hindex]

theorem finite_blockFibre (hindex : α.range.index ≠ 0) (i : Block α hα) :
    Finite ↥(blockFibre α hα i) :=
  Nat.finite_of_card_ne_zero (by rw [blockFibre_card]; exact hindex)

/-- A chosen enumeration of the eight sites of a block. -/
noncomputable def blockFibreEquivFin (hindex : α.range.index = 8)
    (i : Block α hα) : ↥(blockFibre α hα i) ≃ Fin 8 := by
  have hcard : Nat.card ↥(blockFibre α hα i) = 8 :=
    blockCard_eq_eight α hα hindex i
  haveI : Finite ↥(blockFibre α hα i) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  letI : Fintype ↥(blockFibre α hα i) := Fintype.ofFinite _
  exact Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hcard)

/-- The relative index of the base copy in level one is the index of the
range of `α`; this is the index-eight statement of the manuscript in its
subgroup form. -/
theorem base_relIndex_block :
    (baseSubgroup α hα).relIndex (blockSubgroup α hα) = α.range.index := by
  have h := level_succ_relIndex_eq α hα 0
  show (baseSubgroup α hα).relIndex (verticalLevel α hα 1) = α.range.index
  rw [baseSubgroup_eq_map, verticalLevel_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ inl_injective]
  exact h

/-! ### Block stabilisers are telescope levels -/

theorem smul_blockOf_rootCoset_iff (k : Vertical α hα) :
    k • blockOf α hα (rootCoset α hα) = blockOf α hα (rootCoset α hα) ↔
      k ∈ blockSubgroup α hα := by
  rw [blockOf_rootCoset, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
    QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff]

/-- **The stabiliser of the base block is the telescope level `B₁`.** -/
theorem blockStabilizer_eq_level :
    MulAction.stabilizer (Vertical α hα) (blockOf α hα (rootCoset α hα)) =
      verticalLevel α hα 1 := by
  ext k
  rw [MulAction.mem_stabilizer_iff]
  exact smul_blockOf_rootCoset_iff α hα k

/-- The stabiliser of an arbitrary block is the corresponding conjugate. -/
theorem mem_stabilizer_blockOf_mk_iff (g k : Vertical α hα) :
    k ∈ MulAction.stabilizer (Vertical α hα)
        (blockOf α hα (QuotientGroup.mk g)) ↔
      g⁻¹ * k * g ∈ blockSubgroup α hα := by
  rw [MulAction.mem_stabilizer_iff, blockOf_mk, MulAction.Quotient.smul_mk,
    smul_eq_mul, QuotientGroup.eq]
  have heq : (k * g)⁻¹ * g = (g⁻¹ * k * g)⁻¹ := by group
  rw [heq, Subgroup.inv_mem_iff]

/-! ### The action of `B₁` on the eight sites of the base block -/

theorem smul_mem_baseBlock {k : Vertical α hα} (hk : k ∈ blockSubgroup α hα)
    {x : Cosets α hα} (hx : x ∈ baseBlock α hα) : k • x ∈ baseBlock α hα := by
  show blockOf α hα (k • x) = blockOf α hα (rootCoset α hα)
  rw [blockOf_smul]
  have hx' : blockOf α hα x = blockOf α hα (rootCoset α hα) := hx
  rw [hx']
  exact (smul_blockOf_rootCoset_iff α hα k).mpr hk

/-- One element of `B₁` as a permutation of the eight sites of its block. -/
def blockSitePerm (k : blockSubgroup α hα) : Equiv.Perm ↥(baseBlock α hα) where
  toFun x := ⟨(k : Vertical α hα) • (x : Cosets α hα),
    smul_mem_baseBlock α hα k.2 x.2⟩
  invFun x := ⟨((k : Vertical α hα))⁻¹ • (x : Cosets α hα),
    smul_mem_baseBlock α hα (Subgroup.inv_mem _ k.2) x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

/-- **The block site action.**  The telescope level `B₁` — the stabiliser of
the base block — permutes the eight sites of that block.  Through
`baseBlockEquiv` and `smul_baseBlockMap` this is the left-translation action
of `Γ` on `Γ ⧸ α.range`; in the concrete affine model that eight-element set
is `ℤ³/2ℤ³` and the action is the affine group `AGL₃(𝔽₂)`. -/
def blockSiteAction : blockSubgroup α hα →* Equiv.Perm ↥(baseBlock α hα) where
  toFun := blockSitePerm α hα
  map_one' := Equiv.ext fun x => Subtype.ext (by
    show ((1 : blockSubgroup α hα) : Vertical α hα) • (x : Cosets α hα) =
      (x : Cosets α hα)
    rw [Subgroup.coe_one, one_smul])
  map_mul' k l := Equiv.ext fun x => Subtype.ext (by
    show ((k * l : blockSubgroup α hα) : Vertical α hα) • (x : Cosets α hα) =
      (k : Vertical α hα) • ((l : Vertical α hα) • (x : Cosets α hα))
    rw [Subgroup.coe_mul, mul_smul])

@[simp] theorem blockSiteAction_apply_coe (k : blockSubgroup α hα)
    (x : ↥(baseBlock α hα)) :
    ((blockSiteAction α hα k x : ↥(baseBlock α hα)) : Cosets α hα) =
      (k : Vertical α hα) • (x : Cosets α hα) := rfl

theorem finite_baseBlock (hindex : α.range.index ≠ 0) :
    Finite ↥(baseBlock α hα) :=
  finite_blockFibre α hα hindex _

/-! ### Finite level orbits on blocks

The site version is `MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit`;
the `V`-isomorphism `I ≅ X` transports it. -/

theorem finite_verticalLevel_block_orbit [α.range.FiniteIndex] (n : ℕ)
    (i : Block α hα) :
    (Set.range fun h : verticalLevel α hα n ↦ (h : Vertical α hα) • i).Finite := by
  have himg :
      (blockEquivCosets α hα) ''
          (Set.range fun h : verticalLevel α hα n ↦ (h : Vertical α hα) • i) =
        Set.range fun h : verticalLevel α hα n ↦
          (h : Vertical α hα) • blockEquivCosets α hα i := by
    ext s
    constructor
    · rintro ⟨t, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, (blockEquivCosets_smul α hα _ i).symm⟩
    · rintro ⟨h, rfl⟩
      exact ⟨(h : Vertical α hα) • i, ⟨h, rfl⟩,
        blockEquivCosets_smul α hα _ i⟩
  have hfin := finite_verticalLevel_orbit α hα n (blockEquivCosets α hα i)
  rw [← himg] at hfin
  exact Set.Finite.of_finite_image hfin
    ((blockEquivCosets α hα).injective.injOn)

/-! ## The orbital graph

`𝒢` is the graph on the site set whose edge set is the `V`-orbit of the
marked pair `{a, b} = {τo, v₁τo}`. -/

/-- The site `a = τ o`. -/
def markedSiteA : Cosets α hα := tVertical α hα • rootCoset α hα

/-- The site `b = v₁ τ o`. -/
def markedSiteB (a₀ : Γ) : Cosets α hα :=
  (iotaVertical α hα a₀ * tVertical α hα) • rootCoset α hα

theorem markedSiteA_eq_mk :
    markedSiteA α hα = QuotientGroup.mk (tVertical α hα) :=
  smul_rootCoset α hα _

theorem markedSiteB_eq_mk (a₀ : Γ) :
    markedSiteB α hα a₀ =
      QuotientGroup.mk (iotaVertical α hα a₀ * tVertical α hα) :=
  smul_rootCoset α hα _

include hα in
/-- `a ≠ b`: the last assertion of the manuscript's `lem:linear`. -/
theorem markedSite_ne {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    markedSiteA α hα ≠ markedSiteB α hα a₀ :=
  moved_cosets_ne α hα ha₀

/-- The marked pair lies in one block. -/
theorem blockOf_markedSite (a₀ : Γ) :
    blockOf α hα (markedSiteA α hα) = blockOf α hα (markedSiteB α hα a₀) := by
  rw [markedSiteA_eq_mk, markedSiteB_eq_mk, blockOf_mk, blockOf_mk,
    QuotientGroup.eq]
  refine (mem_blockSubgroup_iff α hα _).mpr ⟨a₀, ?_⟩
  group

/-- Adjacency in the orbital graph `𝒢`: the `V`-orbit of the marked pair. -/
def Adj (a₀ : Γ) (ξ η : Cosets α hα) : Prop :=
  ∃ g : Vertical α hα,
    (g • markedSiteA α hα = ξ ∧ g • markedSiteB α hα a₀ = η) ∨
    (g • markedSiteA α hα = η ∧ g • markedSiteB α hα a₀ = ξ)

theorem adj_symm {a₀ : Γ} {ξ η : Cosets α hα} (h : Adj α hα a₀ ξ η) :
    Adj α hα a₀ η ξ := by
  obtain ⟨g, h | h⟩ := h
  · exact ⟨g, Or.inr h⟩
  · exact ⟨g, Or.inl h⟩

include hα in
theorem adj_irrefl {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) (ξ : Cosets α hα) :
    ¬ Adj α hα a₀ ξ ξ := by
  rintro ⟨g, h | h⟩
  · exact markedSite_ne α hα ha₀ (MulAction.injective g (h.1.trans h.2.symm))
  · exact markedSite_ne α hα ha₀ (MulAction.injective g (h.1.trans h.2.symm))

/-- **Edges never leave a block.**  This half is unconditional. -/
theorem adj_blockOf_eq {a₀ : Γ} {ξ η : Cosets α hα} (h : Adj α hα a₀ ξ η) :
    blockOf α hα ξ = blockOf α hα η := by
  obtain ⟨g, h | h⟩ := h
  · rw [← h.1, ← h.2, blockOf_smul, blockOf_smul, blockOf_markedSite]
  · rw [← h.2, ← h.1, blockOf_smul, blockOf_smul, blockOf_markedSite]

/-- Adjacent sites lie at the same level. -/
theorem adj_levelOf_eq {a₀ : Γ} {ξ η : Cosets α hα} (h : Adj α hα a₀ ξ η) :
    levelOf α hα ξ = levelOf α hα η := by
  obtain ⟨g, h | h⟩ := h
  · rw [← h.1, ← h.2, levelOf_smul, levelOf_smul, markedSiteA_eq_mk,
      markedSiteB_eq_mk, levelOf_mk, levelOf_mk]
    rfl
  · rw [← h.2, ← h.1, levelOf_smul, levelOf_smul, markedSiteA_eq_mk,
      markedSiteB_eq_mk, levelOf_mk, levelOf_mk]
    rfl

/-- **The transitivity input.**  In the manuscript this is the `[audit-fix]`
finite computation that the mod-`2` reductions of the three displayed
matrices move `ē₁` onto every nonzero class of `(ℤ/2)³`; abstractly it says
that `α(Γ)` acts transitively on the nontrivial cosets of `α(Γ)` in `Γ`,
with `a₀` a marked nontrivial coset representative. -/
def AlphaCosetTransitive (a₀ : Γ) : Prop :=
  ∀ γ : Γ, γ ∉ Set.range α → ∃ ν : Γ, γ⁻¹ * (α ν * a₀) ∈ Set.range α

include hα in
/-- **Blocks are complete graphs.**  Any two distinct sites of one block are
adjacent. -/
theorem adj_of_blockOf_eq {a₀ : Γ} (htr : AlphaCosetTransitive α a₀)
    {ξ η : Cosets α hα} (hne : ξ ≠ η)
    (hblock : blockOf α hα ξ = blockOf α hα η) : Adj α hα a₀ ξ η := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective ξ
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective η
  rw [blockOf_mk, blockOf_mk, QuotientGroup.eq] at hblock
  obtain ⟨γ, hγ⟩ := (mem_blockSubgroup_iff α hα _).mp hblock
  have hγrange : γ ∉ Set.range α := by
    intro hmem
    apply hne
    rw [QuotientGroup.eq, ← hγ]
    exact (tconj_mem_base_iff α hα γ).mpr hmem
  obtain ⟨ν, μ, hμ⟩ := htr γ hγrange
  have hkey : α μ⁻¹ = a₀⁻¹ * (α ν)⁻¹ * γ := by
    rw [map_inv, hμ]
    group
  refine ⟨p * iotaVertical α hα ν * (tVertical α hα)⁻¹, Or.inl ⟨?_, ?_⟩⟩
  · rw [markedSiteA_eq_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      QuotientGroup.eq]
    refine ⟨ν⁻¹, ?_⟩
    rw [map_inv]
    group
  · rw [markedSiteB_eq_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      QuotientGroup.eq]
    refine ⟨μ⁻¹, ?_⟩
    have hq : q = p * ((tVertical α hα)⁻¹ * iotaVertical α hα γ *
        tVertical α hα) := by
      rw [hγ]
      group
    have hgamma : iotaVertical α hα (α μ⁻¹) =
        (iotaVertical α hα a₀)⁻¹ * (iotaVertical α hα (α ν))⁻¹ *
          iotaVertical α hα γ := by
      rw [hkey, map_mul, map_mul, map_inv, map_inv]
    have hfinal : iotaVertical α hα μ⁻¹ =
        (tVertical α hα)⁻¹ *
          ((iotaVertical α hα a₀)⁻¹ *
            (tVertical α hα * iotaVertical α hα ν * (tVertical α hα)⁻¹)⁻¹ *
            iotaVertical α hα γ) * tVertical α hα := by
      rw [vertical_compress α hα ν, ← hgamma, ← vertical_compress α hα μ⁻¹]
      group
    rw [hfinal, hq]
    group

include hα in
/-- **The orbital graph, completely described.**  Two sites are adjacent iff
they are distinct and lie in the same block. -/
theorem adj_iff {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α)
    (htr : AlphaCosetTransitive α a₀) (ξ η : Cosets α hα) :
    Adj α hα a₀ ξ η ↔ (ξ ≠ η ∧ blockOf α hα ξ = blockOf α hα η) := by
  constructor
  · intro h
    refine ⟨?_, adj_blockOf_eq α hα h⟩
    rintro rfl
    exact adj_irrefl α hα ha₀ ξ h
  · rintro ⟨h1, h2⟩
    exact adj_of_blockOf_eq α hα htr h1 h2

/-- The neighbours of a site. -/
def neighborSet (a₀ : Γ) (ξ : Cosets α hα) : Set (Cosets α hα) :=
  {η | Adj α hα a₀ ξ η}

include hα in
theorem neighborSet_eq_sdiff {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α)
    (htr : AlphaCosetTransitive α a₀) (ξ : Cosets α hα) :
    neighborSet α hα a₀ ξ = blockFibre α hα (blockOf α hα ξ) \ {ξ} := by
  ext η
  constructor
  · intro h
    exact ⟨(adj_blockOf_eq α hα h).symm,
      fun he => adj_irrefl α hα ha₀ ξ (he ▸ h)⟩
  · rintro ⟨h1, h2⟩
    exact adj_of_blockOf_eq α hα htr (fun he => h2 he.symm) h1.symm

include hα in
/-- **`𝒢` is `7`-regular.** -/
theorem neighborSet_ncard_eq_seven {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α)
    (htr : AlphaCosetTransitive α a₀) (hindex : α.range.index = 8)
    (ξ : Cosets α hα) : (neighborSet α hα a₀ ξ).ncard = 7 := by
  have h8 : Nat.card ↥(blockFibre α hα (blockOf α hα ξ)) = 8 :=
    blockCard_eq_eight α hα hindex _
  rw [neighborSet_eq_sdiff α hα ha₀ htr ξ,
    Set.ncard_sdiff_singleton_of_mem
      (show ξ ∈ blockFibre α hα (blockOf α hα ξ) from rfl),
    ← Nat.card_coe_set_eq, h8]

end Abstract

/-! ## The literal affine instantiation

Everything above is unconditional for any injective `α`.  We now instantiate
at the concrete affine base `Γ̄ = ℤ³ ⋊ SL₃(ℤ)` of
`GroupApproximation.AffineSL3Doubling`, with `α` the doubling and `a₀` the
first standard translation.  This is the manuscript's `E_lin`; its transfer
to the literal forty-one-relator presentation is the conditional input (I1)
of the source document and is *not* asserted here.

The one new mathematical ingredient is the manuscript's `[audit-fix]`
computation: the mod-`2` reductions of `SL₃(ℤ)` move `ē₁` onto every nonzero
class of `(ℤ/2)³`.  We realise the seven classes by seven explicit matrices.
-/

namespace Literal

open AffineSL3Doubling Matrix
open scoped MatrixGroups

/-! ### Seven matrices realising the seven nonzero parity classes -/

private def slC001 : Linear :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by rw [Matrix.det_fin_three]; simp⟩

private def slC010 : Linear :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by rw [Matrix.det_fin_three]; simp⟩

private def slC011 : Linear :=
  ⟨!![0, 0, 1; 1, 0, 0; 1, 1, 0], by rw [Matrix.det_fin_three]; simp⟩

private def slC100 : Linear :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; simp⟩

private def slC101 : Linear :=
  ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], by rw [Matrix.det_fin_three]; simp⟩

private def slC110 : Linear :=
  ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; simp⟩

private def slC111 : Linear :=
  ⟨!![1, 0, 0; 1, 1, 0; 1, 0, 1], by rw [Matrix.det_fin_three]; simp⟩

/-- The `SL₃(ℤ)`-action moves the marked translation vector to a first
column. -/
private theorem sl_smul_aVector (A : Linear) (i : Fin 3) :
    (A • aVector) i = (A : Matrix (Fin 3) (Fin 3) ℤ) i 0 := by
  show ((A : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ aVector) i = _
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three]
  simp [aVector]

/-- **Transitivity on nonzero parity classes, and the only part of the
transitivity hypothesis that is about matrices rather than about a particular
carrier.**  If a lattice vector is not even then some element of `SL₃(ℤ)` has
a first column congruent to it mod `2`.  Seven explicit matrices; the eighth
case is excluded by hypothesis.  Equivalently the reduction
`SL₃(ℤ) → GL₃(𝔽₂)` moves `ē₁` onto every nonzero class.  `alphaCosetTransitive`
below packages this for `AffineSL3Doubling.Gamma`, but the statement mentions
only `Lattice` and `Linear`, so the same lemma serves any model of the affine
group — in particular the `4 × 4` rational `gammaBar`, over which the
soficity chain actually runs and where the packaging is still missing.  It is
public for that reason. -/
theorem exists_sl_column {w : Lattice} (hw : ¬ ∃ u : Lattice, w = 2 • u) :
    ∃ (A : Linear) (v : Lattice),
      ∀ i, (A : Matrix (Fin 3) (Fin 3) ℤ) i 0 = w i + 2 * v i := by
  rcases Int.even_or_odd (w 0) with ⟨k0, h0⟩ | ⟨k0, h0⟩ <;>
    rcases Int.even_or_odd (w 1) with ⟨k1, h1⟩ | ⟨k1, h1⟩ <;>
      rcases Int.even_or_odd (w 2) with ⟨k2, h2⟩ | ⟨k2, h2⟩
  · refine absurd ⟨![k0, k1, k2], ?_⟩ hw
    rw [two_nsmul]
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · refine ⟨slC001, ![-k0, -k1, -k2], ?_⟩
    intro i
    fin_cases i
    · show (0 : ℤ) = w 0 + 2 * -k0
      omega
    · show (0 : ℤ) = w 1 + 2 * -k1
      omega
    · show (1 : ℤ) = w 2 + 2 * -k2
      omega
  · refine ⟨slC010, ![-k0, -k1, -k2], ?_⟩
    intro i
    fin_cases i
    · show (0 : ℤ) = w 0 + 2 * -k0
      omega
    · show (1 : ℤ) = w 1 + 2 * -k1
      omega
    · show (0 : ℤ) = w 2 + 2 * -k2
      omega
  · refine ⟨slC011, ![-k0, -k1, -k2], ?_⟩
    intro i
    fin_cases i
    · show (0 : ℤ) = w 0 + 2 * -k0
      omega
    · show (1 : ℤ) = w 1 + 2 * -k1
      omega
    · show (1 : ℤ) = w 2 + 2 * -k2
      omega
  · refine ⟨slC100, ![-k0, -k1, -k2], ?_⟩
    intro i
    fin_cases i
    · show (1 : ℤ) = w 0 + 2 * -k0
      omega
    · show (0 : ℤ) = w 1 + 2 * -k1
      omega
    · show (0 : ℤ) = w 2 + 2 * -k2
      omega
  · refine ⟨slC101, ![-k0, -k1, -k2], ?_⟩
    intro i
    fin_cases i
    · show (1 : ℤ) = w 0 + 2 * -k0
      omega
    · show (0 : ℤ) = w 1 + 2 * -k1
      omega
    · show (1 : ℤ) = w 2 + 2 * -k2
      omega
  · refine ⟨slC110, ![-k0, -k1, -k2], ?_⟩
    intro i
    fin_cases i
    · show (1 : ℤ) = w 0 + 2 * -k0
      omega
    · show (1 : ℤ) = w 1 + 2 * -k1
      omega
    · show (0 : ℤ) = w 2 + 2 * -k2
      omega
  · refine ⟨slC111, ![-k0, -k1, -k2], ?_⟩
    intro i
    fin_cases i
    · show (1 : ℤ) = w 0 + 2 * -k0
      omega
    · show (1 : ℤ) = w 1 + 2 * -k1
      omega
    · show (1 : ℤ) = w 2 + 2 * -k2
      omega

/-- The `SL₃(ℤ)`-action commutes with doubling. -/
private theorem smul_two_nsmul (C : Linear) (u : Lattice) :
    C • ((2 : ℕ) • u) = (2 : ℕ) • (C • u) := by
  rw [two_nsmul, two_nsmul, smul_add]

/-- **The transitivity hypothesis holds for the affine doubling.** -/
theorem alphaCosetTransitive :
    AlphaCosetTransitive alpha AffineSL3Doubling.a := by
  intro g hg
  have hw : ¬ ∃ u : Lattice, g.left.toAdd = 2 • u := by
    intro h
    exact hg ((mem_range_alpha_iff g).mpr h)
  obtain ⟨A, v, hAv⟩ := exists_sl_column hw
  refine ⟨(⟨1, A⟩ : Gamma), ?_⟩
  rw [mem_range_alpha_iff]
  refine ⟨(g.right)⁻¹ • v, ?_⟩
  have h1 : (alpha (⟨1, A⟩ : Gamma) * AffineSL3Doubling.a).left.toAdd =
      A • aVector := by
    show (2 : ℕ) • (0 : Lattice) + A • aVector = _
    rw [smul_zero, zero_add]
  have h2 : (g⁻¹ * (alpha (⟨1, A⟩ : Gamma) * AffineSL3Doubling.a)).left.toAdd =
      (g.right)⁻¹ • (-(g.left.toAdd)) +
        (g.right)⁻¹ •
          ((alpha (⟨1, A⟩ : Gamma) * AffineSL3Doubling.a).left.toAdd) := rfl
  have hAvec : -(g.left.toAdd) + A • aVector = (2 : ℕ) • v := by
    funext i
    have hi := hAv i
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, nsmul_eq_mul]
    rw [sl_smul_aVector]
    omega
  rw [h2, h1, ← smul_add, hAvec, smul_two_nsmul]

/-! ### The concrete block geometry -/

instance : (alpha.range).FiniteIndex :=
  ⟨by rw [alpha_range_index]; decide⟩

/-- Proposition 4.2 for the affine base: every block carries eight sites. -/
theorem literalBlockCard_eq_eight (i : Block alpha alpha_injective) :
    Nat.card ↥(blockFibre alpha alpha_injective i) = 8 :=
  blockCard_eq_eight alpha alpha_injective alpha_range_index i

/-- A chosen enumeration of the eight sites of a block. -/
noncomputable def literalBlockFibreEquivFin (i : Block alpha alpha_injective) :
    ↥(blockFibre alpha alpha_injective i) ≃ Fin 8 :=
  blockFibreEquivFin alpha alpha_injective alpha_range_index i

/-- Proposition 4.2 for the affine base: the orbital graph is the disjoint
union of complete graphs, one on each block. -/
theorem literalAdj_iff (ξ η : Cosets alpha alpha_injective) :
    Adj alpha alpha_injective AffineSL3Doubling.a ξ η ↔
      (ξ ≠ η ∧
        blockOf alpha alpha_injective ξ = blockOf alpha alpha_injective η) :=
  adj_iff alpha alpha_injective a_not_mem_range alphaCosetTransitive ξ η

/-- Proposition 4.2 for the affine base: the orbital graph is `7`-regular. -/
theorem literalNeighborSet_ncard_eq_seven (ξ : Cosets alpha alpha_injective) :
    (neighborSet alpha alpha_injective AffineSL3Doubling.a ξ).ncard = 7 :=
  neighborSet_ncard_eq_seven alpha alpha_injective a_not_mem_range
    alphaCosetTransitive alpha_range_index ξ

/-- The stabiliser of the base block is the telescope level `B₁`. -/
theorem literalBlockStabilizer_eq_level :
    MulAction.stabilizer (Vertical alpha alpha_injective)
        (blockOf alpha alpha_injective (rootCoset alpha alpha_injective)) =
      verticalLevel alpha alpha_injective 1 :=
  blockStabilizer_eq_level alpha alpha_injective

end Literal

end LiteralBlockGeometry
end GroupApproximation
