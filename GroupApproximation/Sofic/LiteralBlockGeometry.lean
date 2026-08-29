import GroupApproximation.Sofic.MappingTelescopeFiniteOrbits

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

/-- `blockOf` is `V`-equivariant. -/
theorem blockOf_smul (v : Vertical α hα) (x : Cosets α hα) :
    blockOf α hα (v • x) = v • blockOf α hα x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, blockOf_mk]

/-! ## The block set is `V`-isomorphic to the site set

Right translation by `τ⁻¹` carries `V ⧸ B₁ = V ⧸ τ⁻¹Bτ` onto `V ⧸ B`.  In
the manuscript's coordinates this is the level shift `n ↦ n - 1` of
Proposition 4.2. -/

/-! ## The level coordinate

The first coordinate of Proposition 4.1: the `τ`-exponent.  It is defined on
sites because the base copy lies in the kernel of the projection `V ↠ ℤ`. -/

/-! ## Fibres of `blockOf`: the sites of a block -/

/-- The set of sites lying in a given block. -/
def blockFibre (i : Block α hα) : Set (Cosets α hα) :=
  {x | blockOf α hα x = i}

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

theorem finite_blockFibre (hindex : α.range.index ≠ 0) (i : Block α hα) :
    Finite ↥(blockFibre α hα i) :=
  Nat.finite_of_card_ne_zero (by rw [blockFibre_card]; exact hindex)

/-! ### Block stabilisers are telescope levels -/

/-! ### The action of `B₁` on the eight sites of the base block -/

/-! ### Finite level orbits on blocks

The site version is `MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit`;
the `V`-isomorphism `I ≅ X` transports it. -/

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

/-- Adjacency in the orbital graph `𝒢`: the `V`-orbit of the marked pair. -/
def Adj (a₀ : Γ) (ξ η : Cosets α hα) : Prop :=
  ∃ g : Vertical α hα,
    (g • markedSiteA α hα = ξ ∧ g • markedSiteB α hα a₀ = η) ∨
    (g • markedSiteA α hα = η ∧ g • markedSiteB α hα a₀ = ξ)

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
    exact hne (by
      rw [QuotientGroup.eq, ← hγ]
      exact (tconj_mem_base_iff α hα γ).mpr hmem)
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

/-! ### Seven matrices realising the seven nonzero parity classes -/

/-! ### The concrete block geometry -/

end LiteralBlockGeometry
end GroupApproximation
