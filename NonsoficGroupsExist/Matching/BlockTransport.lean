import NonsoficGroupsExist.Matching.BlockIndex

/-!
# Transporting component partitions

A compressor acts by a genuine permutation on every finite model.  The source
expander decomposition is therefore transported occurrence-by-occurrence,
including parallel edges, and its component partition is transported by the
same permutation.  This file records the exact finite-set identities.
-/

namespace NonsoficGroupsExist
namespace BlockStructure

variable {Y : FiniteModel} (P : BlockStructure Y)

/-- Transport a block partition along an equivalence of finite vertex types. -/
noncomputable def transportEquiv {Z : FiniteModel} (q : Y ≃ Z) : BlockStructure Z where
  block y := (P.block (q.symm y)).image q
  self_mem y := by
    classical
    exact Finset.mem_image.mpr ⟨q.symm y, P.self_mem (q.symm y), q.apply_symm_apply y⟩
  eq_of_mem x y hy := by
    classical
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    have hzq : z = q.symm y := by
      rw [← hzy]
      simp
    rw [← hzq, P.eq_of_mem (q.symm x) z hz]

/-- Transport a block partition by a permutation. -/
noncomputable def transport (q : Equiv.Perm Y) : BlockStructure Y :=
  P.transportEquiv q

@[simp] theorem transportEquiv_block {Z : FiniteModel} (q : Y ≃ Z) (y : Y) :
    (P.transportEquiv q).block (q y) = (P.block y).image q := by
  simp [transportEquiv]

@[simp] theorem transport_block (q : Equiv.Perm Y) (y : Y) :
    (P.transport q).block (q y) = (P.block y).image q := by
  simp [transport]

@[simp] theorem transport_size (q : Equiv.Perm Y) (y : Y) :
    (P.transport q).size (q y) = P.size y := by
  classical
  change ((P.transport q).block (q y)).card = (P.block y).card
  rw [P.transport_block]
  exact Finset.card_image_of_injective _ q.injective

theorem transportEquiv_blocksFinset {Z : FiniteModel} (q : Y ≃ Z) :
    (P.transportEquiv q).blocksFinset =
      P.blocksFinset.image (Finset.image q) := by
  classical
  ext C
  simp only [mem_blocksFinset, Finset.mem_image]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨P.block (q.symm z), ⟨q.symm z, rfl⟩, ?_⟩
    simp [transportEquiv]
  · rintro ⟨B, ⟨y, rfl⟩, rfl⟩
    exact ⟨q y, by simp [transportEquiv]⟩

theorem transport_blocksFinset (q : Equiv.Perm Y) :
    (P.transport q).blocksFinset = P.blocksFinset.image (Finset.image q) :=
  P.transportEquiv_blocksFinset q

theorem image_block_card (q : Equiv.Perm Y) (y : Y) :
    ((P.block y).image q).card = (P.block y).card :=
  Finset.card_image_of_injective _ q.injective

end BlockStructure

namespace BlockIndex

variable {Y Z : FiniteModel}

/-- Transporting a block partition along an equivalence transports its finite
type of distinct blocks bijectively.  This is the object map used by the
finite component groupoid: it contains no choice of representatives. -/
noncomputable def transportEquiv (P : BlockStructure Y) (q : Y ≃ Z) :
    BlockIndex P ≃ BlockIndex (P.transportEquiv q) :=
  Equiv.ofBijective
    (fun C ↦
      ⟨C.block.image q, by
        rw [P.transportEquiv_blocksFinset q]
        exact Finset.mem_image.mpr ⟨C.block, C.2, rfl⟩⟩)
    ⟨by
      intro C D hCD
      apply Subtype.ext
      exact Finset.image_injective q.injective (Subtype.ext_iff.mp hCD),
     by
      intro D
      have hD : D.1 ∈ P.blocksFinset.image (Finset.image q) := by
        simpa only [P.transportEquiv_blocksFinset q] using D.2
      obtain ⟨C, hC, hCD⟩ := Finset.mem_image.mp hD
      exact ⟨⟨C, hC⟩, Subtype.ext hCD⟩⟩

@[simp] theorem transportEquiv_block (P : BlockStructure Y) (q : Y ≃ Z)
    (C : BlockIndex P) :
    (transportEquiv P q C).block = C.block.image q := rfl

@[simp] theorem transportEquiv_card (P : BlockStructure Y) (q : Y ≃ Z)
    (C : BlockIndex P) :
    (transportEquiv P q C).block.card = C.block.card := by
  rw [transportEquiv_block]
  exact Finset.card_image_of_injective _ q.injective

theorem transportEquiv_representative_mem (P : BlockStructure Y) (q : Y ≃ Z)
    (C : BlockIndex P) :
    q (representative P C) ∈ (transportEquiv P q C).block := by
  rw [transportEquiv_block]
  exact Finset.mem_image.mpr ⟨representative P C, representative_mem P C, rfl⟩

/-- A permutation which sends every block of `P` onto another block induces
a genuine permutation of the finite component type. -/
noncomputable def componentPerm (P : BlockStructure Y) (q : Equiv.Perm Y)
    (hmaps : ∀ C : BlockIndex P, C.block.image q ∈ P.blocksFinset) :
    Equiv.Perm (BlockIndex P) := by
  let f : BlockIndex P → BlockIndex P := fun C ↦ ⟨C.block.image q, hmaps C⟩
  have hf : Function.Injective f := by
    intro C D hCD
    apply Subtype.ext
    exact Finset.image_injective q.injective (Subtype.ext_iff.mp hCD)
  exact Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩

@[simp] theorem componentPerm_block (P : BlockStructure Y) (q : Equiv.Perm Y)
    (hmaps : ∀ C : BlockIndex P, C.block.image q ∈ P.blocksFinset)
    (C : BlockIndex P) :
    (componentPerm P q hmaps C).block = C.block.image q := rfl

/-- An involution which preserves the partition induces an involution of its
component type.  This is the exact finite precursor of the involutive
component arrows used for the flip lamp. -/
theorem componentPerm_sq (P : BlockStructure Y) (q : Equiv.Perm Y)
    (hmaps : ∀ C : BlockIndex P, C.block.image q ∈ P.blocksFinset)
    (hsq : q * q = 1) :
    componentPerm P q hmaps * componentPerm P q hmaps = 1 := by
  apply Equiv.ext
  intro C
  apply Subtype.ext
  change (C.block.image q).image q = C.block
  have hpoint (x : Y) : q (q x) = x := by
    have hx := DFunLike.congr_fun hsq x
    simpa [Equiv.Perm.mul_apply] using hx
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    simpa only [hpoint] using hz
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨q x, ?_, hpoint x⟩
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

end BlockIndex
end NonsoficGroupsExist
