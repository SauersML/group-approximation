import GroupApproximation.Matching.BlockIndex

/-!
# Transporting component partitions

A compressor acts by a genuine permutation on every finite model.  The source
expander decomposition is therefore transported occurrence-by-occurrence,
including parallel edges, and its component partition is transported by the
same permutation.  This file records the exact finite-set identities.
-/

namespace GroupApproximation
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

/-- The number of vertices transported from component `C` into component
`D`.  Unlike a choice of dominant target, this retains the entire finite
component correspondence. -/
noncomputable def overlap (P : BlockStructure Y) (q : Equiv.Perm Y)
    (C D : BlockIndex P) : ℕ :=
  ((C.block.image q) ∩ D.block).card

/-- Reversing a transported overlap exchanges its source and target. -/
theorem overlap_inv_comm (P : BlockStructure Y) (q : Equiv.Perm Y)
    (C D : BlockIndex P) :
    overlap P q C D = overlap P q⁻¹ D C := by
  classical
  unfold overlap
  apply Finset.card_bij (fun y _ ↦ q⁻¹ y)
  · intro y hy
    obtain ⟨hyqC, hyD⟩ := Finset.mem_inter.mp hy
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_image.mpr ⟨y, hyD, rfl⟩, ?_⟩
    obtain ⟨x, hxC, hxy⟩ := Finset.mem_image.mp hyqC
    simpa [← hxy] using hxC
  · intro x _ y _ hxy
    exact q⁻¹.injective hxy
  · intro x hx
    obtain ⟨hxqD, hxC⟩ := Finset.mem_inter.mp hx
    refine ⟨q x, ?_, by simp⟩
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x, hxC, rfl⟩, ?_⟩
    obtain ⟨y, hyD, hyx⟩ := Finset.mem_image.mp hxqD
    simpa [← hyx] using hyD

/-- An involution gives a symmetric component-overlap matrix. -/
theorem overlap_comm_of_sq (P : BlockStructure Y) (q : Equiv.Perm Y)
    (hsq : q * q = 1) (C D : BlockIndex P) :
    overlap P q C D = overlap P q D C := by
  classical
  have hpoint (x : Y) : q (q x) = x := by
    have hx := DFunLike.congr_fun hsq x
    simpa [Equiv.Perm.mul_apply] using hx
  unfold overlap
  apply Finset.card_bij (fun x _ ↦ q x)
  · intro x hx
    obtain ⟨hxC, hxD⟩ := Finset.mem_inter.mp hx
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x, hxD, rfl⟩, ?_⟩
    obtain ⟨c, hc, hcx⟩ := Finset.mem_image.mp hxC
    rw [← hcx, hpoint]
    exact hc
  · intro x _ y _ hxy
    exact q.injective hxy
  · intro y hy
    refine ⟨q y, ?_, hpoint y⟩
    obtain ⟨hyD, hyC⟩ := Finset.mem_inter.mp hy
    apply Finset.mem_inter.mpr
    refine ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨y, hyC, rfl⟩
    · obtain ⟨d, hd, hdy⟩ := Finset.mem_image.mp hyD
      rw [← hdy, hpoint]
      exact hd

/-- Every row of the component-overlap matrix has total weight equal to the
size of its source component. -/
theorem sum_overlap (P : BlockStructure Y) (q : Equiv.Perm Y)
    (C : BlockIndex P) :
    ∑ D : BlockIndex P, (overlap P q C D : ℝ) = C.block.card := by
  classical
  let U : Finset Y := C.block.image q
  have hpartition := BlockIndex.sum_card_filter P (fun x ↦ x ∈ U)
  calc
    ∑ D : BlockIndex P, (overlap P q C D : ℝ) =
        ∑ D : BlockIndex P,
          ((Finset.univ.filter fun x : D.block ↦ (x : Y) ∈ U).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro D _
            congr 1
            unfold overlap
            apply Finset.card_bij (fun x hx ↦ ⟨x, (Finset.mem_inter.mp hx).2⟩)
            · intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact (Finset.mem_inter.mp hx).1
            · intro x _ y _ hxy
              exact congrArg Subtype.val hxy
            · intro x hx
              refine ⟨x.1, Finset.mem_inter.mpr ⟨?_, x.2⟩, rfl⟩
              simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
    _ = ((Finset.univ.filter fun x : Y ↦ x ∈ U).card : ℝ) := hpartition
    _ = U.card := by simp
    _ = C.block.card := by
      exact_mod_cast Finset.card_image_of_injective C.block q.injective

/-- A transported component has at most one target component containing a
strict majority of its vertices. -/
theorem eq_of_two_mul_overlap_gt_card (P : BlockStructure Y)
    (q : Equiv.Perm Y) (C D E : BlockIndex P)
    (hD : C.block.card < 2 * overlap P q C D)
    (hE : C.block.card < 2 * overlap P q C E) : D = E := by
  classical
  by_contra hDE
  have hdisj : Disjoint D.block E.block :=
    P.blocksFinset_pairwise_disjoint D.2 E.2
      (Subtype.coe_injective.ne hDE)
  let U := C.block.image q
  have hparts : Disjoint (U ∩ D.block) (U ∩ E.block) :=
    Finset.disjoint_of_subset_right Finset.inter_subset_right
      (Finset.disjoint_of_subset_left Finset.inter_subset_right hdisj)
  have hsub : (U ∩ D.block) ∪ (U ∩ E.block) ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).1
    · exact (Finset.mem_inter.mp hx).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hparts] at hcard
  have hU : U.card = C.block.card :=
    Finset.card_image_of_injective C.block q.injective
  unfold overlap at hD hE
  dsimp only [U] at hcard hU
  omega

end BlockIndex
end GroupApproximation
