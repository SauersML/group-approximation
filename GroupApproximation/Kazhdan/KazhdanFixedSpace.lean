import GroupApproximation.Kazhdan.Kazhdan
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed subspaces of subgroup representations

The EJZ spectral argument is expressed in terms of the closed Hilbert
subspaces fixed by its root and vertex subgroups.  This file constructs those
subspaces from an actual orthogonal representation and proves their basic
lattice and closure properties.
-/

namespace GroupApproximation

universe u v

namespace KazhdanFixedSpace

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restriction of an orthogonal representation to a subgroup. -/
def restrictRepresentation (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (L : Subgroup G) :
    L →* (E ≃ₗᵢ[ℝ] E) := ρ.comp L.subtype

/-- Restrict an orthogonal representation to a linear subspace preserved by
the action.  The inverse is induced by `g⁻¹`, so this constructs genuine
linear isometric equivalences on the subtype rather than merely endomorphisms. -/
noncomputable def restrictToInvariantSubspace
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (U : Submodule ℝ E)
    (hU : ∀ g : G, ∀ x ∈ U, ρ g x ∈ U) :
    G →* (U ≃ₗᵢ[ℝ] U) where
  toFun g :=
    LinearIsometryEquiv.ofSurjective
      { toLinearMap :=
          { toFun := fun x ↦ ⟨ρ g x.1, hU g x.1 x.2⟩
            map_add' := fun x y ↦ by ext; simp
            map_smul' := fun r x ↦ by ext; simp }
        norm_map' := fun x ↦ (ρ g).norm_map x.1 }
      (by
        intro y
        refine ⟨⟨ρ g⁻¹ y.1, hU g⁻¹ y.1 y.2⟩, ?_⟩
        ext
        simp)
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro g h
    ext x
    simp [map_mul]

/-- The subspace fixed pointwise by a subgroup. -/
def fixedSubspace (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) :
    Submodule ℝ E :=
  ⨅ h : H,
    ((ρ h.1).toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap.fixedSubmodule)

@[simp] theorem mem_fixedSubspace_iff (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (H : Subgroup G) (x : E) :
    x ∈ fixedSubspace ρ H ↔ ∀ h ∈ H, ρ h x = x := by
  simp [fixedSubspace, LinearMap.mem_fixedSubmodule_iff]

/-- Fixed subspaces are closed, including for infinitely generated
subgroups. -/
theorem isClosed_fixedSubspace (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (H : Subgroup G) : IsClosed (fixedSubspace ρ H : Set E) := by
  rw [show (fixedSubspace ρ H : Set E) =
      ⋂ h : H, {x : E | ρ h.1 x = x} by
    ext x
    simp [mem_fixedSubspace_iff]]
  exact isClosed_iInter fun h ↦ isClosed_eq (ρ h.1).continuous continuous_id

/-- Inclusion of subgroups reverses inclusion of fixed subspaces. -/
theorem antitone (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {H K : Subgroup G}
    (hHK : H ≤ K) : fixedSubspace ρ K ≤ fixedSubspace ρ H := by
  intro x hx
  rw [mem_fixedSubspace_iff] at hx ⊢
  intro h hh
  exact hx h (hHK hh)

/-- An element normalizing `H` preserves its fixed subspace. -/
theorem map_mem_fixedSubspace_of_mem_normalizer
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {x : E}
    (hx : x ∈ fixedSubspace ρ H) : ρ g x ∈ fixedSubspace ρ H := by
  rw [mem_fixedSubspace_iff] at hx ⊢
  intro h hh
  have hconj : g⁻¹ * h * g ∈ H :=
    (Subgroup.mem_normalizer_iff''.mp hg h).mp hh
  calc
    ρ h (ρ g x) = ρ (h * g) x := by simp [map_mul]
    _ = ρ (g * (g⁻¹ * h * g)) x := by congr 2; group
    _ = ρ g (ρ (g⁻¹ * h * g) x) := by simp [map_mul]
    _ = ρ g x := by rw [hx _ hconj]

/-- A normalizing element also preserves the orthogonal complement of the
fixed subspace. -/
theorem map_mem_fixedSubspace_orthogonal_of_mem_normalizer
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {x : E}
    (hx : x ∈ (fixedSubspace ρ H)ᗮ) :
    ρ g x ∈ (fixedSubspace ρ H)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normalizer (H : Set G)).inv_mem hg
  have hy' : ρ g⁻¹ y ∈ fixedSubspace ρ H :=
    map_mem_fixedSubspace_of_mem_normalizer ρ H hginv hy
  calc
    inner ℝ y (ρ g x) = inner ℝ (ρ g⁻¹ y) (ρ g⁻¹ (ρ g x)) := by
      rw [(ρ g⁻¹).inner_map_map]
    _ = inner ℝ (ρ g⁻¹ y) x := by simp
    _ = 0 := Submodule.inner_right_of_mem_orthogonal hy' hx

/-- The moving subspace relative to a subgroup is the orthogonal complement
of that subgroup's fixed vectors. -/
noncomputable def subgroupMovingSubspace
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) : Submodule ℝ E :=
  (fixedSubspace ρ H)ᗮ

/-- The restricted action of `H` on the orthogonal complement of its fixed
space. -/
noncomputable def subgroupMovingRepresentation
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) :
    H →* (subgroupMovingSubspace ρ H ≃ₗᵢ[ℝ] subgroupMovingSubspace ρ H) :=
  restrictToInvariantSubspace (restrictRepresentation ρ H)
    (subgroupMovingSubspace ρ H) fun g _ hx ↦
      map_mem_fixedSubspace_orthogonal_of_mem_normalizer ρ H
        (H.le_normalizer g.2) hx

@[simp] theorem subgroupMovingRepresentation_apply
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (g : H)
    (x : subgroupMovingSubspace ρ H) :
    ((subgroupMovingRepresentation ρ H g x : subgroupMovingSubspace ρ H) : E) =
      ρ g.1 x.1 := rfl

/-- The moving representation of a subgroup has no nonzero invariant
vectors, with no hypothesis on the original representation. -/
theorem subgroupMovingRepresentation_hasNoInvariantVectors
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) :
    IsKazhdanPair.HasNoInvariantVectors H
      (subgroupMovingRepresentation ρ H) := by
  intro x hx
  have hxfix : (x : E) ∈ fixedSubspace ρ H := by
    rw [mem_fixedSubspace_iff]
    intro g hg
    have h := congrArg Subtype.val (hx ⟨g, hg⟩)
    simpa using h
  have hxorth : (x : E) ∈ (fixedSubspace ρ H)ᗮ := x.2
  have hinner : inner ℝ (x : E) x = 0 :=
    Submodule.inner_right_of_mem_orthogonal hxfix hxorth
  exact Subtype.ext (inner_self_eq_zero.mp hinner)

/-- A vector fixed by a set is fixed by the subgroup it generates. -/
theorem fixed_of_mem_closure (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (S : Set G) (x : E) (hx : ∀ g ∈ S, ρ g x = x) :
    ∀ g ∈ Subgroup.closure S, ρ g x = x := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hx g hg
  | one => simp
  | mul a b _ _ ha hb => simp [map_mul, ha, hb]
  | inv a _ ha =>
      have h := congrArg (fun z ↦ (ρ a)⁻¹ z) ha
      simpa [map_inv] using h.symm

/-- Fixed vectors of a join are exactly the vectors fixed by both subgroups. -/
theorem fixedSubspace_sup (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H K : Subgroup G) :
    fixedSubspace ρ (H ⊔ K) = fixedSubspace ρ H ⊓ fixedSubspace ρ K := by
  refine le_antisymm (le_inf (antitone ρ le_sup_left) (antitone ρ le_sup_right)) ?_
  intro x hx
  change x ∈ fixedSubspace ρ H ∧ x ∈ fixedSubspace ρ K at hx
  rw [mem_fixedSubspace_iff, mem_fixedSubspace_iff] at hx
  rw [mem_fixedSubspace_iff]
  intro g hg
  have hseed : ∀ s ∈ (H : Set G) ∪ (K : Set G), ρ s x = x := by
    intro s hs
    rcases hs with hs | hs
    · exact hx.1 s hs
    · exact hx.2 s hs
  apply fixed_of_mem_closure ρ ((H : Set G) ∪ (K : Set G)) x hseed g
  rwa [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]

/-- The fixed subspace carries the complete-space instance required by
orthogonal projection. -/
noncomputable def fixedProjection [CompleteSpace E] (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (H : Subgroup G) : E →L[ℝ] fixedSubspace ρ H := by
  letI : CompleteSpace (fixedSubspace ρ H) :=
    (isClosed_fixedSubspace ρ H).completeSpace_coe
  exact (fixedSubspace ρ H).orthogonalProjectionOnto

/-- Orthogonal projection onto the moving subspace relative to `H`. -/
noncomputable def subgroupMovingProjection [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) : E →L[ℝ] E := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  exact Uᗮ.starProjection

/-- The moving projection is the residual after orthogonal projection onto
the subgroup-fixed space. -/
theorem subgroupMovingProjection_eq_sub_fixedProjection [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    subgroupMovingProjection ρ H x =
      x - (fixedProjection ρ H x : E) := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  change Uᗮ.starProjection x = x - U.starProjection x
  exact congrArg (fun T : E →L[ℝ] E ↦ T x)
    (Submodule.starProjection_orthogonal U)

/-- Fixed and moving projections are orthogonal. -/
theorem fixedProjection_inner_movingProjection [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    inner ℝ (fixedProjection ρ H x : E)
      (subgroupMovingProjection ρ H x) = 0 := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  exact Submodule.inner_right_of_mem_orthogonal (fixedProjection ρ H x).property
    (Uᗮ.starProjection_apply_mem x)

/-- Pythagoras for the fixed/moving decomposition of a vector. -/
theorem norm_sq_fixedProjection_add_movingProjection [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    ‖x‖ ^ 2 = ‖(fixedProjection ρ H x : E)‖ ^ 2 +
      ‖subgroupMovingProjection ρ H x‖ ^ 2 := by
  calc
    ‖x‖ ^ 2 = ‖(fixedProjection ρ H x : E) +
        subgroupMovingProjection ρ H x‖ ^ 2 := by
      rw [subgroupMovingProjection_eq_sub_fixedProjection]
      abel
    _ = ‖(fixedProjection ρ H x : E)‖ ^ 2 +
        ‖subgroupMovingProjection ρ H x‖ ^ 2 := by
      simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real
        (fixedProjection_inner_movingProjection ρ H x)

theorem subgroupMovingProjection_mem [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    subgroupMovingProjection ρ H x ∈ subgroupMovingSubspace ρ H := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  exact Uᗮ.starProjection_apply_mem x

/-- Orthogonal projection onto `H`-fixed vectors commutes with every element
that normalizes `H`. -/
theorem fixedProjection_equivariant_of_mem_normalizer [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (x : E) :
    (fixedProjection ρ H (ρ g x) : E) =
      ρ g (fixedProjection ρ H x : E) := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  change U.starProjection (ρ g x) = ρ g (U.starProjection x)
  apply U.eq_starProjection_of_mem_orthogonal
  · exact map_mem_fixedSubspace_of_mem_normalizer ρ H hg
      (U.starProjection_apply_mem x)
  · have hxorth : x - U.starProjection x ∈ Uᗮ :=
      U.sub_starProjection_mem_orthogonal x
    have hmap := map_mem_fixedSubspace_orthogonal_of_mem_normalizer
      ρ H hg hxorth
    simpa [map_sub] using hmap

/-- The moving projection commutes with every element that normalizes the
subgroup. -/
theorem subgroupMovingProjection_equivariant_of_mem_normalizer [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (x : E) :
    subgroupMovingProjection ρ H (ρ g x) =
      ρ g (subgroupMovingProjection ρ H x) := by
  rw [subgroupMovingProjection_eq_sub_fixedProjection,
    fixedProjection_equivariant_of_mem_normalizer ρ H hg,
    subgroupMovingProjection_eq_sub_fixedProjection, map_sub]

/-- Orthogonal projection onto the moving subspace is contractive. -/
theorem norm_subgroupMovingProjection_le [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    ‖subgroupMovingProjection ρ H x‖ ≤ ‖x‖ := by
  have hpyth := norm_sq_fixedProjection_add_movingProjection ρ H x
  have hsq : ‖subgroupMovingProjection ρ H x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hpyth]
    exact le_add_of_nonneg_left (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Under a normalizing element, displacement of the moving projection is no
larger than displacement of the original vector. -/
theorem norm_subgroupMovingProjection_displacement_le_of_mem_normalizer
    [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (x : E) :
    ‖ρ g (subgroupMovingProjection ρ H x) -
        subgroupMovingProjection ρ H x‖ ≤ ‖ρ g x - x‖ := by
  rw [← subgroupMovingProjection_equivariant_of_mem_normalizer ρ H hg, ← map_sub]
  exact norm_subgroupMovingProjection_le ρ H (ρ g x - x)

/-- If `K` normalizes `H` and `x` is `K`-fixed, projecting `x` onto the
`H`-fixed space already lands in the fixed space of `H ⊔ K`. -/
theorem fixedProjection_eq_sup_of_fixed_of_normalizes [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H K : Subgroup G)
    (hKnorm : K ≤ Subgroup.normalizer (H : Set G)) {x : E}
    (hxK : x ∈ fixedSubspace ρ K) :
    (fixedProjection ρ H x : E) = fixedProjection ρ (H ⊔ K) x := by
  let U := fixedSubspace ρ H
  let V := fixedSubspace ρ (H ⊔ K)
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  letI : CompleteSpace V :=
    (isClosed_fixedSubspace ρ (H ⊔ K)).completeSpace_coe
  let p : E := U.starProjection x
  have hpH : p ∈ fixedSubspace ρ H := U.starProjection_apply_mem x
  have hpK : p ∈ fixedSubspace ρ K := by
    rw [mem_fixedSubspace_iff]
    intro k hk
    calc
      ρ k p = U.starProjection (ρ k x) :=
        (fixedProjection_equivariant_of_mem_normalizer ρ H (hKnorm hk) x).symm
      _ = p := by rw [(mem_fixedSubspace_iff ρ K x).mp hxK k hk]
  have hpV : p ∈ V := by
    change p ∈ fixedSubspace ρ (H ⊔ K)
    rw [fixedSubspace_sup]
    exact ⟨hpH, hpK⟩
  have hresU : x - p ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hVU : V ≤ U := antitone ρ le_sup_left
  have hresV : x - p ∈ Vᗮ := Submodule.orthogonal_le hVU hresU
  exact (V.eq_starProjection_of_mem_orthogonal hpV hresV).symm

end KazhdanFixedSpace
end GroupApproximation
