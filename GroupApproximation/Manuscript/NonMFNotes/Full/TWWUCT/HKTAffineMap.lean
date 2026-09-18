import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTAlgebraDef
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Transporting finite-dimensional affine subspaces along affine isometries

Lane TWWUCT-C (WO-TWWUCT-C).  An affine isometry `h ↦ U h + w` of `H` carries `E = a + V` to
`E' = (U a + w) + U V`.  Foot, perpendicular part and radial variable are equivariant, and the
stage coefficients `k ∈ C₀(V, Cliff(V))` are carried to `orth U ∘ k ∘ U⁻¹ ∈ C₀(UV, Cliff(UV))`
(HKT 1998, §4: the action of the affine isometry group on the directed system).

* `FinDimAffine.mapAffine E U w`: the image `E'`.
* `perp_mapAffine`, `coe_foot_mapAffine`, `radiusSq_mapAffine`, `gaussian_mapAffine`.
* `FinDimAffine.transportCoeff`, `transportCoeff_foot` and `isStageCoeff_transport`.
* `CliffordSystem.orth_mem_cliffordSub`: `orth U (Cliff(V)) ⊆ Cliff(UV)`.
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe v w

open Filter Topology

namespace CliffordSystem

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-- Second quantisation maps `Cliff(V)` into `Cliff(UV)`. -/
theorem orth_mem_cliffordSub (U : H ≃ₗᵢ[ℝ] H) {V : Submodule ℝ H} {a : C}
    (ha : a ∈ cliffordSub (C := C) H V) :
    orth (C := C) U a ∈ cliffordSub (C := C) H (V.map (U.toLinearEquiv : H →ₗ[ℝ] H)) := by
  have hle : cliffordSub (C := C) H V ≤
      (cliffordSub (C := C) H (V.map (U.toLinearEquiv : H →ₗ[ℝ] H))).comap
        (orth U : C ≃⋆ₐ[ℂ] C).toStarAlgHom := by
    refine StarAlgebra.adjoin_le ?_
    rintro _ ⟨v, rfl⟩
    rw [SetLike.mem_coe, StarSubalgebra.mem_comap]
    show orth (C := C) U (clifford ((0 : ℝ), (v : H))) ∈ _
    rw [orth_clifford]
    exact clifford_mem_cliffordSub (V.map (U.toLinearEquiv : H →ₗ[ℝ] H))
      ⟨U (v : H), Submodule.mem_map_of_mem v.2⟩
  exact (StarSubalgebra.mem_comap _ _ _).1 (hle ha)

end CliffordSystem

namespace FinDimAffine

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (E : FinDimAffine H) (U : H ≃ₗᵢ[ℝ] H) (w : H)

/-- The image of `E = a + V` under the affine isometry `h ↦ U h + w`. -/
def mapAffine : FinDimAffine H where
  base := U E.base + w
  dir := E.dir.map (U.toLinearEquiv : H →ₗ[ℝ] H)
  finiteDimensional := inferInstance
  hasOrthogonalProjection := Submodule.HasOrthogonalProjection.map_linearIsometryEquiv E.dir U

theorem mapAffine_base : (E.mapAffine U w).base = U E.base + w :=
  rfl

theorem mapAffine_dir : (E.mapAffine U w).dir = E.dir.map (U.toLinearEquiv : H →ₗ[ℝ] H) :=
  rfl

theorem mapAffine_sub_base (h : H) : U h + w - (E.mapAffine U w).base = U (h - E.base) := by
  rw [mapAffine_base, add_sub_add_right_eq_sub]
  exact (map_sub U h E.base).symm

theorem starProjection_mapAffine (x : H) :
    (E.mapAffine U w).dir.starProjection x = U (E.dir.starProjection (U.symm x)) :=
  Submodule.starProjection_map_apply U E.dir x

theorem perp_mapAffine (h : H) : (E.mapAffine U w).perp (U h + w) = U (E.perp h) := by
  show U h + w - (E.mapAffine U w).base -
      (E.mapAffine U w).dir.starProjection (U h + w - (E.mapAffine U w).base) =
    U (h - E.base - E.dir.starProjection (h - E.base))
  rw [E.mapAffine_sub_base U w h, E.starProjection_mapAffine U w,
    LinearIsometryEquiv.symm_apply_apply]
  exact (map_sub U _ _).symm

theorem coe_foot (h : H) : (E.foot h : H) = E.dir.starProjection (h - E.base) :=
  rfl

theorem coe_foot_mapAffine (h : H) :
    ((E.mapAffine U w).foot (U h + w) : H) = U (E.foot h) := by
  rw [coe_foot, coe_foot, E.mapAffine_sub_base U w h, E.starProjection_mapAffine U w,
    LinearIsometryEquiv.symm_apply_apply]

theorem radiusSq_mapAffine (t : ℝ) (h : H) :
    (E.mapAffine U w).radiusSq (t, U h + w) = E.radiusSq (t, h) := by
  show t ^ 2 + ‖(E.mapAffine U w).perp (U h + w)‖ ^ 2 = t ^ 2 + ‖E.perp h‖ ^ 2
  rw [E.perp_mapAffine U w h, LinearIsometryEquiv.norm_map]

theorem gaussian_mapAffine (t : ℝ) (h : H) :
    (E.mapAffine U w).gaussian (t, U h + w) = E.gaussian (t, h) := by
  show ((Real.exp (-((E.mapAffine U w).radiusSq (t, U h + w))) : ℝ) : ℂ) =
    ((Real.exp (-(E.radiusSq (t, h))) : ℝ) : ℂ)
  rw [E.radiusSq_mapAffine U w t h]

/-- The inverse direction map `U V → V`, `v ↦ U⁻¹ v`. -/
def dirSymm (v : (E.mapAffine U w).dir) : E.dir :=
  ⟨U.symm v, by
    have hv : (v : H) ∈ E.dir.map (U.toLinearEquiv : H →ₗ[ℝ] H) := v.2
    exact (Submodule.mem_map_equiv (p := E.dir)).1 hv⟩

theorem coe_dirSymm (v : (E.mapAffine U w).dir) : (E.dirSymm U w v : H) = U.symm v :=
  rfl

theorem dirSymm_foot (h : H) : E.dirSymm U w ((E.mapAffine U w).foot (U h + w)) = E.foot h := by
  apply Subtype.ext
  rw [coe_dirSymm, E.coe_foot_mapAffine U w h, LinearIsometryEquiv.symm_apply_apply]

theorem isometry_dirSymm : Isometry (E.dirSymm U w) :=
  Isometry.of_dist_eq fun v v' => by
    show dist (U.symm (v : H)) (U.symm (v' : H)) = dist (v : H) (v' : H)
    exact U.symm.dist_map (v : H) v'

theorem tendsto_dirSymm_cocompact :
    Tendsto (E.dirSymm U w) (cocompact (E.mapAffine U w).dir) (cocompact E.dir) := by
  haveI : CompleteSpace (E.mapAffine U w).dir := FiniteDimensional.complete ℝ _
  exact (E.isometry_dirSymm U w).isClosedEmbedding.tendsto_cocompact

variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-- The transported coefficient `v ↦ orth U (k (U⁻¹ v))` on `U V`. -/
def transportCoeff (k : E.dir →ᵇ C) : (E.mapAffine U w).dir →ᵇ C :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun v => CliffordSystem.orth (H := H) (C := C) U (k (E.dirSymm U w v)))
    ((StarAlgEquiv.isometry (CliffordSystem.orth (H := H) (C := C) U)).continuous.comp
      (k.continuous.comp (E.isometry_dirSymm U w).continuous)) ‖k‖
    (fun v => by
      show ‖CliffordSystem.orth (H := H) (C := C) U (k (E.dirSymm U w v))‖ ≤ ‖k‖
      rw [StarAlgEquiv.norm_map]
      exact k.norm_coe_le_norm _)

theorem transportCoeff_apply (k : E.dir →ᵇ C) (v : (E.mapAffine U w).dir) :
    E.transportCoeff U w k v = CliffordSystem.orth (H := H) (C := C) U (k (E.dirSymm U w v)) :=
  rfl

theorem transportCoeff_foot (k : E.dir →ᵇ C) (h : H) :
    E.transportCoeff U w k ((E.mapAffine U w).foot (U h + w)) =
      CliffordSystem.orth (H := H) (C := C) U (k (E.foot h)) := by
  rw [transportCoeff_apply, E.dirSymm_foot U w h]

/-- Transport preserves the stage coefficients `C₀(V, Cliff(V))`. -/
theorem isStageCoeff_transport {k : E.dir →ᵇ C} (hk : E.IsStageCoeff k) :
    (E.mapAffine U w).IsStageCoeff (E.transportCoeff U w k) := by
  refine ⟨?_, fun v => ?_⟩
  · have h0 : Tendsto (fun a : C => CliffordSystem.orth (H := H) (C := C) U a) (𝓝 0) (𝓝 0) :=
      (StarAlgEquiv.isometry (CliffordSystem.orth (H := H) (C := C) U)).continuous.tendsto' 0 0
        (map_zero _)
    exact h0.comp (hk.1.comp (E.tendsto_dirSymm_cocompact U w))
  · exact CliffordSystem.orth_mem_cliffordSub U (hk.2 (E.dirSymm U w v))

end FinDimAffine

end

end GroupApproximation.Full.TWWUCT
