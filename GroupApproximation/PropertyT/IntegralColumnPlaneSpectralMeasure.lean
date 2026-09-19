import GroupApproximation.Analysis.RepresentedRootPlaneSpectralMeasure
import GroupApproximation.Kazhdan.KazhdanFixedSpace
import GroupApproximation.Kazhdan.RealToComplexUnitaryRepresentation
import GroupApproximation.Leavitt.ElementaryRoots

/-!
# Spectral measure of the integral elementary column plane

This module specializes the represented abelian-plane construction to the
two elementary root families `x_{02}(a)` and `x_{12}(b)` in
`EL_3(R)`.  Their common terminal index makes every pair of coordinates
commute by the elementary Steinberg relations.  Thus every real orthogonal
representation, after complexification, gives a canonical commutative
C-star algebra and scalar spectral measure for this entire coefficient
plane.

For a unit real vector `z`, the terminal theorem identifies the integral of
squared character displacement at either root coordinate exactly with
`||rho(x_{i2}(a))z-z||^2`.  Complexification changes neither the vector norm
nor the displacement norm.  No finiteness, characteristic, property `(T)`,
or external existence hypothesis is used.
-/

namespace GroupApproximation

namespace IntegralColumnPlaneSpectralMeasure

open WeakDual MeasureTheory

noncomputable section

universe u v

/-! ### The two common-terminal root coordinates -/

/-- The inclusion of the two source indices into the first two indices of
`Fin 3`. -/
def columnSource (b : Fin 2) : Fin 3 :=
  ⟨b.1, by omega⟩

@[simp] theorem columnSource_zero : columnSource 0 = (0 : Fin 3) := rfl

@[simp] theorem columnSource_one : columnSource 1 = (1 : Fin 3) := rfl

/-- Neither source index is the terminal index `2`. -/
theorem columnSource_ne_terminal (b : Fin 2) :
    columnSource b ≠ (2 : Fin 3) := by
  intro h
  have hval := congrArg Fin.val h
  simp [columnSource] at hval
  omega

/-- The terminal index is distinct from either source index. -/
theorem terminal_ne_columnSource (b : Fin 2) :
    (2 : Fin 3) ≠ columnSource b :=
  (columnSource_ne_terminal b).symm

/-- The honestly indexed common-column root family.  Its index records both
which of the two root subgroups is used and its arbitrary coefficient. -/
def columnRoot {R : Type u} [Ring R] (q : Fin 2 × R) :
    elementaryGroup (Fin 3) R :=
  elementaryRoot (columnSource q.1) 2
    (columnSource_ne_terminal q.1) q.2

/-- Any two coordinates in the common-terminal root family commute.  This
includes two coefficients in the same root subgroup as well as one
coefficient from each of the two different root subgroups. -/
theorem columnRoot_commute {R : Type u} [Ring R] (p q : Fin 2 × R) :
    Commute (columnRoot p) (columnRoot q) :=
  elementaryRoot_commute_of_ne
    (columnSource p.1) 2 (columnSource q.1) 2
    (columnSource_ne_terminal p.1) (columnSource_ne_terminal q.1)
    (terminal_ne_columnSource q.1) (terminal_ne_columnSource p.1)
    p.2 q.2

/-! ### Complexified represented column plane -/

variable {R : Type u} [Ring R]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The represented abelian plane formed by the two elementary root
subgroups with terminal index `2`, in the complexification of a real
orthogonal representation. -/
def representedColumnPlane
    (rho : elementaryGroup (Fin 3) R →* (E ≃ₗᵢ[ℝ] E)) :
    RepresentedRootPlaneSpectralMeasure.RepresentedAbelianPlane
      (elementaryGroup (Fin 3) R) (Fin 2 × R) (Complexification E) where
  rho := RealToComplexUnitaryRepresentation.complexifiedUnitaryRepresentation rho
  root := columnRoot
  root_commute := columnRoot_commute

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The real vector `z` embedded as `(z,0)` remains a unit vector after
complexification. -/
theorem norm_mk_zero_eq_one {z : E} (hz : ‖z‖ = 1) :
    ‖Complexification.mk z 0‖ = 1 :=
  (Complexification.norm_mk_zero z).trans hz

variable (rho : elementaryGroup (Fin 3) R →* (E ≃ₗᵢ[ℝ] E))

noncomputable local instance : MeasurableSpace
    (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  borel _
local instance : BorelSpace
    (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  ⟨rfl⟩

/-- **Exact elementary-column spectral identity.**  The scalar spectral
measure of the complexified vector state integrates the squared character
displacement of `x_{02}(a)` or `x_{12}(a)` to the exact squared displacement
of the original real vector by that elementary matrix. -/
theorem integral_columnRoot_displacement_sq
    (z : E) (hz : ‖z‖ = 1) (q : Fin 2 × R) :
    ∫ chi, ‖chi ((representedColumnPlane rho).coordinate q) - 1‖ ^ 2
        ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
          ((representedColumnPlane rho).vectorState
            (Complexification.mk z 0) (norm_mk_zero_eq_one hz)) =
      ‖rho (columnRoot q) z - z‖ ^ 2 := by
  have hspectral :=
    RepresentedRootPlaneSpectralMeasure.integral_coordinate_displacement_sq
      (representedColumnPlane rho) (Complexification.mk z 0)
        (norm_mk_zero_eq_one hz) q
  rw [hspectral]
  exact congrArg (fun t : ℝ ↦ t ^ 2)
    (RealToComplexUnitaryRepresentation.norm_complexified_displacement_mk_zero
      rho (columnRoot q) z)

/-! ### The coordinate family and the Hilbert-space moving projection -/

/-- The subgroup generated by all represented column coordinates is exactly
the join of the two additive root subgroups in the terminal column. -/
theorem closure_range_columnRoot :
    Subgroup.closure (Set.range (columnRoot : Fin 2 × R →
      elementaryGroup (Fin 3) R)) =
      elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ⊔
        elementaryRootSubgroup (1 : Fin 3) 2 (by decide) := by
  classical
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g ⟨q, rfl⟩
    rcases q with ⟨b, a⟩
    fin_cases b
    · exact (show elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ≤ _
          from le_sup_left) ⟨a, by simp [columnRoot, columnSource]⟩
    · exact (show elementaryRootSubgroup (1 : Fin 3) 2 (by decide) ≤ _
          from le_sup_right) ⟨a, by simp [columnRoot, columnSource]⟩
  · apply sup_le
    · rintro g ⟨a, rfl⟩
      apply Subgroup.subset_closure
      exact ⟨((0 : Fin 2), a), by simp [columnRoot, columnSource]⟩
    · rintro g ⟨a, rfl⟩
      apply Subgroup.subset_closure
      exact ⟨((1 : Fin 2), a), by simp [columnRoot, columnSource]⟩

omit [CompleteSpace E] in
/-- A vector is fixed by the full two-root column subgroup precisely when it
is fixed by every coordinate used to construct the scalar spectral measure. -/
theorem mem_fixedSubspace_columnPlane_iff (z : E) :
    z ∈ KazhdanFixedSpace.fixedSubspace rho
        (elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ⊔
          elementaryRootSubgroup (1 : Fin 3) 2 (by decide)) ↔
      ∀ q : Fin 2 × R, rho (columnRoot q) z = z := by
  rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
  constructor
  · intro hz q
    apply hz
    rw [← closure_range_columnRoot (R := R)]
    exact Subgroup.subset_closure ⟨q, rfl⟩
  · intro hz g hg
    apply KazhdanFixedSpace.fixed_of_mem_closure rho
      (Set.range (columnRoot : Fin 2 × R → elementaryGroup (Fin 3) R)) z
    · rintro _ ⟨q, rfl⟩
      exact hz q
    · rw [closure_range_columnRoot (R := R)]
      exact hg

/-- The moving projection vanishes exactly when every column coordinate fixes
the vector.  This identifies the Hilbert-space subgroup occurring in the EJZ
plane estimate with the coordinate family underlying the spectral measure. -/
theorem subgroupMovingProjection_eq_zero_iff_columnRoot_fixed (z : E) :
    KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ⊔
          elementaryRootSubgroup (1 : Fin 3) 2 (by decide)) z = 0 ↔
      ∀ q : Fin 2 × R, rho (columnRoot q) z = z := by
  rw [← mem_fixedSubspace_columnPlane_iff rho z]
  constructor
  · intro hzero
    rw [KazhdanFixedSpace.subgroupMovingProjection_eq_sub_fixedProjection] at hzero
    have hzproj : z =
        (KazhdanFixedSpace.fixedProjection rho
          (elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ⊔
            elementaryRootSubgroup (1 : Fin 3) 2 (by decide)) z : E) :=
      sub_eq_zero.mp hzero
    rw [hzproj]
    exact (KazhdanFixedSpace.fixedProjection rho
      (elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ⊔
        elementaryRootSubgroup (1 : Fin 3) 2 (by decide)) z).property
  · exact KazhdanFixedSpace.subgroupMovingProjection_eq_zero_of_mem rho _

/-- Vanishing of the moving projection is already detected by the complete
family of scalar spectral displacement moments.  The stronger quantitative
identity with the measure of the nontrivial-character set additionally needs
an indicator/spectral-projection argument. -/
theorem subgroupMovingProjection_eq_zero_iff_all_spectralMoments_zero
    (z : E) (hz : ‖z‖ = 1) :
    KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ⊔
          elementaryRootSubgroup (1 : Fin 3) 2 (by decide)) z = 0 ↔
      ∀ q : Fin 2 × R,
        ∫ chi, ‖chi ((representedColumnPlane rho).coordinate q) - 1‖ ^ 2
            ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
              ((representedColumnPlane rho).vectorState
                (Complexification.mk z 0) (norm_mk_zero_eq_one hz)) = 0 := by
  rw [subgroupMovingProjection_eq_zero_iff_columnRoot_fixed rho z]
  constructor
  · intro hfixed q
    rw [integral_columnRoot_displacement_sq rho z hz q, hfixed q, sub_self,
      norm_zero, pow_two, zero_mul]
  · intro hmoments q
    have hsq : ‖rho (columnRoot q) z - z‖ ^ 2 = 0 := by
      rw [← integral_columnRoot_displacement_sq rho z hz q]
      exact hmoments q
    have hnorm : ‖rho (columnRoot q) z - z‖ = 0 := by
      nlinarith [norm_nonneg (rho (columnRoot q) z - z)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Norm-level form of
`subgroupMovingProjection_eq_zero_iff_all_spectralMoments_zero`. -/
theorem norm_subgroupMovingProjection_eq_zero_iff_all_spectralMoments_zero
    (z : E) (hz : ‖z‖ = 1) :
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ⊔
          elementaryRootSubgroup (1 : Fin 3) 2 (by decide)) z‖ = 0 ↔
      ∀ q : Fin 2 × R,
        ∫ chi, ‖chi ((representedColumnPlane rho).coordinate q) - 1‖ ^ 2
            ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
              ((representedColumnPlane rho).vectorState
                (Complexification.mk z 0) (norm_mk_zero_eq_one hz)) = 0 := by
  rw [norm_eq_zero]
  exact subgroupMovingProjection_eq_zero_iff_all_spectralMoments_zero rho z hz

end

end IntegralColumnPlaneSpectralMeasure

end GroupApproximation
