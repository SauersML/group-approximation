import GroupApproximation.Analysis.RepresentedRootPlaneSpectralMeasure
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

end

end IntegralColumnPlaneSpectralMeasure

end GroupApproximation
