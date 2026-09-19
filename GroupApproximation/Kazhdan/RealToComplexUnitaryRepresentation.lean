import GroupApproximation.Kazhdan.HilbertComplexification
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Real orthogonal representations as complex operator representations

The relative-property-`(T)` interfaces in this repository quantify over real
orthogonal representations

`rho : G →* (E ≃ₗᵢ[ℝ] E)`.

The spectral-measure argument instead needs a representation by unitary
elements of the complex C-star algebra of bounded operators.  The existing
complexification constructs the intermediate representation on
`Complexification E` by complex linear isometries.  Mathlib's multiplicative
equivalence `Unitary.linearIsometryEquiv` supplies the remaining conversion.

This file records that conversion and the exact comparison on the embedded
real vector `x ↦ (x, 0)`.  In particular, complexification preserves every
displacement norm with no change of constants.  All statements are direct
constructions; no property-`(T)` or spectral hypothesis is used.
-/

namespace GroupApproximation

namespace RealToComplexUnitaryRepresentation

noncomputable section

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The unitary-operator representation obtained by complexifying a real
orthogonal representation. -/
def complexifiedUnitaryRepresentation
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) :
    G →* unitary
      (Complexification E →L[ℂ] Complexification E) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp
    (Complexification.mapHom rho)

/-- Coercing the complexified unitary to a bounded operator recovers the
complexified linear isometry. -/
@[simp] theorem complexifiedUnitaryRepresentation_coe
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) :
    ((complexifiedUnitaryRepresentation rho g :
        unitary (Complexification E →L[ℂ] Complexification E)) :
      Complexification E →L[ℂ] Complexification E) =
        Complexification.mapHom rho g :=
  rfl

/-- Pointwise form of the operator bridge: the complexified representation
acts separately on the real and imaginary coordinates. -/
@[simp] theorem complexifiedUnitaryRepresentation_apply
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G)
    (v : Complexification E) :
    ((complexifiedUnitaryRepresentation rho g :
        unitary (Complexification E →L[ℂ] Complexification E)) :
      Complexification E →L[ℂ] Complexification E) v =
        Complexification.mk (rho g v.re) (rho g v.im) :=
  rfl

/-- The same representation with the unitary subtype forgotten, as a monoid
homomorphism into the complex C-star algebra of bounded operators. -/
def complexifiedOperatorRepresentation
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) :
    G →* (Complexification E →L[ℂ] Complexification E) where
  toFun g := complexifiedUnitaryRepresentation rho g
  map_one' := congrArg
    (fun u : unitary (Complexification E →L[ℂ] Complexification E) ↦
      (u : Complexification E →L[ℂ] Complexification E))
    (map_one (complexifiedUnitaryRepresentation rho))
  map_mul' g h := congrArg
    (fun u : unitary (Complexification E →L[ℂ] Complexification E) ↦
      (u : Complexification E →L[ℂ] Complexification E))
    (map_mul (complexifiedUnitaryRepresentation rho) g h)

@[simp] theorem complexifiedOperatorRepresentation_apply
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G)
    (v : Complexification E) :
    complexifiedOperatorRepresentation rho g v =
      Complexification.mk (rho g v.re) (rho g v.im) :=
  rfl

/-- Every operator in the complexified representation is unitary. -/
theorem complexifiedOperatorRepresentation_mem_unitary
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) :
    complexifiedOperatorRepresentation rho g ∈
      unitary (Complexification E →L[ℂ] Complexification E) :=
  (complexifiedUnitaryRepresentation rho g).property

/-- Commuting group elements give commuting complexified operators. -/
theorem complexifiedOperatorRepresentation_commute
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {g h : G}
    (hgh : Commute g h) :
    Commute (complexifiedOperatorRepresentation rho g)
      (complexifiedOperatorRepresentation rho h) :=
  hgh.map (complexifiedOperatorRepresentation rho)

/-- A real vector embedded with zero imaginary coordinate has exactly the
same displacement after complexification. -/
theorem norm_complexified_displacement_mk_zero
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (x : E) :
    ‖complexifiedOperatorRepresentation rho g
          (Complexification.mk x 0) - Complexification.mk x 0‖ =
      ‖rho g x - x‖ := by
  rw [complexifiedOperatorRepresentation_apply]
  simp only [Complexification.re_mk, Complexification.im_mk, map_zero]
  exact Complexification.norm_mk_sub_mk (rho g x) x

/-- Near invariance of a real vector and near invariance of its complexified
copy are literally equivalent, with the same finite set and tolerance. -/
theorem complexified_near_iff
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (S : Finset G)
    (x : E) (delta : ℝ) :
    (∀ s ∈ S, ‖complexifiedOperatorRepresentation rho s
          (Complexification.mk x 0) - Complexification.mk x 0‖ < delta) ↔
      ∀ s ∈ S, ‖rho s x - x‖ < delta := by
  simp_rw [norm_complexified_displacement_mk_zero]

/-- The embedded real vector is fixed by a complexified operator exactly when
the original real vector is fixed. -/
theorem complexified_fixed_mk_zero_iff
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (x : E) :
    complexifiedOperatorRepresentation rho g (Complexification.mk x 0) =
        Complexification.mk x 0 ↔
      rho g x = x := by
  rw [complexifiedOperatorRepresentation_apply]
  simp only [Complexification.re_mk, Complexification.im_mk, map_zero]
  constructor
  · intro h
    exact congrArg Complexification.re h
  · intro h
    rw [h]

end

end RealToComplexUnitaryRepresentation

end GroupApproximation
