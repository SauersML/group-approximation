import NonsoficGroupsExist.Sofic.CentralCoverInheritance

/-!
# Universal central extensions

This file gives the categorical interface needed by the unconditional
Steinberg route.  A universal central extension is a central extension with
a perfect covering group and a lift to every other central extension of the
same base.  Perfectness makes such a lift unique; the proof is included here
rather than stored as an additional field.
-/

namespace NonsoficGroupsExist

/-- A universal central extension, expressed using the project's concrete
`CentralExtension` interface.  Existence of a lift is stored; uniqueness is a
theorem because it follows from perfectness of the covering group. -/
structure UniversalCentralExtension (U H : Type) [Group U] [Group H]
    extends CentralExtension U H where
  isPerfect : Group.IsPerfect U
  exists_lift : ∀ {E : Type} [Group E] (Q : CentralExtension E H),
    ∃ f : U →* E, Q.projection.comp f = projection

namespace UniversalCentralExtension

open scoped commutatorElement

variable {U H E : Type} [Group U] [Group H] [Group E]

/-- The pointwise difference of two maps over the same central quotient is a
homomorphism into the center. -/
noncomputable def differenceHom
    (P : UniversalCentralExtension U H)
    (Q : CentralExtension E H) (f g : U →* E)
    (hf : Q.projection.comp f = P.projection)
    (hg : Q.projection.comp g = P.projection) :
    U →* Subgroup.center E where
  toFun x := ⟨f x * (g x)⁻¹, by
    apply Q.ker_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have hfx : Q.projection (f x) = P.projection x :=
      DFunLike.congr_fun hf x
    have hgx : Q.projection (g x) = P.projection x :=
      DFunLike.congr_fun hg x
    rw [hfx, hgx]
    simp⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
    have hdy : f y * (g y)⁻¹ ∈ Subgroup.center E := by
      apply Q.ker_le_center
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have hfy : Q.projection (f y) = P.projection y :=
        DFunLike.congr_fun hf y
      have hgy : Q.projection (g y) = P.projection y :=
        DFunLike.congr_fun hg y
      rw [hfy, hgy]
      simp
    have hc : Commute (g x)⁻¹ (f y * (g y)⁻¹) := by
      exact Subgroup.mem_center_iff.mp hdy (g x)⁻¹
    calc
      f x * f y * ((g y)⁻¹ * (g x)⁻¹) =
          f x * (f y * (g y)⁻¹) * (g x)⁻¹ := by
            simp only [mul_assoc]
      _ = f x * ((g x)⁻¹ * (f y * (g y)⁻¹)) := by
            rw [hc.eq]
            exact mul_assoc _ _ _
      _ = (f x * (g x)⁻¹) * (f y * (g y)⁻¹) := by
            exact (mul_assoc _ _ _).symm

/-- Two homomorphisms from a universal cover over the same base are equal.
This is the standard perfect-domain uniqueness lemma. -/
theorem hom_ext
    (P : UniversalCentralExtension U H)
    (Q : CentralExtension E H) (f g : U →* E)
    (hf : Q.projection.comp f = P.projection)
    (hg : Q.projection.comp g = P.projection) : f = g := by
  letI : Group.IsPerfect U := P.isPerfect
  let d : U →* Subgroup.center E := P.differenceHom Q f g hf hg
  have hcomm : commutator U ≤ d.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, b, rfl⟩
    change d ⁅a, b⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    apply Subtype.ext
    change (d a : E) * (d b : E) = (d b : E) * (d a : E)
    exact (Subgroup.mem_center_iff.mp (d a).property (d b : E)).symm
  have hd : ∀ x : U, d x = 1 := by
    intro x
    apply MonoidHom.mem_ker.mp
    exact hcomm (Group.IsPerfect.mem_commutator (G := U) (g := x))
  apply MonoidHom.ext
  intro x
  have hx := congrArg Subtype.val (hd x)
  change f x * (g x)⁻¹ = 1 at hx
  exact mul_inv_eq_one.mp hx

/-- The universal property in its usual `∃!` form. -/
theorem existsUnique_lift
    (P : UniversalCentralExtension U H)
    (Q : CentralExtension E H) :
    ∃! f : U →* E, Q.projection.comp f = P.projection := by
  obtain ⟨f, hf⟩ := P.exists_lift (E := E) Q
  exact ⟨f, hf, fun g hg ↦ P.hom_ext Q g f hg hf⟩

end UniversalCentralExtension
end NonsoficGroupsExist
