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

namespace CentralExtension

variable {U H E : Type} [Group U] [Group H] [Group E]

/-- The fiber product of two central extensions over the same base, viewed as
a subgroup of the product of their covering groups. -/
def pullbackSubgroup (P : CentralExtension U H)
    (Q : CentralExtension E H) : Subgroup (U × E) where
  carrier := {z | P.projection z.1 = Q.projection z.2}
  one_mem' := by
    change P.projection 1 = Q.projection 1
    simp
  mul_mem' := by
    intro x y hx hy
    change P.projection (x.1 * y.1) = Q.projection (x.2 * y.2)
    rw [map_mul, map_mul]
    rw [hx, hy]
  inv_mem' := by
    intro x hx
    change P.projection x.1⁻¹ = Q.projection x.2⁻¹
    rw [map_inv, map_inv]
    rw [hx]

/-- Projection of the fiber product to the first covering group. -/
def pullbackProjection (P : CentralExtension U H)
    (Q : CentralExtension E H) : P.pullbackSubgroup Q →* U where
  toFun z := z.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection of the fiber product to the second covering group. -/
def pullbackSecond (P : CentralExtension U H)
    (Q : CentralExtension E H) : P.pullbackSubgroup Q →* E where
  toFun z := z.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem pullback_condition (P : CentralExtension U H)
    (Q : CentralExtension E H) (z : P.pullbackSubgroup Q) :
    P.projection (P.pullbackProjection Q z) =
      Q.projection (P.pullbackSecond Q z) :=
  z.property

/-- The fiber product projects to the first cover as a central extension. -/
def pullback (P : CentralExtension U H)
    (Q : CentralExtension E H) :
    CentralExtension (P.pullbackSubgroup Q) U where
  projection := P.pullbackProjection Q
  surjective := by
    intro u
    obtain ⟨e, he⟩ := Q.surjective (P.projection u)
    exact ⟨⟨(u, e), he.symm⟩, rfl⟩
  ker_le_center := by
    intro z hz
    have hz1 : z.1.1 = 1 := MonoidHom.mem_ker.mp hz
    have hz2ker : z.1.2 ∈ Q.projection.ker := by
      rw [MonoidHom.mem_ker]
      have hcondition : P.projection z.1.1 = Q.projection z.1.2 :=
        z.property
      rw [hz1, map_one] at hcondition
      exact hcondition.symm
    have hz2center : z.1.2 ∈ Subgroup.center E :=
      Q.ker_le_center hz2ker
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    apply Prod.ext
    · change x.1.1 * z.1.1 = z.1.1 * x.1.1
      rw [hz1]
      simp
    · change x.1.2 * z.1.2 = z.1.2 * x.1.2
      exact Subgroup.mem_center_iff.mp hz2center x.1.2

end CentralExtension

namespace UniversalCentralExtension

variable {U H : Type} [Group U] [Group H]

/-- Recognition theorem in the form needed for Steinberg groups: a central
extension with perfect covering group is universal if every central extension
of the covering group splits. -/
noncomputable def of_every_centralExtension_splits
    (P : CentralExtension U H) (hperfect : Group.IsPerfect U)
    (hsplit : ∀ {E : Type} [Group E] (Q : CentralExtension E U),
      ∃ s : U →* E, Q.projection.comp s = MonoidHom.id U) :
    UniversalCentralExtension U H where
  toCentralExtension := P
  isPerfect := hperfect
  exists_lift := by
    intro E _ Q
    let T : CentralExtension (P.pullbackSubgroup Q) U := P.pullback Q
    obtain ⟨s, hs⟩ := hsplit T
    let f : U →* E := (P.pullbackSecond Q).comp s
    refine ⟨f, ?_⟩
    apply MonoidHom.ext
    intro u
    change Q.projection (P.pullbackSecond Q (s u)) = P.projection u
    rw [← P.pullback_condition Q (s u)]
    have hsu : P.pullbackProjection Q (s u) = u := by
      have := DFunLike.congr_fun hs u
      exact this
    rw [hsu]

end UniversalCentralExtension
end NonsoficGroupsExist
