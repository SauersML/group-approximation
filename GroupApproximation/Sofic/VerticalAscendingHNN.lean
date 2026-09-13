import GroupApproximation.Sofic.MarkedCompressionGroup
import Mathlib.GroupTheory.HNNExtension
import GroupApproximation.Meta.AxiomGuard

/-!
# The vertical group is the ascending HNN extension

`non_mf_groups_exist.tex`, Section `sec:amenable-nonqd`, the construction of `W` (tex 1926–1935 at
origin/main 5b3910136):

> Put `T_α = lim→ (Γ →α Γ →α ⋯)`, `V = T_α ⋊ ⟨t⟩`, where `tgt⁻¹ = α(g)` on the level-zero copy
> of `Γ`, so that `V` is the ascending HNN extension of `Γ` along `α` and
> `T_α = ⋃_{n≥0} t^{-n} Γ t^n`.

`MarkedCompression.Vertical α hα` is the telescope extended by the shift.  This module proves both
identifications in the printed sentence.

* `verticalEquivHNN`: `V ≃* HNNExtension Γ ⊤ α.range φ_α`, Mathlib's HNN extension with
  `φ_α a = α a`.  It sends the stable letter to the stable letter and the level-zero copy of `γ`
  to `of γ`.  The closed endpoint is `manuscriptPrintedVerticalIsAscendingHNN`.
* `manuscriptSentence_telescopeIsUnionOfConjugates`: the telescope, inside `V`, is
  `⋃_{n≥0} t^{-n} Γ t^n`.
-/

namespace GroupApproximation
namespace VerticalAscendingHNN

open MarkedCompression MappingTelescope SemidirectProduct

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The printed `α`, read as an isomorphism from the whole group onto its image. -/
noncomputable def ascendingIso : (⊤ : Subgroup Γ) ≃* α.range :=
  MulEquiv.ofBijective (α.rangeRestrict.comp (⊤ : Subgroup Γ).subtype)
    ⟨fun a b hab => Subtype.ext (hα (congrArg Subtype.val hab)),
      fun b => by
        obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp b.2
        exact ⟨⟨x, Subgroup.mem_top x⟩, Subtype.ext hx⟩⟩

theorem ascendingIso_apply (a : (⊤ : Subgroup Γ)) :
    ((ascendingIso α hα a : α.range) : Γ) = α a := rfl

/-- The stable-letter relation of the HNN extension holds in `V`. -/
theorem iota_relation (a : (⊤ : Subgroup Γ)) :
    tVertical α hα * iotaVertical α hα (a : Γ) =
      iotaVertical α hα ((ascendingIso α hα a : α.range) : Γ) * tVertical α hα := by
  rw [ascendingIso_apply, ← vertical_compress α hα (a : Γ)]
  group

/-- `HNNExtension Γ ⊤ α.range φ_α →* V`, with `of γ ↦ ι γ` and `t ↦ t`. -/
noncomputable def toVertical :
    HNNExtension Γ ⊤ α.range (ascendingIso α hα) →* Vertical α hα :=
  HNNExtension.lift (iotaVertical α hα) (tVertical α hα) (iota_relation α hα)

/-- `V →* HNNExtension Γ ⊤ α.range φ_α`, from the universal property of the telescope. -/
noncomputable def toHNN :
    Vertical α hα →* HNNExtension Γ ⊤ α.range (ascendingIso α hα) :=
  verticalLift α hα HNNExtension.of HNNExtension.t
    (fun x => HNNExtension.equiv_eq_conj (φ := ascendingIso α hα) ⟨x, Subgroup.mem_top x⟩)

@[simp] theorem toVertical_of (γ : Γ) :
    toVertical α hα (HNNExtension.of γ) = iotaVertical α hα γ :=
  HNNExtension.lift_of _ _ _ γ

@[simp] theorem toVertical_t : toVertical α hα HNNExtension.t = tVertical α hα :=
  HNNExtension.lift_t _ _ _

@[simp] theorem toHNN_iota (γ : Γ) :
    toHNN α hα (iotaVertical α hα γ) = HNNExtension.of γ :=
  verticalLift_iota α hα _ _ _ γ

@[simp] theorem toHNN_t : toHNN α hα (tVertical α hα) = HNNExtension.t :=
  verticalLift_t α hα _ _ _

theorem toHNN_comp_toVertical :
    (toHNN α hα).comp (toVertical α hα) = MonoidHom.id _ := by
  apply HNNExtension.hom_ext
  · refine MonoidHom.ext fun γ => ?_
    simp
  · simp

theorem toVertical_comp_toHNN :
    (toVertical α hα).comp (toHNN α hα) = MonoidHom.id _ := by
  let S : Subgroup (Vertical α hα) :=
    { carrier := {v | toVertical α hα (toHNN α hα v) = v}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
        rw [ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_inv] at ha ⊢
        rw [ha] }
  refine MonoidHom.ext fun v => ?_
  exact vertical_mem_subgroup_of_iota_mem_of_t_mem α hα S
    (fun γ => by
      show toVertical α hα (toHNN α hα (iotaVertical α hα γ)) = iotaVertical α hα γ
      simp)
    (by
      show toVertical α hα (toHNN α hα (tVertical α hα)) = tVertical α hα
      simp)
    v

/-- **`V` is the ascending HNN extension of `Γ` along `α`.** -/
noncomputable def verticalEquivHNN :
    Vertical α hα ≃* HNNExtension Γ ⊤ α.range (ascendingIso α hα) :=
  MonoidHom.toMulEquiv (toHNN α hα) (toVertical α hα)
    (toVertical_comp_toHNN α hα) (toHNN_comp_toVertical α hα)

/-- **Printed sentence (tex 1933–1935), first identification, as a closed proposition.**

> so that `V` is the ascending HNN extension of `Γ` along `α` -/
def PrintedVerticalIsAscendingHNN : Prop :=
  ∀ (Γ : Type) [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α),
    ∃ e : Vertical α hα ≃* HNNExtension Γ ⊤ α.range (ascendingIso α hα),
      e (tVertical α hα) = HNNExtension.t ∧
        ∀ γ : Γ, e (iotaVertical α hα γ) = HNNExtension.of γ

theorem manuscriptPrintedVerticalIsAscendingHNN : PrintedVerticalIsAscendingHNN := by
  intro Γ _ α hα
  exact ⟨verticalEquivHNN α hα, toHNN_t α hα, toHNN_iota α hα⟩

/-- Level `n` of the telescope is the `t^{-n}`-conjugate of the level-zero copy. -/
theorem inl_level_eq_conj (n : ℕ) (γ : Γ) :
    (inl (level α hα n γ) : Vertical α hα) =
      (tVertical α hα ^ n)⁻¹ * iotaVertical α hα γ * tVertical α hα ^ n := by
  induction n with
  | zero => simp [iotaVertical]
  | succ n ih =>
      rw [inl_level_succ, ih, pow_succ]
      group

/-- **Printed sentence (tex 1933–1935), second identification.**

> and `T_α = ⋃_{n≥0} t^{-n} Γ t^n`. -/
theorem manuscriptSentence_telescopeIsUnionOfConjugates :
    Set.range (inl : Telescope α hα →* Vertical α hα) =
      ⋃ n : ℕ, {v : Vertical α hα | ∃ γ : Γ,
        v = (tVertical α hα ^ n)⁻¹ * iotaVertical α hα γ * tVertical α hα ^ n} := by
  ext v
  simp only [Set.mem_range, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨n, γ⟩, rfl⟩ := MappingTelescope.mk_surjective α hα x
    exact ⟨n, γ, inl_level_eq_conj α hα n γ⟩
  · rintro ⟨n, γ, rfl⟩
    exact ⟨level α hα n γ, inl_level_eq_conj α hα n γ⟩

end VerticalAscendingHNN
end GroupApproximation

open GroupApproximation.VerticalAscendingHNN

#audit_closed_axioms manuscriptPrintedVerticalIsAscendingHNN
#audit_axioms verticalEquivHNN
#audit_axioms manuscriptSentence_telescopeIsUnionOfConjugates
