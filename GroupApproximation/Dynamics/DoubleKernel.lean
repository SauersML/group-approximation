import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group
import GroupApproximation.Sofic.WeakMFNonsoficDouble

/-!
# The pointed free-group action in a group double

For a pointed group set, the kernel model has one free generator at every
non-base site. Translation acts by changing the basepoint in each generator.

For a subgroup `Γ ≤ A` and the coset space `A ⧸ Γ` pointed at the trivial
coset, the symmetric double `A *_Γ A` is isomorphic to the semidirect product
of this free kernel by `A` (`doubleModelEquiv`). The first copy of `A` goes to
the acting group, and the second copy of `g` goes to `(e_(g x₀)⁻¹, g)`.
-/

namespace GroupApproximation.Surjunctivity.DoubleKernel

universe u v w

variable {X : Type u} (x₀ : X)

abbrev Kernel := FreeGroup {x : X // x ≠ x₀}

/-- The base-site letter is the identity. -/
noncomputable def letter (x : X) : Kernel x₀ := by
  classical
  exact if h : x = x₀ then 1 else FreeGroup.of ⟨x, h⟩

@[simp] theorem letter_base : letter x₀ x₀ = 1 := by simp [letter]

@[simp] theorem letter_of (x : {x : X // x ≠ x₀}) :
    letter x₀ x.1 = FreeGroup.of x := by simp [letter, x.property]

theorem freeHom_ext {Y : Type v} [Group Y]
    {f g : Kernel x₀ →* Y}
    (h : ∀ x, f (FreeGroup.of x) = g (FreeGroup.of x)) : f = g :=
  FreeGroup.lift.symm.injective (funext h)

variable {G : Type v} [Group G] [MulAction G X]

/-- Translate a free generator and cancel the translated basepoint. -/
noncomputable def actionHom (g : G) : Kernel x₀ →* Kernel x₀ :=
  FreeGroup.lift fun x => letter x₀ (g • x.1) * (letter x₀ (g • x₀))⁻¹

@[simp] theorem actionHom_letter (g : G) (x : X) :
    actionHom x₀ g (letter x₀ x) =
      letter x₀ (g • x) * (letter x₀ (g • x₀))⁻¹ := by
  classical
  by_cases hx : x = x₀
  · subst x
    simp
  · simp [letter, hx, actionHom]

@[simp] theorem actionHom_one : actionHom x₀ (1 : G) = MonoidHom.id _ := by
  apply freeHom_ext
  intro x
  change actionHom x₀ 1 (FreeGroup.of x) = FreeGroup.of x
  rw [← letter_of x₀ x, actionHom_letter]
  simp

theorem actionHom_mul (g h : G) :
    (actionHom x₀ g).comp (actionHom x₀ h) = actionHom x₀ (g * h) := by
  apply freeHom_ext
  intro x
  change actionHom x₀ g (actionHom x₀ h (FreeGroup.of x)) =
    actionHom x₀ (g * h) (FreeGroup.of x)
  rw [← letter_of x₀ x]
  simp only [actionHom_letter, map_mul, map_inv, mul_inv_rev, inv_inv,
    mul_assoc, inv_mul_cancel_left, mul_smul]

/-- Translation is an automorphism, inverted by inverse translation. -/
noncomputable def actionAut (g : G) : MulAut (Kernel x₀) where
  toFun := actionHom x₀ g
  invFun := actionHom x₀ g⁻¹
  left_inv n := by
    have h := DFunLike.congr_fun (actionHom_mul x₀ g⁻¹ g) n
    simpa only [MonoidHom.comp_apply, inv_mul_cancel, actionHom_one,
      MonoidHom.id_apply] using h
  right_inv n := by
    have h := DFunLike.congr_fun (actionHom_mul x₀ g g⁻¹) n
    simpa only [MonoidHom.comp_apply, mul_inv_cancel, actionHom_one,
      MonoidHom.id_apply] using h
  map_mul' := (actionHom x₀ g).map_mul

/-- The group action on the pointed free group. -/
noncomputable def action : G →* MulAut (Kernel x₀) where
  toFun := actionAut x₀
  map_one' := by
    apply MulEquiv.ext
    intro n
    exact DFunLike.congr_fun (actionHom_one x₀) n
  map_mul' g h := by
    apply MulEquiv.ext
    intro n
    exact (DFunLike.congr_fun (actionHom_mul x₀ g h) n).symm

@[simp] theorem action_letter (g : G) (x : X) :
    action x₀ g (letter x₀ x) =
      letter x₀ (g • x) * (letter x₀ (g • x₀))⁻¹ := actionHom_letter x₀ g x

/-- The second copy of the acting group in the free-kernel semidirect model. -/
noncomputable def secondCopy : G →* SemidirectProduct (Kernel x₀) G (action x₀) where
  toFun g := ⟨(letter x₀ (g • x₀))⁻¹, g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · simp
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change (letter x₀ ((g * h) • x₀))⁻¹ =
        (letter x₀ (g • x₀))⁻¹ * actionHom x₀ g ((letter x₀ (h • x₀))⁻¹)
      rw [map_inv, actionHom_letter, mul_inv_rev, inv_inv]
      simp only [mul_smul, inv_mul_cancel_left]
    · rfl

@[simp] theorem secondCopy_left (g : G) :
    (secondCopy x₀ g).left = (letter x₀ (g • x₀))⁻¹ := rfl

@[simp] theorem secondCopy_right (g : G) : (secondCopy x₀ g).right = g := rfl

theorem secondCopy_eq_inr {g : G} (hg : g • x₀ = x₀) :
    secondCopy x₀ g = SemidirectProduct.inr (φ := action x₀) g := by
  apply SemidirectProduct.ext
  · simp [hg]
  · rfl

theorem secondCopy_eq_inl_mul_inr (g : G) :
    secondCopy x₀ g =
      SemidirectProduct.inl (letter x₀ (g • x₀))⁻¹ * SemidirectProduct.inr g := by
  rw [← SemidirectProduct.inl_left_mul_inr_right (secondCopy x₀ g), secondCopy_left,
    secondCopy_right]

section Double

variable (A : Type u) [Group A] (Γ : Subgroup A)

abbrev baseSite : A ⧸ Γ := QuotientGroup.mk 1

abbrev Model := SemidirectProduct (Kernel (baseSite A Γ)) A (action (baseSite A Γ))

theorem subgroup_fixes_base (γ : Γ) : (γ : A) • baseSite A Γ = baseSite A Γ := by
  change (QuotientGroup.mk ((γ : A) * 1) : A ⧸ Γ) = QuotientGroup.mk 1
  apply Quotient.sound
  change QuotientGroup.leftRel Γ ((γ : A) * 1) 1
  rw [QuotientGroup.leftRel_apply]
  simpa only [mul_one] using Γ.inv_mem γ.property

theorem smul_baseSite (g : A) : g • baseSite A Γ = (QuotientGroup.mk g : A ⧸ Γ) := by
  change (QuotientGroup.mk (g * 1) : A ⧸ Γ) = QuotientGroup.mk g
  rw [mul_one]

noncomputable def modelCopy : ∀ b, DoubleFactor A b →* Model A Γ
  | true => SemidirectProduct.inr
  | false => secondCopy (baseSite A Γ)

theorem modelCopy_agree : ∀ b,
    (modelCopy A Γ b).comp (doubleMap A Γ b) =
      (SemidirectProduct.inr (φ := action (baseSite A Γ))).comp Γ.subtype := by
  intro b
  cases b with
  | true => rfl
  | false =>
    apply MonoidHom.ext
    intro γ
    exact secondCopy_eq_inr (baseSite A Γ) (subgroup_fixes_base A Γ γ)

/-- The two copies of the base group give the map from the amalgam to the model. -/
noncomputable def toModel : SymmetricDouble A Γ →* Model A Γ :=
  Monoid.PushoutI.lift (modelCopy A Γ)
    ((SemidirectProduct.inr (φ := action (baseSite A Γ))).comp Γ.subtype)
    (modelCopy_agree A Γ)

@[simp] theorem toModel_inDouble (b : Bool) (g : A) :
    toModel A Γ (inDouble A Γ b g) = modelCopy A Γ b g := by
  exact Monoid.PushoutI.lift_of (φ := doubleMap A Γ) (modelCopy A Γ)
    ((SemidirectProduct.inr (φ := action (baseSite A Γ))).comp Γ.subtype)
    (modelCopy_agree A Γ) (i := b) g

theorem inDouble_agree (γ : Γ) :
    inDouble A Γ true γ = inDouble A Γ false γ := by
  exact (Monoid.PushoutI.of_apply_eq_base (doubleMap A Γ) true γ).trans
    (Monoid.PushoutI.of_apply_eq_base (doubleMap A Γ) false γ).symm

def difference (g : A) : SymmetricDouble A Γ :=
  inDouble A Γ true g * (inDouble A Γ false g)⁻¹

theorem difference_mul_subgroup (g : A) (γ : Γ) :
    difference A Γ (g * γ) = difference A Γ g := by
  simp only [difference, map_mul, mul_inv_rev]
  rw [inDouble_agree A Γ γ]
  group

/-- The difference between the two copies depends only on the coset. -/
def cosetDifference : A ⧸ Γ → SymmetricDouble A Γ :=
  Quotient.lift (difference A Γ) (by
    intro g h hrel
    have hm : g⁻¹ * h ∈ Γ := QuotientGroup.leftRel_apply.mp hrel
    let γ : Γ := ⟨g⁻¹ * h, hm⟩
    have hgh : g * (γ : A) = h := mul_inv_cancel_left g h
    exact (hgh ▸ difference_mul_subgroup A Γ g γ).symm)

@[simp] theorem cosetDifference_mk (g : A) :
    cosetDifference A Γ (QuotientGroup.mk g) = difference A Γ g := rfl

@[simp] theorem cosetDifference_base : cosetDifference A Γ (baseSite A Γ) = 1 := by
  simp [baseSite, difference]

/-- The candidate free-kernel inclusion into the double. -/
noncomputable def kernelToDouble : Kernel (baseSite A Γ) →* SymmetricDouble A Γ :=
  FreeGroup.lift fun q => cosetDifference A Γ q.1

@[simp] theorem kernelToDouble_letter (q : A ⧸ Γ) :
    kernelToDouble A Γ (letter (baseSite A Γ) q) = cosetDifference A Γ q := by
  classical
  by_cases hq : q = baseSite A Γ
  · subst q
    rw [letter_base, map_one, cosetDifference_base]
  · simp [letter, hq, kernelToDouble]

theorem cosetDifference_translate (g : A) (q : A ⧸ Γ) :
    cosetDifference A Γ (g • q) * (cosetDifference A Γ (g • baseSite A Γ))⁻¹ =
      inDouble A Γ true g * cosetDifference A Γ q * (inDouble A Γ true g)⁻¹ := by
  induction q using Quotient.inductionOn with
  | h h =>
    change difference A Γ (g * h) * (difference A Γ (g * 1))⁻¹ =
      inDouble A Γ true g * difference A Γ h * (inDouble A Γ true g)⁻¹
    simp only [difference, map_mul, mul_one]
    group

theorem kernelToDouble_equivariant (g : A) :
    (kernelToDouble A Γ).comp (action (baseSite A Γ) g).toMonoidHom =
      (MulAut.conj (inDouble A Γ true g)).toMonoidHom.comp (kernelToDouble A Γ) := by
  apply freeHom_ext
  intro q
  change kernelToDouble A Γ (action (baseSite A Γ) g (FreeGroup.of q)) =
    inDouble A Γ true g * kernelToDouble A Γ (FreeGroup.of q) *
      (inDouble A Γ true g)⁻¹
  rw [← letter_of (baseSite A Γ) q, action_letter, map_mul, map_inv,
    kernelToDouble_letter, kernelToDouble_letter, kernelToDouble_letter]
  exact cosetDifference_translate A Γ g q.1

/-- The map back from the semidirect model to the symmetric amalgam. -/
noncomputable def fromModel : Model A Γ →* SymmetricDouble A Γ :=
  SemidirectProduct.lift (kernelToDouble A Γ) (inDouble A Γ true)
    (kernelToDouble_equivariant A Γ)

@[simp] theorem fromModel_inl (n : Kernel (baseSite A Γ)) :
    fromModel A Γ (SemidirectProduct.inl n) = kernelToDouble A Γ n :=
  SemidirectProduct.lift_inl _ _ _ n

@[simp] theorem fromModel_inr (g : A) :
    fromModel A Γ (SemidirectProduct.inr g) = inDouble A Γ true g :=
  SemidirectProduct.lift_inr _ _ _ g

theorem fromModel_toModel : (fromModel A Γ).comp (toModel A Γ) = MonoidHom.id _ := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro b
  apply MonoidHom.ext
  intro g
  change fromModel A Γ (toModel A Γ (inDouble A Γ b g)) = inDouble A Γ b g
  rw [toModel_inDouble]
  cases b with
  | true => exact fromModel_inr A Γ g
  | false =>
    change kernelToDouble A Γ ((letter (baseSite A Γ) (g • baseSite A Γ))⁻¹) *
      inDouble A Γ true g = inDouble A Γ false g
    rw [map_inv, kernelToDouble_letter]
    change (difference A Γ (g * 1))⁻¹ * inDouble A Γ true g = inDouble A Γ false g
    simp only [mul_one, difference]
    group

/-- The difference of the two copies of `g` is the letter of the coset of `g`. -/
theorem toModel_difference (g : A) :
    toModel A Γ (difference A Γ g) =
      SemidirectProduct.inl (letter (baseSite A Γ) (QuotientGroup.mk g)) := by
  rw [difference, map_mul, map_inv, toModel_inDouble, toModel_inDouble]
  change SemidirectProduct.inr g * (secondCopy (baseSite A Γ) g)⁻¹ = _
  rw [secondCopy_eq_inl_mul_inr, mul_inv_rev, mul_inv_cancel_left, map_inv, inv_inv,
    smul_baseSite]

theorem toModel_fromModel : (toModel A Γ).comp (fromModel A Γ) = MonoidHom.id _ := by
  apply SemidirectProduct.hom_ext
  · apply freeHom_ext
    rintro ⟨c, hc⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have hletter : (FreeGroup.of ⟨QuotientGroup.mk g, hc⟩ : Kernel (baseSite A Γ)) =
        letter (baseSite A Γ) (QuotientGroup.mk g) :=
      (letter_of (baseSite A Γ) ⟨QuotientGroup.mk g, hc⟩).symm
    change toModel A Γ (fromModel A Γ
        (SemidirectProduct.inl (FreeGroup.of ⟨QuotientGroup.mk g, hc⟩))) =
      SemidirectProduct.inl (FreeGroup.of ⟨QuotientGroup.mk g, hc⟩)
    rw [hletter, fromModel_inl, kernelToDouble_letter]
    exact toModel_difference A Γ g
  · apply MonoidHom.ext
    intro g
    change toModel A Γ (fromModel A Γ (SemidirectProduct.inr g)) = SemidirectProduct.inr g
    rw [fromModel_inr, toModel_inDouble]
    rfl

/-- The symmetric double is isomorphic to its free-kernel semidirect model. -/
noncomputable def doubleModelEquiv : SymmetricDouble A Γ ≃* Model A Γ :=
  MonoidHom.toMulEquiv (toModel A Γ) (fromModel A Γ) (fromModel_toModel A Γ)
    (toModel_fromModel A Γ)

end Double

end GroupApproximation.Surjunctivity.DoubleKernel
