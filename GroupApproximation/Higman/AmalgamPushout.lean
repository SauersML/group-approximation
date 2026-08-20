import GroupApproximation.Higman.AmalgamPresentation
import Mathlib.GroupTheory.PushoutI

/-!
# The presented amalgam is Mathlib's pushout

`Higman.AmalgamPresentation` builds the amalgamated free product by hand, as
a quotient of the free product by the finitely many relators identifying two
copies of a generating set, and gets finite presentation out of that.  Mathlib
builds the same group as `Monoid.PushoutI`, and gets the normal form theorem
out of that --- `PushoutI.of_injective`, `PushoutI.base_injective` and
`Reduced.eq_empty_of_mem_range`, which is the statement that an alternating
product of letters outside the amalgamated subgroup never lands back inside
it.

Higman's constructions need both, so this file identifies the two.  Both
groups have the same universal property, so the identification is two `lift`s
and two `hom_ext`s, and nothing else.

The family is indexed by `Bool`, which is the smallest thing Mathlib's
indexed pushout accepts; `fam K₁ K₂` is the two-element family and `famHom`
the two structure maps.
-/

namespace GroupApproximation
namespace Higman
namespace Amalgam

open scoped Monoid.Coprod

variable {G K₁ K₂ : Type} [Group G] [Group K₁] [Group K₂]
  (e₁ : G →* K₁) (e₂ : G →* K₂)

/-! ## 1.  The two-element diagram -/

/-- The two-element family of groups. -/
def fam (K₁ K₂ : Type) : Bool → Type
  | false => K₁
  | true => K₂

instance famGroup : ∀ b, Group (fam K₁ K₂ b)
  | false => inferInstanceAs (Group K₁)
  | true => inferInstanceAs (Group K₂)

/-- The two structure maps of the diagram. -/
def famHom : ∀ b, G →* fam K₁ K₂ b
  | false => e₁
  | true => e₂

/-- Mathlib's amalgamated free product of the diagram. -/
abbrev Push : Type := Monoid.PushoutI (famHom e₁ e₂)

/-! ## 2.  The two comparison maps -/

/-- From the presented amalgam to the pushout. -/
def toPush : Amalg e₁ e₂ →* Push e₁ e₂ := by
  refine QuotientGroup.lift (Rel e₁ e₂ Set.univ)
    (Monoid.Coprod.lift
      (Monoid.PushoutI.of (φ := famHom e₁ e₂) false)
      (Monoid.PushoutI.of (φ := famHom e₁ e₂) true)) ?_
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨g, -, rfl⟩
  have h₁ : Monoid.PushoutI.of (φ := famHom e₁ e₂) false (e₁ g)
      = Monoid.PushoutI.base (famHom e₁ e₂) g :=
    Monoid.PushoutI.of_apply_eq_base (famHom e₁ e₂) false g
  have h₂ : Monoid.PushoutI.of (φ := famHom e₁ e₂) true (e₂ g)
      = Monoid.PushoutI.base (famHom e₁ e₂) g :=
    Monoid.PushoutI.of_apply_eq_base (famHom e₁ e₂) true g
  show Monoid.Coprod.lift _ _ (relator e₁ e₂ g) = 1
  simp only [relator, map_mul, map_inv, Monoid.Coprod.lift_apply_inl,
    Monoid.Coprod.lift_apply_inr]
  exact mul_inv_eq_one.mpr (h₁.trans h₂.symm)

/-- From the pushout to the presented amalgam. -/
def fromPush : Push e₁ e₂ →* Amalg e₁ e₂ := by
  refine Monoid.PushoutI.lift
    (fun b => match b with
      | false => inl e₁ e₂
      | true => inr e₁ e₂)
    ((inl e₁ e₂).comp e₁) ?_
  intro b
  cases b with
  | false => rfl
  | true => exact (inl_comp_eq_inr_comp e₁ e₂).symm

@[simp] theorem toPush_inl (a : K₁) :
    toPush e₁ e₂ (inl e₁ e₂ a) = Monoid.PushoutI.of (φ := famHom e₁ e₂) false a :=
  rfl

@[simp] theorem toPush_inr (b : K₂) :
    toPush e₁ e₂ (inr e₁ e₂ b) = Monoid.PushoutI.of (φ := famHom e₁ e₂) true b :=
  rfl

@[simp] theorem fromPush_of_false (a : K₁) :
    fromPush e₁ e₂ (Monoid.PushoutI.of (φ := famHom e₁ e₂) false a)
      = inl e₁ e₂ a := by
  unfold fromPush
  rw [Monoid.PushoutI.lift_of]
  rfl

@[simp] theorem fromPush_of_true (b : K₂) :
    fromPush e₁ e₂ (Monoid.PushoutI.of (φ := famHom e₁ e₂) true b)
      = inr e₁ e₂ b := by
  unfold fromPush
  rw [Monoid.PushoutI.lift_of]
  rfl

/-! ## 3.  They are inverse -/

theorem fromPush_comp_toPush :
    (fromPush e₁ e₂).comp (toPush e₁ e₂) = MonoidHom.id (Amalg e₁ e₂) := by
  have hsurj : Function.Surjective (QuotientGroup.mk' (Rel e₁ e₂ Set.univ)) :=
    QuotientGroup.mk'_surjective _
  refine (MonoidHom.cancel_right hsurj).mp ?_
  refine Monoid.Coprod.hom_ext ?_ ?_
  · refine MonoidHom.ext fun a => ?_
    show fromPush e₁ e₂ (toPush e₁ e₂ (inl e₁ e₂ a)) = inl e₁ e₂ a
    rw [toPush_inl, fromPush_of_false]
  · refine MonoidHom.ext fun b => ?_
    show fromPush e₁ e₂ (toPush e₁ e₂ (inr e₁ e₂ b)) = inr e₁ e₂ b
    rw [toPush_inr, fromPush_of_true]

theorem toPush_comp_fromPush :
    (toPush e₁ e₂).comp (fromPush e₁ e₂) = MonoidHom.id (Push e₁ e₂) := by
  refine Monoid.PushoutI.hom_ext ?_ ?_
  · intro b
    cases b with
    | false =>
        refine MonoidHom.ext fun a => ?_
        show toPush e₁ e₂ (fromPush e₁ e₂
          (Monoid.PushoutI.of (φ := famHom e₁ e₂) false a)) = _
        rw [fromPush_of_false, toPush_inl]
        rfl
    | true =>
        refine MonoidHom.ext fun a => ?_
        show toPush e₁ e₂ (fromPush e₁ e₂
          (Monoid.PushoutI.of (φ := famHom e₁ e₂) true a)) = _
        rw [fromPush_of_true, toPush_inr]
        rfl
  · refine MonoidHom.ext fun g => ?_
    have hbase : Monoid.PushoutI.base (famHom e₁ e₂) g
        = Monoid.PushoutI.of (φ := famHom e₁ e₂) false (e₁ g) :=
      (Monoid.PushoutI.of_apply_eq_base (famHom e₁ e₂) false g).symm
    show toPush e₁ e₂ (fromPush e₁ e₂
      (Monoid.PushoutI.base (famHom e₁ e₂) g)) = _
    rw [hbase, fromPush_of_false, toPush_inl]
    exact hbase.symm

/-- **The two amalgams agree.** -/
def pushEquiv : Amalg e₁ e₂ ≃* Push e₁ e₂ where
  toFun := toPush e₁ e₂
  invFun := fromPush e₁ e₂
  left_inv x :=
    congrArg (fun f : Amalg e₁ e₂ →* Amalg e₁ e₂ => f x)
      (fromPush_comp_toPush e₁ e₂)
  right_inv x :=
    congrArg (fun f : Push e₁ e₂ →* Push e₁ e₂ => f x)
      (toPush_comp_fromPush e₁ e₂)
  map_mul' := map_mul _

/-! ## 4.  Consequences -/

/-- **Mathlib's amalgamated product of two finitely presented groups over a
finitely generated one is finitely presented.**  This is the form the
constructions consume, because the normal form theorem lives on this side. -/
theorem isFinitelyPresented_push [Group.IsFinitelyPresented K₁]
    [Group.IsFinitelyPresented K₂] [Group.FG G] :
    Group.IsFinitelyPresented (Push e₁ e₂) := by
  letI : Group.IsFinitelyPresented (Amalg e₁ e₂) := isFinitelyPresented_amalg e₁ e₂
  exact Group.IsFinitelyPresented.equiv (pushEquiv e₁ e₂)

/-- The structure maps of the diagram are injective when the two embeddings
are, which is what `PushoutI`'s normal form theorem requires. -/
theorem famHom_injective (h₁ : Function.Injective e₁) (h₂ : Function.Injective e₂) :
    ∀ b, Function.Injective (famHom e₁ e₂ b) := by
  intro b
  cases b with
  | false => exact h₁
  | true => exact h₂

/-- Each factor embeds in the amalgam. -/
theorem of_injective_push (h₁ : Function.Injective e₁) (h₂ : Function.Injective e₂)
    (b : Bool) :
    Function.Injective (Monoid.PushoutI.of (φ := famHom e₁ e₂) b) :=
  Monoid.PushoutI.of_injective (famHom_injective e₁ e₂ h₁ h₂) b

/-- The amalgamated subgroup embeds in the amalgam. -/
theorem base_injective_push (h₁ : Function.Injective e₁)
    (h₂ : Function.Injective e₂) :
    Function.Injective (Monoid.PushoutI.base (famHom e₁ e₂)) :=
  Monoid.PushoutI.base_injective (famHom_injective e₁ e₂ h₁ h₂)

end Amalgam
end Higman
end GroupApproximation
