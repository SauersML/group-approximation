import GroupApproximation.Sofic.FreeLampKernelSplitting
import GroupApproximation.Sofic.SymmetricDoubleFlip

/-!
# At a two-element lamp the covering *is* the symmetric double

`Sofic/FreeLampKernelSplitting` identifies the kernel of `G *_Γ (Γ × K) → K`
with the `K`-fold amalgam `⋆_{Γ, k ∈ K} G`.  At `K = C₂` that amalgam has two
vertices, so it should be the two-vertex symmetric double `G *_Γ G` itself.
This file proves exactly that, and draws the consequences.

## Why the identification is worth its own file

The literature input on the MF side of the Kun--Thom/Shulman construction is
Shulman's amalgamation theorem.  Its **symmetric** form, Theorem 10, is about
`A *_C A`: two copies, one subalgebra.  The general `K`-fold statement needs the
finitely-many-factors form as well.  With

```text
IteratedDouble G Γ FlipC2  ≃*  SymmetricDouble G Γ
```

proved here, the `C₂` member of the free-lamp family needs only the symmetric
theorem -- and its group-level conclusion `IsOperatorMF (SymmetricDouble G Γ)`
is *literally the `operatorMF` field* of the existing
`KunThomShulmanDoubleData`.  So the datum the repository already quarantines
now buys the free-lamp amalgam too, with no new citation.

## What is proved

* `symmetricDoubleEquivIteratedBool` -- the `Bool`-indexed amalgam is the
  symmetric double, by mutually inverse lifts; and `symmetricDoubleEquivIteratedFlip`
  transports it along `FlipC2 ≃ Bool`;
* `isOperatorMF_freeLampFlip_iff_isOperatorMF_symmetricDouble` -- operator-MF of
  the `C₂` free-lamp amalgam and of the symmetric double are **equivalent**;
* `isSofic_freeLampFlip_iff_isSofic_symmetricDouble` -- likewise for soficity.
  `Sofic/DoubleSoficTransfer` already proved the forward direction through the
  flip semidirect product; the converse is new and comes from the covering, and
  the two routes agree.

All unconditional.
-/

namespace GroupApproximation

open Monoid

/-! ## The `Bool`-indexed amalgam is the symmetric double -/

/-- The symmetric double, read into the `Bool`-indexed amalgam vertex by
vertex. -/
def doubleToIteratedBool (G : Type) [Group G] (Γ : Subgroup G) :
    SymmetricDouble G Γ →* IteratedDouble G Γ Bool :=
  doubleToIterated G Γ false true

@[simp] theorem doubleToIteratedBool_inDouble (G : Type) [Group G]
    (Γ : Subgroup G) (b : Bool) (g : G) :
    doubleToIteratedBool G Γ (inDouble G Γ b g)
      = inIterated G Γ Bool b g := by
  show doubleToIterated G Γ false true (inDouble G Γ b g) = _
  rw [doubleToIterated_inDouble]
  cases b <;> rfl

@[simp] theorem doubleToIteratedBool_base (G : Type) [Group G]
    (Γ : Subgroup G) (γ : ↥Γ) :
    doubleToIteratedBool G Γ (PushoutI.base (doubleMap G Γ) γ)
      = PushoutI.base (iteratedMap G Γ Bool) γ :=
  PushoutI.lift_base _ _ _ _

/-- The vertex maps in the other direction. -/
def iteratedBoolToDoubleMaps (G : Type) [Group G] (Γ : Subgroup G) :
    ∀ b : Bool, IteratedFactor G Bool b →* SymmetricDouble G Γ :=
  fun b ↦ inDouble G Γ b

theorem iteratedBoolToDoubleMaps_comp (G : Type) [Group G] (Γ : Subgroup G) :
    ∀ b : Bool, (iteratedBoolToDoubleMaps G Γ b).comp (iteratedMap G Γ Bool b)
      = PushoutI.base (doubleMap G Γ) :=
  fun b ↦ PushoutI.of_comp_eq_base b

/-- The `Bool`-indexed amalgam, read back into the symmetric double. -/
def iteratedBoolToDouble (G : Type) [Group G] (Γ : Subgroup G) :
    IteratedDouble G Γ Bool →* SymmetricDouble G Γ :=
  PushoutI.lift (iteratedBoolToDoubleMaps G Γ) (PushoutI.base (doubleMap G Γ))
    (iteratedBoolToDoubleMaps_comp G Γ)

@[simp] theorem iteratedBoolToDouble_inIterated (G : Type) [Group G]
    (Γ : Subgroup G) (b : Bool) (g : G) :
    iteratedBoolToDouble G Γ (inIterated G Γ Bool b g) = inDouble G Γ b g :=
  PushoutI.lift_of _ _ _ _

@[simp] theorem iteratedBoolToDouble_base (G : Type) [Group G] (Γ : Subgroup G)
    (γ : ↥Γ) :
    iteratedBoolToDouble G Γ (PushoutI.base (iteratedMap G Γ Bool) γ)
      = PushoutI.base (doubleMap G Γ) γ :=
  PushoutI.lift_base _ _ _ _

theorem iteratedBoolToDouble_comp_doubleToIteratedBool (G : Type) [Group G]
    (Γ : Subgroup G) :
    (iteratedBoolToDouble G Γ).comp (doubleToIteratedBool G Γ)
      = MonoidHom.id _ := by
  apply PushoutI.hom_ext_nonempty
  intro b
  ext g
  change iteratedBoolToDouble G Γ
      (doubleToIteratedBool G Γ (inDouble G Γ b g)) = inDouble G Γ b g
  rw [doubleToIteratedBool_inDouble, iteratedBoolToDouble_inIterated]

theorem doubleToIteratedBool_comp_iteratedBoolToDouble (G : Type) [Group G]
    (Γ : Subgroup G) :
    (doubleToIteratedBool G Γ).comp (iteratedBoolToDouble G Γ)
      = MonoidHom.id _ := by
  refine iteratedDouble_hom_ext G Γ (fun b g ↦ ?_) (fun γ ↦ ?_)
  · show doubleToIteratedBool G Γ
        (iteratedBoolToDouble G Γ (inIterated G Γ Bool b g))
      = inIterated G Γ Bool b g
    rw [iteratedBoolToDouble_inIterated, doubleToIteratedBool_inDouble]
  · show doubleToIteratedBool G Γ (iteratedBoolToDouble G Γ
        (PushoutI.base (iteratedMap G Γ Bool) γ))
      = PushoutI.base (iteratedMap G Γ Bool) γ
    rw [iteratedBoolToDouble_base, doubleToIteratedBool_base]

/-- **The two-vertex amalgam is the symmetric double.** -/
def symmetricDoubleEquivIteratedBool (G : Type) [Group G] (Γ : Subgroup G) :
    SymmetricDouble G Γ ≃* IteratedDouble G Γ Bool where
  toFun := doubleToIteratedBool G Γ
  invFun := iteratedBoolToDouble G Γ
  left_inv x :=
    DFunLike.congr_fun
      (iteratedBoolToDouble_comp_doubleToIteratedBool G Γ) x
  right_inv y :=
    DFunLike.congr_fun
      (doubleToIteratedBool_comp_iteratedBoolToDouble G Γ) y
  map_mul' := (doubleToIteratedBool G Γ).map_mul

/-! ## The order-two lamp as a two-element vertex set -/

/-- The order-two lamp group, as a two-element index set. -/
def flipC2EquivBool : FlipC2 ≃ Bool where
  toFun
    | .one => false
    | .swap => true
  invFun
    | false => .one
    | true => .swap
  left_inv := by
    intro k
    cases k <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

/-- **The covering of the `C₂` free-lamp amalgam is the symmetric double.** -/
def symmetricDoubleEquivIteratedFlip (G : Type) [Group G] (Γ : Subgroup G) :
    SymmetricDouble G Γ ≃* IteratedDouble G Γ FlipC2 :=
  (symmetricDoubleEquivIteratedBool G Γ).trans
    (iteratedEquivOfEquiv G Γ flipC2EquivBool.symm)

/-! ## Consequences at the order-two lamp -/

/-- **Operator-MF of the symmetric double gives operator-MF of the `C₂`
free-lamp amalgam.**  This is the step for which only the *symmetric*
amalgamation theorem is needed. -/
theorem isOperatorMF_freeLampFlip_of_isOperatorMF_symmetricDouble
    (G : Type) [Group G] (Γ : Subgroup G)
    (h : IsOperatorMF (SymmetricDouble G Γ)) :
    IsOperatorMF (FreeLamp G Γ FlipC2) :=
  isOperatorMF_freeLamp_of_isOperatorMF_iterated G Γ FlipC2
    (isOperatorMF_of_mulEquiv (symmetricDoubleEquivIteratedFlip G Γ) h)

theorem isOperatorMF_symmetricDouble_of_isOperatorMF_freeLampFlip
    (G : Type) [Group G] (Γ : Subgroup G)
    (h : IsOperatorMF (FreeLamp G Γ FlipC2)) :
    IsOperatorMF (SymmetricDouble G Γ) :=
  isOperatorMF_of_mulEquiv (symmetricDoubleEquivIteratedFlip G Γ).symm
    (isOperatorMF_iterated_of_isOperatorMF_freeLamp G Γ FlipC2 h)

/-- Operator-MF cannot tell the symmetric double from its `C₂` free-lamp
amalgam. -/
theorem isOperatorMF_freeLampFlip_iff_isOperatorMF_symmetricDouble
    (G : Type) [Group G] (Γ : Subgroup G) :
    IsOperatorMF (FreeLamp G Γ FlipC2) ↔ IsOperatorMF (SymmetricDouble G Γ) :=
  ⟨isOperatorMF_symmetricDouble_of_isOperatorMF_freeLampFlip G Γ,
    isOperatorMF_freeLampFlip_of_isOperatorMF_symmetricDouble G Γ⟩

theorem isSofic_freeLampFlip_of_isSofic_symmetricDouble (G : Type) [Group G]
    (Γ : Subgroup G) (h : IsSofic (SymmetricDouble G Γ)) :
    IsSofic (FreeLamp G Γ FlipC2) :=
  isSofic_freeLamp_of_isSofic_iterated G Γ FlipC2
    ((isSofic_mulEquiv_iff (symmetricDoubleEquivIteratedFlip G Γ)).mp h)

theorem isSofic_symmetricDouble_of_isSofic_freeLampFlip (G : Type) [Group G]
    (Γ : Subgroup G) (h : IsSofic (FreeLamp G Γ FlipC2)) :
    IsSofic (SymmetricDouble G Γ) :=
  (isSofic_mulEquiv_iff (symmetricDoubleEquivIteratedFlip G Γ)).mpr
    (isSofic_iterated_of_isSofic_freeLamp G Γ FlipC2 h)

/-- Soficity cannot tell the symmetric double from its `C₂` free-lamp amalgam
either.  The forward direction is `Sofic/DoubleSoficTransfer`'s, reproved here
through the covering; the converse is new. -/
theorem isSofic_freeLampFlip_iff_isSofic_symmetricDouble (G : Type) [Group G]
    (Γ : Subgroup G) :
    IsSofic (FreeLamp G Γ FlipC2) ↔ IsSofic (SymmetricDouble G Γ) :=
  ⟨isSofic_symmetricDouble_of_isSofic_freeLampFlip G Γ,
    isSofic_freeLampFlip_of_isSofic_symmetricDouble G Γ⟩

/-- The covering identity at the order-two lamp, in the shape the endpoint
consumes: the kernel of the retraction `G *_Γ (Γ × C₂) → C₂` is the symmetric
double. -/
theorem lampKernelFlip_equiv_symmetricDouble (G : Type) [Group G]
    (Γ : Subgroup G) :
    Nonempty (SymmetricDouble G Γ ≃* ↥(lampKernel G Γ FlipC2)) :=
  ⟨(symmetricDoubleEquivIteratedFlip G Γ).trans
    (iteratedEquivLampKernel G Γ FlipC2)⟩

end GroupApproximation
