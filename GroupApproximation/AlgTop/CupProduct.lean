import GroupApproximation.AlgTop.SingularCohomology

/-!
# The cup product on `H^*(X; R)`

This file descends the Alexander–Whitney cochain cup product `cochainCup` to a
cohomology-level product

```text
cup : Hᵖ(X; R) → H^q(X; R) → H^{p+q}(X; R)
```

for an **arbitrary** commutative coefficient ring `R`, using the signed Leibniz
identity `aw_cochain_leibniz` of `CochainLeibniz.lean`. The vendored HamSandwich
development performs this descent only over `ZMod 2`, where the Koszul signs are
invisible; the sign bookkeeping is what is new here.

## The one place the signs actually bite

Descending a bilinear cochain operation to cohomology needs three facts: the cup
of two cocycles is a cocycle, a coboundary cupped with a cocycle is a coboundary,
and a cocycle cupped with a coboundary is a coboundary. The third is where the
sign appears: `(-1)^p (φ ⌣ δβ) = δ(φ ⌣ β)`. Since `(-1)^p` is a unit with
`((-1)^p)^2 = 1`, this still exhibits `φ ⌣ δβ` as the coboundary
`δ((-1)^p • (φ ⌣ β))`, so the descent goes through unchanged — see
`cocycleClass_cup_coboundary_right_zero`.

## Main definitions

* `cup a b` — the cup product, with notation `a ⌣ b`.
* `one R X` — the unit class `1 ∈ H⁰(X; R)`.

## Main results

* `cup_mk` — the computation rule: the cup of two cocycle classes is the class of
  their cochain cup.
* `cup_add_left`, `cup_add_right`, `cup_smul_left`, `cup_smul_right` —
  `R`-bilinearity.
* `cup_one` — right unitality (no degree cast: `p + 0` is `p`).
* `cohPullback_cup` — naturality `f^*(a ⌣ b) = f^* a ⌣ f^* b`.

Strict associativity and left unitality need the Alexander–Whitney face
composition calculus in `SimplexCategory` and live in `CupAssoc.lean`.
Graded commutativity is **not** proved here or there: the Alexander–Whitney
diagonal is not cocommutative on the nose and the identity requires the
Eilenberg–Zilber chain homotopy between `Δ` and `T ∘ Δ`.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.AlgTop

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable (R : Type) [CommRing R]

/-! ## 1. The cup product as a cochain-level module morphism in each variable -/

/-- Cup with a fixed cochain on the right, `φ ↦ φ ⌣ ψ`, as a `ModuleCat`
morphism `C^p ⟶ C^{p+q}`. -/
def cupRightMor (X : TopCat.{0}) (p q : ℕ) (ψ : singularCochainGroup R X q) :
    (cochainCx R X).X p ⟶ (cochainCx R X).X (p + q) :=
  ModuleCat.ofHom
    { toFun := fun φ => cochainCup p q φ ψ
      map_add' := fun φ φ' => cochainCup_add_left p q φ φ' ψ
      map_smul' := fun s φ => cochainCup_smul_left p q s φ ψ }

@[simp] theorem cupRightMor_hom (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup R X q) (φ : (cochainCx R X).X p) :
    (cupRightMor R X p q ψ).hom φ = cochainCup p q φ ψ := rfl

/-- Cup with a fixed cochain on the left, `ψ ↦ φ ⌣ ψ`, as a `ModuleCat`
morphism `C^q ⟶ C^{p+q}`. -/
def cupLeftFixedMor (X : TopCat.{0}) (p q : ℕ) (φ : singularCochainGroup R X p) :
    (cochainCx R X).X q ⟶ (cochainCx R X).X (p + q) :=
  ModuleCat.ofHom
    { toFun := fun ψ => cochainCup p q φ ψ
      map_add' := fun ψ ψ' => cochainCup_add_right p q φ ψ ψ'
      map_smul' := fun s ψ => cochainCup_smul_right p q s φ ψ }

@[simp] theorem cupLeftFixedMor_hom (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup R X p) (ψ : (cochainCx R X).X q) :
    (cupLeftFixedMor R X p q φ).hom ψ = cochainCup p q φ ψ := rfl

/-- Cupping a cycle with a fixed cocycle on the right lands in cocycles. -/
theorem cupRight_cocycle_cond (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup R X q) (hψ : IsCocycle R X q ψ) :
    ((cochainCx R X).iCycles p ≫ cupRightMor R X p q ψ)
        ≫ (cochainCx R X).d (p + q) (p + q + 1) = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro c
  show cochainCoboundary R X (p + q)
      (cochainCup p q (((cochainCx R X).iCycles p).hom c) ψ) = 0
  exact cochainCup_cocycle (cochainCoboundary_iCycles R X p c) hψ

/-- Cupping a cycle with a fixed cocycle on the left lands in cocycles. -/
theorem cupLeftFixed_cocycle_cond (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ) :
    ((cochainCx R X).iCycles q ≫ cupLeftFixedMor R X p q φ)
        ≫ (cochainCx R X).d (p + q) (p + q + 1) = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro c
  show cochainCoboundary R X (p + q)
      (cochainCup p q φ (((cochainCx R X).iCycles q).hom c)) = 0
  exact cochainCup_cocycle hφ (cochainCoboundary_iCycles R X q c)

/-- Cup with a fixed cocycle on the right, as a map `cycles p ⟶ H^{p+q}`. -/
def cupLeftMor (X : TopCat.{0}) (p q : ℕ) (ψ : singularCochainGroup R X q)
    (hψ : IsCocycle R X q ψ) :
    (cochainCx R X).cycles p ⟶ cohomology R X (p + q) :=
  (cochainCx R X).liftCycles ((cochainCx R X).iCycles p ≫ cupRightMor R X p q ψ) (p + q + 1)
      (by simp [ComplexShape.next]) (cupRight_cocycle_cond R X p q ψ hψ)
    ≫ (cochainCx R X).homologyπ (p + q)

/-- Cup with a fixed cocycle on the left, as a map `cycles q ⟶ H^{p+q}`. -/
def cupRightMor' (X : TopCat.{0}) (p q : ℕ) (φ : singularCochainGroup R X p)
    (hφ : IsCocycle R X p φ) :
    (cochainCx R X).cycles q ⟶ cohomology R X (p + q) :=
  (cochainCx R X).liftCycles ((cochainCx R X).iCycles q ≫ cupLeftFixedMor R X p q φ) (p + q + 1)
      (by simp [ComplexShape.next]) (cupLeftFixed_cocycle_cond R X p q φ hφ)
    ≫ (cochainCx R X).homologyπ (p + q)

theorem cupLeftMor_cyclesMk (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup R X q) (hψ : IsCocycle R X q ψ)
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ) :
    (cupLeftMor R X p q ψ hψ).hom
        ((cochainCx R X).cyclesMk φ (p + 1) (by simp [ComplexShape.next]) hφ)
      = cocycleClass R X (p + q) (cochainCup p q φ ψ) (cochainCup_cocycle hφ hψ) := by
  unfold cupLeftMor cocycleClass
  simp only [ModuleCat.comp_apply]
  apply congrArg ((cochainCx R X).homologyπ (p + q)).hom
  apply (ModuleCat.mono_iff_injective ((cochainCx R X).iCycles (p + q))).1 inferInstance
  calc
    _ = ((cochainCx R X).iCycles p ≫ cupRightMor R X p q ψ).hom
          ((cochainCx R X).cyclesMk φ (p + 1) (by simp [ComplexShape.next]) hφ) :=
      ConcreteCategory.congr_hom
        ((cochainCx R X).liftCycles_i
          ((cochainCx R X).iCycles p ≫ cupRightMor R X p q ψ)
          (p + q + 1) (by simp [ComplexShape.next]) (cupRight_cocycle_cond R X p q ψ hψ)) _
    _ = cochainCup p q φ ψ := by
      rw [ModuleCat.comp_apply, cupRightMor_hom, iCycles_cyclesMk]
    _ = _ := ((cochainCx R X).i_cyclesMk _ _ _ _).symm

theorem cupRightMor'_cyclesMk (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ)
    (ψ : singularCochainGroup R X q) (hψ : IsCocycle R X q ψ) :
    (cupRightMor' R X p q φ hφ).hom
        ((cochainCx R X).cyclesMk ψ (q + 1) (by simp [ComplexShape.next]) hψ)
      = cocycleClass R X (p + q) (cochainCup p q φ ψ) (cochainCup_cocycle hφ hψ) := by
  unfold cupRightMor' cocycleClass
  simp only [ModuleCat.comp_apply]
  apply congrArg ((cochainCx R X).homologyπ (p + q)).hom
  apply (ModuleCat.mono_iff_injective ((cochainCx R X).iCycles (p + q))).1 inferInstance
  calc
    _ = ((cochainCx R X).iCycles q ≫ cupLeftFixedMor R X p q φ).hom
          ((cochainCx R X).cyclesMk ψ (q + 1) (by simp [ComplexShape.next]) hψ) :=
      ConcreteCategory.congr_hom
        ((cochainCx R X).liftCycles_i
          ((cochainCx R X).iCycles q ≫ cupLeftFixedMor R X p q φ)
          (p + q + 1) (by simp [ComplexShape.next]) (cupLeftFixed_cocycle_cond R X p q φ hφ)) _
    _ = cochainCup p q φ ψ := by
      rw [ModuleCat.comp_apply, cupLeftFixedMor_hom, iCycles_cyclesMk]
    _ = _ := ((cochainCx R X).i_cyclesMk _ _ _ _).symm

theorem cupLeftMor_apply (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup R X q) (hψ : IsCocycle R X q ψ)
    (c : (cochainCx R X).cycles p) :
    (cupLeftMor R X p q ψ hψ).hom c
      = cocycleClass R X (p + q) (cochainCup p q (((cochainCx R X).iCycles p).hom c) ψ)
          (cochainCup_cocycle (cochainCoboundary_iCycles R X p c) hψ) := by
  conv_lhs => rw [← cyclesMk_iCycles R X p c]
  exact cupLeftMor_cyclesMk R X p q ψ hψ (((cochainCx R X).iCycles p).hom c)
    (cochainCoboundary_iCycles R X p c)

theorem cupRightMor'_apply (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ)
    (c : (cochainCx R X).cycles q) :
    (cupRightMor' R X p q φ hφ).hom c
      = cocycleClass R X (p + q) (cochainCup p q φ (((cochainCx R X).iCycles q).hom c))
          (cochainCup_cocycle hφ (cochainCoboundary_iCycles R X q c)) := by
  conv_lhs => rw [← cyclesMk_iCycles R X q c]
  exact cupRightMor'_cyclesMk R X p q φ hφ (((cochainCx R X).iCycles q).hom c)
    (cochainCoboundary_iCycles R X q c)

/-! ## 2. Coboundaries cup to coboundaries

The left case is sign-free; the right case is where `(-1)^p` appears, and it is
absorbed by rewriting the coboundary `δ(φ ⌣ β)` as `δ((-1)^p • (φ ⌣ β))`. -/

/-- **A coboundary cupped with a cocycle has zero class.** -/
theorem cocycleClass_cup_coboundary_left_zero (X : TopCat.{0}) (m q : ℕ)
    (η : singularCochainGroup R X m) (ψ : singularCochainGroup R X q)
    (hψ : IsCocycle R X q ψ)
    (hcoc : IsCocycle R X (m + 1 + q)
      (cochainCup (m + 1) q (cochainCoboundary R X m η) ψ)) :
    cocycleClass R X (m + 1 + q)
        (cochainCup (m + 1) q (cochainCoboundary R X m η) ψ) hcoc = 0 := by
  have key : cochainCup (m + 1) q (cochainCoboundary R X m η) ψ
      = cochainCast (aw_degree_left_succ m q).symm
          (cochainCoboundary R X (m + q) (cochainCup m q η ψ)) := by
    rw [← cochainCup_coboundary_left η hψ, cochainCast_cast]
  refine cocycleClass_eq_zero_of_eq R X (m + 1 + q) key hcoc ?_ ?_
  · rw [← key]; exact hcoc
  · exact cocycleClass_cast_coboundary_zero R X (m + q) (m + 1 + q)
      (aw_degree_left_succ m q).symm (cochainCup m q η ψ) _

/-- **A cocycle cupped with a coboundary has zero class.** The Koszul sign
`(-1)^p` is absorbed into the primitive: `φ ⌣ δβ = δ((-1)^p • (φ ⌣ β))`. -/
theorem cocycleClass_cup_coboundary_right_zero (X : TopCat.{0}) (p m : ℕ)
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ)
    (β : singularCochainGroup R X m)
    (hcoc : IsCocycle R X (p + (m + 1))
      (cochainCup p (m + 1) φ (cochainCoboundary R X m β))) :
    cocycleClass R X (p + (m + 1))
        (cochainCup p (m + 1) φ (cochainCoboundary R X m β)) hcoc = 0 := by
  have key : cochainCup p (m + 1) φ (cochainCoboundary R X m β)
      = cochainCoboundary R X (p + m) (((-1 : R) ^ p) • cochainCup p m φ β) := by
    have h := cochainCup_coboundary_right (R := R) (X := X) (p := p) (m := m) β hφ
    rw [cochainCoboundary_smul, ← h, smul_smul, neg_one_pow_mul_self, one_smul]
  refine cocycleClass_eq_zero_of_eq R X (p + (m + 1)) key hcoc ?_ ?_
  · rw [← key]; exact hcoc
  · exact cocycleClass_coboundary_zero R X (p + m)
      (((-1 : R) ^ p) • cochainCup p m φ β) _

/-- The cup of an element in the image of a differential (left factor) with a
cocycle has zero class, for any source index. -/
theorem cocycleClass_cup_d_left_zero (X : TopCat.{0}) (q i p : ℕ)
    (η : (cochainCx R X).X i) (ψ : singularCochainGroup R X q) (hψ : IsCocycle R X q ψ)
    (hcoc : IsCocycle R X (p + q) (cochainCup p q (((cochainCx R X).d i p).hom η) ψ)) :
    cocycleClass R X (p + q) (cochainCup p q (((cochainCx R X).d i p).hom η) ψ) hcoc = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i + 1 = p := h
    exact cocycleClass_cup_coboundary_left_zero R X i q η ψ hψ hcoc
  · have hz : cochainCup p q (((cochainCx R X).d i p).hom η) ψ = 0 := by
      rw [(cochainCx R X).shape i p h]; simp
    exact cocycleClass_eq_zero_of_eq R X (p + q) hz hcoc (by simp)
      (cocycleClass_zero R X (p + q) (by simp))

/-- The cup of a cocycle with an element in the image of a differential (right
factor) has zero class, for any source index. -/
theorem cocycleClass_cup_d_right_zero (X : TopCat.{0}) (p i q : ℕ)
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ) (η : (cochainCx R X).X i)
    (hcoc : IsCocycle R X (p + q) (cochainCup p q φ (((cochainCx R X).d i q).hom η))) :
    cocycleClass R X (p + q) (cochainCup p q φ (((cochainCx R X).d i q).hom η)) hcoc = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel i q
  · obtain rfl : i + 1 = q := h
    exact cocycleClass_cup_coboundary_right_zero R X p i φ hφ η hcoc
  · have hz : cochainCup p q φ (((cochainCx R X).d i q).hom η) = 0 := by
      rw [(cochainCx R X).shape i q h]; simp
    exact cocycleClass_eq_zero_of_eq R X (p + q) hz hcoc (by simp)
      (cocycleClass_zero R X (p + q) (by simp))

/-- The cup-with-right-cocycle map kills coboundaries (cokernel condition). -/
theorem cupLeftMor_toCycles (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup R X q) (hψ : IsCocycle R X q ψ) :
    (cochainCx R X).toCycles ((ComplexShape.up ℕ).prev p) p ≫ cupLeftMor R X p q ψ hψ = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro η
  show (cupLeftMor R X p q ψ hψ).hom
      (((cochainCx R X).toCycles ((ComplexShape.up ℕ).prev p) p).hom η) = 0
  rw [cupLeftMor_apply]
  have heq : cochainCup p q (((cochainCx R X).iCycles p).hom
        (((cochainCx R X).toCycles ((ComplexShape.up ℕ).prev p) p).hom η)) ψ
      = cochainCup p q (((cochainCx R X).d ((ComplexShape.up ℕ).prev p) p).hom η) ψ := by
    rw [← ModuleCat.comp_apply, (cochainCx R X).toCycles_i]
  refine cocycleClass_eq_zero_of_eq R X (p + q) heq _ ?_ ?_
  · rw [← heq]
    exact cochainCup_cocycle (cochainCoboundary_iCycles R X p _) hψ
  · exact cocycleClass_cup_d_left_zero R X q ((ComplexShape.up ℕ).prev p) p η ψ hψ _

/-- The cup-with-left-cocycle map kills coboundaries (cokernel condition). -/
theorem cupRightMor'_toCycles (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ) :
    (cochainCx R X).toCycles ((ComplexShape.up ℕ).prev q) q ≫ cupRightMor' R X p q φ hφ = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro η
  show (cupRightMor' R X p q φ hφ).hom
      (((cochainCx R X).toCycles ((ComplexShape.up ℕ).prev q) q).hom η) = 0
  rw [cupRightMor'_apply]
  have heq : cochainCup p q φ (((cochainCx R X).iCycles q).hom
        (((cochainCx R X).toCycles ((ComplexShape.up ℕ).prev q) q).hom η))
      = cochainCup p q φ (((cochainCx R X).d ((ComplexShape.up ℕ).prev q) q).hom η) := by
    rw [← ModuleCat.comp_apply, (cochainCx R X).toCycles_i]
  refine cocycleClass_eq_zero_of_eq R X (p + q) heq _ ?_ ?_
  · rw [← heq]
    exact cochainCup_cocycle hφ (cochainCoboundary_iCycles R X q _)
  · exact cocycleClass_cup_d_right_zero R X p ((ComplexShape.up ℕ).prev q) q φ hφ η _

/-! ## 3. Descent to cohomology in each variable -/

/-- Cup with a fixed right cocycle, descended to `Hᵖ ⟶ H^{p+q}`. -/
def cupHomologyLeft (X : TopCat.{0}) (p q : ℕ) (ψ : singularCochainGroup R X q)
    (hψ : IsCocycle R X q ψ) : cohomology R X p ⟶ cohomology R X (p + q) :=
  ((cochainCx R X).homologyIsCokernel ((ComplexShape.up ℕ).prev p) p rfl).desc
    (CokernelCofork.ofπ (cupLeftMor R X p q ψ hψ) (cupLeftMor_toCycles R X p q ψ hψ))

/-- Cup with a fixed left cocycle, descended to `H^q ⟶ H^{p+q}`. -/
def cupHomologyRight (X : TopCat.{0}) (p q : ℕ) (φ : singularCochainGroup R X p)
    (hφ : IsCocycle R X p φ) : cohomology R X q ⟶ cohomology R X (p + q) :=
  ((cochainCx R X).homologyIsCokernel ((ComplexShape.up ℕ).prev q) q rfl).desc
    (CokernelCofork.ofπ (cupRightMor' R X p q φ hφ) (cupRightMor'_toCycles R X p q φ hφ))

theorem homologyπ_cupHomologyLeft (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup R X q) (hψ : IsCocycle R X q ψ) :
    (cochainCx R X).homologyπ p ≫ cupHomologyLeft R X p q ψ hψ = cupLeftMor R X p q ψ hψ :=
  ((cochainCx R X).homologyIsCokernel ((ComplexShape.up ℕ).prev p) p rfl).fac
    (CokernelCofork.ofπ (cupLeftMor R X p q ψ hψ) (cupLeftMor_toCycles R X p q ψ hψ))
    WalkingParallelPair.one

theorem homologyπ_cupHomologyRight (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ) :
    (cochainCx R X).homologyπ q ≫ cupHomologyRight R X p q φ hφ = cupRightMor' R X p q φ hφ :=
  ((cochainCx R X).homologyIsCokernel ((ComplexShape.up ℕ).prev q) q rfl).fac
    (CokernelCofork.ofπ (cupRightMor' R X p q φ hφ) (cupRightMor'_toCycles R X p q φ hφ))
    WalkingParallelPair.one

theorem cupHomologyLeft_apply (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup R X q) (hψ : IsCocycle R X q ψ)
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ) :
    (cupHomologyLeft R X p q ψ hψ).hom (cocycleClass R X p φ hφ)
      = cocycleClass R X (p + q) (cochainCup p q φ ψ) (cochainCup_cocycle hφ hψ) := by
  rw [cocycleClass,
    show (cupHomologyLeft R X p q ψ hψ).hom
          (((cochainCx R X).homologyπ p).hom
            ((cochainCx R X).cyclesMk φ (p + 1) (by simp [ComplexShape.next]) hφ))
        = ((cochainCx R X).homologyπ p ≫ cupHomologyLeft R X p q ψ hψ).hom
            ((cochainCx R X).cyclesMk φ (p + 1) (by simp [ComplexShape.next]) hφ) from rfl,
    homologyπ_cupHomologyLeft, cupLeftMor_cyclesMk]

theorem cupHomologyRight_apply (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ)
    (ψ : singularCochainGroup R X q) (hψ : IsCocycle R X q ψ) :
    (cupHomologyRight R X p q φ hφ).hom (cocycleClass R X q ψ hψ)
      = cocycleClass R X (p + q) (cochainCup p q φ ψ) (cochainCup_cocycle hφ hψ) := by
  rw [cocycleClass,
    show (cupHomologyRight R X p q φ hφ).hom
          (((cochainCx R X).homologyπ q).hom
            ((cochainCx R X).cyclesMk ψ (q + 1) (by simp [ComplexShape.next]) hψ))
        = ((cochainCx R X).homologyπ q ≫ cupHomologyRight R X p q φ hφ).hom
            ((cochainCx R X).cyclesMk ψ (q + 1) (by simp [ComplexShape.next]) hψ) from rfl,
    homologyπ_cupHomologyRight, cupRightMor'_cyclesMk]

/-! ## 4. The cup product -/

variable {R}

/-- The **cup product** `⌣ : Hᵖ(X; R) → H^q(X; R) → H^{p+q}(X; R)`. -/
def cup {X : TopCat.{0}} {p q : ℕ} (a : cohomology R X p) (b : cohomology R X q) :
    cohomology R X (p + q) :=
  (cupHomologyLeft R X p q (classRepr R X q b) (classRepr_isCocycle R X q b)).hom a

@[inherit_doc] infixl:70 " ⌣ " => cup

/-- **Computation rule.** The cup of the classes of two cocycles is the class of
their cochain cup. -/
theorem cup_mk {X : TopCat.{0}} {p q : ℕ}
    (φ : singularCochainGroup R X p) (hφ : IsCocycle R X p φ)
    (ψ : singularCochainGroup R X q) (hψ : IsCocycle R X q ψ) :
    cup (cocycleClass R X p φ hφ) (cocycleClass R X q ψ hψ)
      = cocycleClass R X (p + q) (cochainCup p q φ ψ) (cochainCup_cocycle hφ hψ) := by
  rw [cup, cupHomologyLeft_apply]
  have key := cupHomologyRight_apply R X p q φ hφ
    (classRepr R X q (cocycleClass R X q ψ hψ)) (classRepr_isCocycle R X q _)
  rw [cocycleClass_classRepr] at key
  have key2 := cupHomologyRight_apply R X p q φ hφ ψ hψ
  rw [← key, ← key2]

/-! ## 5. Bilinearity -/

theorem cup_add_left {X : TopCat.{0}} {p q : ℕ} (a a' : cohomology R X p)
    (b : cohomology R X q) : (a + a') ⌣ b = a ⌣ b + a' ⌣ b := by
  unfold cup
  exact map_add _ _ _

theorem cup_smul_left {X : TopCat.{0}} {p q : ℕ} (s : R) (a : cohomology R X p)
    (b : cohomology R X q) : (s • a) ⌣ b = s • (a ⌣ b) := by
  unfold cup
  exact map_smul _ _ _

theorem cup_add_right {X : TopCat.{0}} {p q : ℕ} (a : cohomology R X p)
    (b b' : cohomology R X q) : a ⌣ (b + b') = a ⌣ b + a ⌣ b' := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective R X p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective R X q b
  obtain ⟨ψ', hψ', rfl⟩ := cocycleClass_surjective R X q b'
  have hs : IsCocycle R X q (ψ + ψ') := by
    show cochainCoboundary R X q (ψ + ψ') = 0
    rw [cochainCoboundary_add, hψ, hψ', add_zero]
  have hsum : IsCocycle R X (p + q) (cochainCup p q φ ψ + cochainCup p q φ ψ') := by
    show cochainCoboundary R X (p + q) (cochainCup p q φ ψ + cochainCup p q φ ψ') = 0
    rw [cochainCoboundary_add, cochainCup_cocycle hφ hψ, cochainCup_cocycle hφ hψ', add_zero]
  rw [← cocycleClass_add R X q ψ ψ' hψ hψ' hs, cup_mk, cup_mk, cup_mk,
    ← cocycleClass_add R X (p + q) _ _ (cochainCup_cocycle hφ hψ)
      (cochainCup_cocycle hφ hψ') hsum]
  exact cocycleClass_congr R X (p + q) (cochainCup_add_right p q φ ψ ψ') _ _

theorem cup_smul_right {X : TopCat.{0}} {p q : ℕ} (s : R) (a : cohomology R X p)
    (b : cohomology R X q) : a ⌣ (s • b) = s • (a ⌣ b) := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective R X p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective R X q b
  have hs : IsCocycle R X q (s • ψ) := by
    show cochainCoboundary R X q (s • ψ) = 0
    rw [cochainCoboundary_smul, hψ, smul_zero]
  have hs2 : IsCocycle R X (p + q) (s • cochainCup p q φ ψ) := by
    show cochainCoboundary R X (p + q) (s • cochainCup p q φ ψ) = 0
    rw [cochainCoboundary_smul, cochainCup_cocycle hφ hψ, smul_zero]
  rw [← cocycleClass_smul R X q s ψ hψ hs, cup_mk, cup_mk,
    ← cocycleClass_smul R X (p + q) s _ (cochainCup_cocycle hφ hψ) hs2]
  exact cocycleClass_congr R X (p + q) (cochainCup_smul_right p q s φ ψ) _ _

@[simp] theorem zero_cup {X : TopCat.{0}} {p q : ℕ} (b : cohomology R X q) :
    (0 : cohomology R X p) ⌣ b = 0 := by
  unfold cup
  exact map_zero _

@[simp] theorem cup_zero {X : TopCat.{0}} {p q : ℕ} (a : cohomology R X p) :
    a ⌣ (0 : cohomology R X q) = 0 := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective R X p a
  rw [← cocycleClass_zero R X q (cochainCoboundary_zero R X q), cup_mk]
  exact cocycleClass_eq_zero_of_eq R X (p + q) (cochainCup_zero_right p q φ) _
    (cochainCoboundary_zero R X (p + q))
    (cocycleClass_zero R X (p + q) (cochainCoboundary_zero R X (p + q)))

/-! ## 6. The unit class -/

/-- The unit cochain is a cocycle: `δ1 = 0`, because every `1`-simplex has exactly
two boundary faces, with opposite signs. -/
theorem cochainCoboundary_cochainOne (X : TopCat.{0}) :
    IsCocycle R X 0 (cochainOne (R := R) (Z := X)) := by
  show cochainCoboundary R X 0 (cochainOne (R := R) (Z := X)) = 0
  apply cochain_ext
  intro σ
  rw [cochainCoboundary_eval, cochainEval_zero]
  rw [Fin.sum_univ_two]
  simp [cochainOne_eval]

/-- The **unit class** `1 ∈ H⁰(X; R)`. -/
def one (R : Type) [CommRing R] (X : TopCat.{0}) : cohomology R X 0 :=
  cocycleClass R X 0 (cochainOne (R := R) (Z := X)) (cochainCoboundary_cochainOne X)

/-- **Right unitality.** No degree cast appears: `p + 0` reduces to `p`. -/
@[simp] theorem cup_one {X : TopCat.{0}} {p : ℕ} (a : cohomology R X p) :
    a ⌣ one R X = a := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective R X p a
  rw [one, cup_mk]
  exact cocycleClass_congr R X (p + 0) (cochainCup_one p φ) _ hφ

/-! ## 7. Naturality -/

/-- **Naturality of the cup product.** `f^*(a ⌣ b) = f^* a ⌣ f^* b`. -/
theorem cohPullback_cup {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (a : cohomology R Y p) (b : cohomology R Y q) :
    (cohPullback R f (p + q)).hom (a ⌣ b)
      = (cohPullback R f p).hom a ⌣ (cohPullback R f q).hom b := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective R Y p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective R Y q b
  rw [cup_mk, cohPullback_cocycleClass, cohPullback_cocycleClass, cohPullback_cocycleClass,
    cup_mk]
  exact cocycleClass_congr R X (p + q) (cochainCup_naturality f p q φ ψ) _ _

/-- The pullback preserves the unit class. -/
@[simp] theorem cohPullback_one {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (cohPullback R f 0).hom (one R Y) = one R X := by
  rw [one, cohPullback_cocycleClass]
  refine cocycleClass_congr R X 0 ?_ _ _
  apply cochain_ext
  intro σ
  rw [cochainPullback_eval, cochainOne_eval, cochainOne_eval]

end

end GroupApproximation.AlgTop
