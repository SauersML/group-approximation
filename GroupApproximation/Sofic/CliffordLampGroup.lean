import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Finsupp.Basic
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel

/-!
# The presented Clifford lamp group and its central sign

For an index type `X`, the Clifford lamp group is presented by an involution
`lamp x` for every `x : X` and one extra involution `sign`, subject to:
`sign` commutes with every lamp, and distinct lamps commute *up to* `sign`.
Thus `⁅lamp x, lamp y⁆ = sign` whenever `x ≠ y` — one anticommuting pair for
every distinct index pair.

Two facts are proved without ever claiming injectivity for the presentation:

* `sign_ne_one`: the sign survives in the presented group.  The witness is a
  homomorphism onto an explicit finite-support model:
  `ZMod 2 × (X →₀ ZMod 2)` with multiplication twisted by the
  strictly-ordered crossing form of a linear order on `X` (any linear order;
  one always exists by the well-ordering theorem).

* `permHom : Equiv.Perm X →* MulAut (CliffordLamp X)`: every permutation of
  `X` acts on the presented group fixing `sign` and permuting the lamps —
  the relator set is permutation invariant.

No faithfulness claim for the model map is made or needed: the downstream
marked-word argument consumes only `sign_ne_one`, the relations, and the
action.
-/

namespace GroupApproximation
namespace CliffordLamp

open scoped commutatorElement

universe u

variable (X : Type u)

/-! ## The presentation -/

/-- Free generators: `Sum.inl ()` is the sign, `Sum.inr x` the lamp at `x`. -/
abbrev Generator := (Unit ⊕ X)

/-- The four Clifford lamp relator families. -/
inductive IsRelator : FreeGroup (Generator X) → Prop
  | sign_sq : IsRelator (FreeGroup.of (Sum.inl ()) ^ 2)
  | lamp_sq (x : X) : IsRelator (FreeGroup.of (Sum.inr x) ^ 2)
  | sign_comm (x : X) :
      IsRelator ⁅(FreeGroup.of (Sum.inl ()) : FreeGroup (Generator X)),
        FreeGroup.of (Sum.inr x)⁆
  | braiding {x y : X} (h : x ≠ y) :
      IsRelator (⁅(FreeGroup.of (Sum.inr x) : FreeGroup (Generator X)),
          FreeGroup.of (Sum.inr y)⁆ *
        (FreeGroup.of (Sum.inl ()))⁻¹)

/-- The Clifford lamp relators as a set. -/
def relators : Set (FreeGroup (Generator X)) := {w | IsRelator X w}

/- The presented Clifford lamp group. -/
set_option linter.dupNamespace false in
abbrev CliffordLamp := PresentedGroup (relators X)

/-- The central sign. -/
def sign : CliffordLamp X := PresentedGroup.of (Sum.inl ())

/-- The lamp generator at `x`. -/
def lamp (x : X) : CliffordLamp X := PresentedGroup.of (Sum.inr x)

/-! ## Relations holding in the group -/

theorem sign_sq : sign X ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (IsRelator.sign_sq (X := X))
  rw [map_pow] at h
  exact h

theorem lamp_sq (x : X) : lamp X x ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (IsRelator.lamp_sq (X := X) x)
  rw [map_pow] at h
  exact h

theorem sign_commute_lamp (x : X) : Commute (sign X) (lamp X x) := by
  have h := PresentedGroup.one_of_mem (IsRelator.sign_comm (X := X) x)
  rw [map_commutatorElement] at h
  exact commutatorElement_eq_one_iff_commute.mp h

/-- The braiding relation: distinct lamps commute exactly up to the sign. -/
theorem commutator_lamp_lamp {x y : X} (h : x ≠ y) :
    ⁅lamp X x, lamp X y⁆ = sign X := by
  have h1 := PresentedGroup.one_of_mem (IsRelator.braiding (X := X) h)
  rw [map_mul, map_inv, map_commutatorElement] at h1
  have h2 : ⁅lamp X x, lamp X y⁆ * (sign X)⁻¹ = 1 := h1
  calc ⁅lamp X x, lamp X y⁆
      = ⁅lamp X x, lamp X y⁆ * (sign X)⁻¹ * sign X := by group
    _ = 1 * sign X := by rw [h2]
    _ = sign X := one_mul _

/-- **Derived Clifford phase.**  Commuting one lamp with the product of it
and a distinct lamp gives the same central sign.  This is the algebraic
identity used by the Kun--Thom phase lock: if the first commutator becomes
`lamp x * lamp y`, then one more commutator with `lamp x` is exactly `sign`.
-/
theorem commutator_lamp_lamp_mul_lamp {x y : X} (h : x ≠ y) :
    ⁅lamp X x, lamp X x * lamp X y⁆ = sign X := by
  have hxx : lamp X x * lamp X x = 1 := by
    simpa [pow_two] using lamp_sq X x
  have hxinv : (lamp X x)⁻¹ = lamp X x :=
    inv_eq_of_mul_eq_one_left hxx
  calc
    ⁅lamp X x, lamp X x * lamp X y⁆ = ⁅lamp X y, lamp X x⁆ := by
      simp only [commutatorElement_def, mul_inv_rev, hxinv]
      rw [← mul_assoc (lamp X x) (lamp X x) (lamp X y), hxx, one_mul]
      simp only [mul_assoc]
    _ = sign X := commutator_lamp_lamp X h.symm

/-- The sign is central. -/
theorem sign_commute (g : CliffordLamp X) : Commute (sign X) g := by
  have hmem : g ∈ Subgroup.centralizer {sign X} := by
    apply PresentedGroup.generated_by (relators X)
      (Subgroup.centralizer {sign X}) (fun j => ?_) g
    rw [Subgroup.mem_centralizer_singleton_iff]
    match j with
    | Sum.inl () => rfl
    | Sum.inr x => exact (sign_commute_lamp X x).eq.symm
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  exact Commute.symm hmem

/-- The sign together with all lamp generators generates the presented
Clifford lamp group.  This is the elimination principle used when proving
surjectivity of the manuscript's affine--Clifford witness map. -/
theorem mem_subgroup_of_sign_mem_of_lamp_mem
    (H : Subgroup (CliffordLamp X))
    (hsign : sign X ∈ H) (hlamp : ∀ x, lamp X x ∈ H)
    (g : CliffordLamp X) : g ∈ H := by
  apply PresentedGroup.generated_by (relators X) H
  intro j
  cases j with
  | inl u => cases u; exact hsign
  | inr x => exact hlamp x

/-! ## The signed finite-support model

The group law on the carrier `ZMod 2 × (X →₀ ZMod 2)` (a one-field structure
to avoid the product instance) is

`(ε, f) * (δ, g) = (ε + δ + crossing f g, f + g)`,

where `crossing f g` counts, mod `2`, the pairs `y < x` with `x` in the
support of `f` and `y` in the support of `g`.  Associativity is biadditivity
of the crossing form; every element is its own inverse up to a sign
adjustment because the coefficients have characteristic two. -/

section Model

variable [LinearOrder X]
noncomputable section SignedComputations

/-- The strictly-ordered crossing form. -/
def crossing (f g : X →₀ ZMod 2) : ZMod 2 :=
  f.sum fun x fx => g.sum fun y gy => if y < x then fx * gy else 0

theorem crossing_add_left (f₁ f₂ g : X →₀ ZMod 2) :
    crossing X (f₁ + f₂) g = crossing X f₁ g + crossing X f₂ g := by
  unfold crossing
  apply Finsupp.sum_add_index'
  · intro x
    simp
  · intro x b₁ b₂
    rw [← Finsupp.sum_add]
    congr 1
    ext y gy
    by_cases hxy : y < x <;> simp [hxy, add_mul]

theorem crossing_add_right (f g₁ g₂ : X →₀ ZMod 2) :
    crossing X f (g₁ + g₂) = crossing X f g₁ + crossing X f g₂ := by
  unfold crossing
  rw [← Finsupp.sum_add]
  congr 1
  ext x fx
  apply Finsupp.sum_add_index'
  · intro y
    simp
  · intro y b₁ b₂
    by_cases hxy : y < x <;> simp [hxy, mul_add]

theorem crossing_zero_left (g : X →₀ ZMod 2) : crossing X 0 g = 0 := by
  simp [crossing]

theorem crossing_zero_right (f : X →₀ ZMod 2) : crossing X f 0 = 0 := by
  simp [crossing]

theorem crossing_single_single (x y : X) (a b : ZMod 2) :
    crossing X (Finsupp.single x a) (Finsupp.single y b) =
      if y < x then a * b else 0 := by
  unfold crossing
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  · simp
  · rw [Finsupp.sum_single_index] <;> simp

/-- The self-crossing of a singleton vanishes: no strict pair below itself. -/
theorem crossing_single_self (x : X) (a b : ZMod 2) :
    crossing X (Finsupp.single x a) (Finsupp.single x b) = 0 := by
  rw [crossing_single_single]
  simp

/-- Exactly one of the two orders of a distinct pair crosses. -/
theorem crossing_single_add_swap {x y : X} (h : x ≠ y) :
    crossing X (Finsupp.single x (1 : ZMod 2)) (Finsupp.single y 1) +
      crossing X (Finsupp.single y 1) (Finsupp.single x 1) = 1 := by
  rw [crossing_single_single, crossing_single_single]
  rcases lt_or_gt_of_ne h with hxy | hyx
  · rw [if_neg (by exact fun hc => (asymm hxy hc)),
      if_pos hxy]
    exact zero_add 1
  · rw [if_pos hyx, if_neg (by exact fun hc => (asymm hyx hc))]
    norm_num

/-- The signed finite-support model carrier. -/
@[ext] structure SignedModel where
  /-- The central sign coordinate. -/
  signPart : ZMod 2
  /-- The lamp configuration. -/
  config : X →₀ ZMod 2

instance : One (SignedModel X) := ⟨⟨0, 0⟩⟩
instance : Mul (SignedModel X) :=
  ⟨fun p q => ⟨p.signPart + q.signPart + crossing X p.config q.config,
    p.config + q.config⟩⟩
instance : Inv (SignedModel X) :=
  ⟨fun p => ⟨p.signPart + crossing X p.config p.config, p.config⟩⟩

@[simp] theorem mul_def (p q : SignedModel X) :
    p * q = ⟨p.signPart + q.signPart + crossing X p.config q.config,
      p.config + q.config⟩ := rfl

omit [LinearOrder X] in
@[simp] theorem one_def : (1 : SignedModel X) = ⟨0, 0⟩ := rfl

@[simp] theorem inv_def (p : SignedModel X) :
    p⁻¹ = ⟨p.signPart + crossing X p.config p.config, p.config⟩ := rfl

instance : Group (SignedModel X) where
  mul_assoc p q r := by
    apply SignedModel.ext
    · show p.signPart + q.signPart + crossing X p.config q.config +
        r.signPart + crossing X (p.config + q.config) r.config =
        p.signPart + (q.signPart + r.signPart +
          crossing X q.config r.config) +
          crossing X p.config (q.config + r.config)
      rw [crossing_add_left, crossing_add_right]
      abel
    · show p.config + q.config + r.config =
        p.config + (q.config + r.config)
      rw [add_assoc]
  one_mul p := by
    apply SignedModel.ext
    · show 0 + p.signPart + crossing X 0 p.config = p.signPart
      rw [crossing_zero_left, zero_add, add_zero]
    · show 0 + p.config = p.config
      rw [zero_add]
  mul_one p := by
    apply SignedModel.ext
    · show p.signPart + 0 + crossing X p.config 0 = p.signPart
      rw [crossing_zero_right, add_zero, add_zero]
    · show p.config + 0 = p.config
      rw [add_zero]
  inv_mul_cancel p := by
    apply SignedModel.ext
    · show p.signPart + crossing X p.config p.config + p.signPart +
        crossing X p.config p.config = 0
      calc p.signPart + crossing X p.config p.config + p.signPart +
            crossing X p.config p.config
          = (p.signPart + p.signPart) + (crossing X p.config p.config +
              crossing X p.config p.config) := by ring
        _ = 0 := by
            rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    · show p.config + p.config = 0
      ext x
      exact CharTwo.add_self_eq_zero _

/-- The model sign. -/
def modelSign : SignedModel X := ⟨1, 0⟩

/-- The model lamp at `x`. -/
def modelLamp (x : X) : SignedModel X := ⟨0, Finsupp.single x 1⟩

theorem modelSign_commute (p : SignedModel X) :
    Commute (modelSign X) p := by
  show modelSign X * p = p * modelSign X
  rw [mul_def, mul_def]
  apply SignedModel.ext
  · show 1 + p.signPart + crossing X 0 p.config =
      p.signPart + 1 + crossing X p.config 0
    rw [crossing_zero_left, crossing_zero_right, add_comm (1 : ZMod 2)]
  · show 0 + p.config = p.config + 0
    rw [zero_add, add_zero]

theorem modelSign_sq : modelSign X ^ 2 = 1 := by
  rw [sq, mul_def]
  apply SignedModel.ext
  · show 1 + 1 + crossing X 0 0 = 0
    rw [crossing_zero_left, add_zero]
    decide
  · show (0 : X →₀ ZMod 2) + 0 = 0
    rw [add_zero]

theorem modelLamp_sq (x : X) : modelLamp X x ^ 2 = 1 := by
  rw [sq, mul_def]
  apply SignedModel.ext
  · show 0 + 0 + crossing X (Finsupp.single x 1) (Finsupp.single x 1) = 0
    rw [crossing_single_self, add_zero, add_zero]
  · show Finsupp.single x 1 + Finsupp.single x 1 = 0
    rw [← Finsupp.single_add]
    rw [show (1 : ZMod 2) + 1 = 0 by decide, Finsupp.single_zero]

theorem modelLamp_inv (x : X) : (modelLamp X x)⁻¹ = modelLamp X x := by
  rw [inv_def]
  apply SignedModel.ext
  · show 0 + crossing X (Finsupp.single x 1) (Finsupp.single x 1) = 0
    rw [crossing_single_self, add_zero]
  · rfl

/-- The commutator of distinct model lamps is the model sign. -/
theorem modelLamp_commutator {x y : X} (h : x ≠ y) :
    ⁅modelLamp X x, modelLamp X y⁆ = modelSign X := by
  rw [commutatorElement_def, modelLamp_inv, modelLamp_inv]
  have hconfig : Finsupp.single x (1 : ZMod 2) + Finsupp.single y 1 +
      Finsupp.single x 1 = Finsupp.single y 1 := by
    calc Finsupp.single x (1 : ZMod 2) + Finsupp.single y 1 +
          Finsupp.single x 1
        = Finsupp.single x 1 + Finsupp.single x 1 + Finsupp.single y 1 := by
          abel
      _ = Finsupp.single y 1 := by
          rw [← Finsupp.single_add,
            show (1 : ZMod 2) + 1 = 0 by decide, Finsupp.single_zero,
            zero_add]
  rw [mul_def, mul_def, mul_def]
  apply SignedModel.ext
  · show 0 + 0 + crossing X (Finsupp.single x 1) (Finsupp.single y 1) + 0 +
      crossing X (Finsupp.single x 1 + Finsupp.single y 1)
        (Finsupp.single x 1) + 0 +
      crossing X (Finsupp.single x 1 + Finsupp.single y 1 +
        Finsupp.single x 1) (Finsupp.single y 1) = 1
    rw [hconfig, crossing_single_self, crossing_add_left,
      crossing_single_self, zero_add, add_zero, add_zero, zero_add, add_zero]
    simpa only [zero_add] using crossing_single_add_swap X h
  · show Finsupp.single x (1 : ZMod 2) + Finsupp.single y 1 +
      Finsupp.single x 1 + Finsupp.single y 1 = 0
    rw [hconfig, ← Finsupp.single_add,
      show (1 : ZMod 2) + 1 = 0 by decide, Finsupp.single_zero]

/-- Generator images in the signed model. -/
def modelGenerator : Generator X → SignedModel X :=
  Sum.elim (fun _ => modelSign X) (fun x => modelLamp X x)

theorem modelGenerator_kills :
    ∀ w ∈ relators X, FreeGroup.lift (modelGenerator X) w = 1 := by
  intro w hw
  change IsRelator X w at hw
  cases hw with
  | sign_sq =>
      rw [map_pow, FreeGroup.lift_apply_of]
      exact modelSign_sq X
  | lamp_sq x =>
      rw [map_pow, FreeGroup.lift_apply_of]
      exact modelLamp_sq X x
  | sign_comm x =>
      rw [map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
      exact (modelSign_commute X (modelLamp X x)).commutator_eq
  | @braiding x y h =>
      rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      show ⁅modelLamp X x, modelLamp X y⁆ * (modelSign X)⁻¹ = 1
      rw [modelLamp_commutator X h]
      exact mul_inv_cancel _

/-- The presentation homomorphism onto the signed model. -/
def toModel : CliffordLamp X →* SignedModel X :=
  PresentedGroup.toGroup (modelGenerator_kills X)

@[simp] theorem toModel_sign : toModel X (sign X) = modelSign X :=
  PresentedGroup.toGroup.of _

@[simp] theorem toModel_lamp (x : X) :
    toModel X (lamp X x) = modelLamp X x :=
  PresentedGroup.toGroup.of _

/-- The sign survives the presentation: the model separates it from `1`. -/
theorem sign_ne_one_of_linearOrder : sign X ≠ 1 := by
  intro hsign
  have h1 : toModel X (sign X) = 1 := by rw [hsign, map_one]
  rw [toModel_sign] at h1
  have h2 : (1 : ZMod 2) = 0 := congrArg SignedModel.signPart h1
  exact absurd h2 (by decide)

end SignedComputations

end Model

/-- **The sign is nontrivial**, for every index type: the crossing-form
model runs over an arbitrary linear order on `X`, and one always exists by
the well-ordering theorem. -/
theorem sign_ne_one : sign X ≠ 1 := by
  letI : LinearOrder X := IsWellOrder.linearOrder WellOrderingRel
  exact sign_ne_one_of_linearOrder X

/-! ## The permutation action -/

/-- Generator images under a permutation of the index set. -/
def permGenerator (e : Equiv.Perm X) : Generator X → CliffordLamp X :=
  Sum.elim (fun _ => sign X) (fun x => lamp X (e x))

theorem permGenerator_kills (e : Equiv.Perm X) :
    ∀ w ∈ relators X, FreeGroup.lift (permGenerator X e) w = 1 := by
  intro w hw
  change IsRelator X w at hw
  cases hw with
  | sign_sq =>
      rw [map_pow, FreeGroup.lift_apply_of]
      exact sign_sq X
  | lamp_sq x =>
      rw [map_pow, FreeGroup.lift_apply_of]
      exact lamp_sq X (e x)
  | sign_comm x =>
      rw [map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
      exact (sign_commute_lamp X (e x)).commutator_eq
  | @braiding x y h =>
      rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      show ⁅lamp X (e x), lamp X (e y)⁆ * (sign X)⁻¹ = 1
      rw [commutator_lamp_lamp X (fun hc => h (e.injective hc))]
      exact mul_inv_cancel _

/-- The endomorphism of the lamp group induced by a permutation. -/
def permMap (e : Equiv.Perm X) : CliffordLamp X →* CliffordLamp X :=
  PresentedGroup.toGroup (permGenerator_kills X e)

@[simp] theorem permMap_sign (e : Equiv.Perm X) :
    permMap X e (sign X) = sign X :=
  PresentedGroup.toGroup.of _

@[simp] theorem permMap_lamp (e : Equiv.Perm X) (x : X) :
    permMap X e (lamp X x) = lamp X (e x) :=
  PresentedGroup.toGroup.of _

theorem permMap_comp_permMap (e₁ e₂ : Equiv.Perm X) (g : CliffordLamp X) :
    permMap X e₁ (permMap X e₂ g) = permMap X (e₁ * e₂) g := by
  have h : (permMap X e₁).comp (permMap X e₂) = permMap X (e₁ * e₂) := by
    apply PresentedGroup.ext
    intro j
    match j with
    | Sum.inl () =>
        show permMap X e₁ (permMap X e₂ (sign X)) =
          permMap X (e₁ * e₂) (sign X)
        rw [permMap_sign, permMap_sign, permMap_sign]
    | Sum.inr x =>
        show permMap X e₁ (permMap X e₂ (lamp X x)) =
          permMap X (e₁ * e₂) (lamp X x)
        rw [permMap_lamp, permMap_lamp, permMap_lamp]
        rfl
  exact DFunLike.congr_fun h g

theorem permMap_one_apply (g : CliffordLamp X) : permMap X 1 g = g := by
  have h : permMap X 1 = MonoidHom.id (CliffordLamp X) := by
    apply PresentedGroup.ext
    intro j
    match j with
    | Sum.inl () =>
        show permMap X 1 (sign X) = sign X
        rw [permMap_sign]
    | Sum.inr x =>
        show permMap X 1 (lamp X x) = lamp X x
        rw [permMap_lamp]
        rfl
  rw [h]
  rfl

/-- The automorphism of the lamp group induced by a permutation. -/
def permAut (e : Equiv.Perm X) : MulAut (CliffordLamp X) :=
  MonoidHom.toMulEquiv (permMap X e) (permMap X e⁻¹)
    (by
      apply PresentedGroup.ext
      intro j
      match j with
      | Sum.inl () =>
          show permMap X e⁻¹ (permMap X e (sign X)) = sign X
          rw [permMap_sign, permMap_sign]
      | Sum.inr x =>
          show permMap X e⁻¹ (permMap X e (lamp X x)) = lamp X x
          rw [permMap_lamp, permMap_lamp]
          simp)
    (by
      apply PresentedGroup.ext
      intro j
      match j with
      | Sum.inl () =>
          show permMap X e (permMap X e⁻¹ (sign X)) = sign X
          rw [permMap_sign, permMap_sign]
      | Sum.inr x =>
          show permMap X e (permMap X e⁻¹ (lamp X x)) = lamp X x
          rw [permMap_lamp, permMap_lamp]
          simp)

@[simp] theorem permAut_apply (e : Equiv.Perm X) (g : CliffordLamp X) :
    permAut X e g = permMap X e g := rfl

/-- The permutation action on the presented Clifford lamp group. -/
def permHom : Equiv.Perm X →* MulAut (CliffordLamp X) where
  toFun := permAut X
  map_one' := by
    apply MulEquiv.ext
    intro g
    rw [permAut_apply, permMap_one_apply]
    rfl
  map_mul' e₁ e₂ := by
    apply MulEquiv.ext
    intro g
    rw [permAut_apply]
    show permMap X (e₁ * e₂) g = (permAut X e₁ * permAut X e₂) g
    rw [MulAut.mul_apply, permAut_apply, permAut_apply,
      permMap_comp_permMap]

@[simp] theorem permHom_apply_sign (e : Equiv.Perm X) :
    permHom X e (sign X) = sign X := by
  show permAut X e (sign X) = sign X
  rw [permAut_apply, permMap_sign]

@[simp] theorem permHom_apply_lamp (e : Equiv.Perm X) (x : X) :
    permHom X e (lamp X x) = lamp X (e x) := by
  show permAut X e (lamp X x) = lamp X (e x)
  rw [permAut_apply, permMap_lamp]

/-! ## Countability -/

instance freeGroupCountable {β : Type u} [Countable β] :
    Countable (FreeGroup β) := by
  have hsurj : Function.Surjective (FreeGroup.mk : List (β × Bool) → _) := by
    intro g
    obtain ⟨L, hL⟩ := Quot.exists_rep g
    exact ⟨L, by rw [← FreeGroup.quot_mk_eq_mk, hL]⟩
  exact hsurj.countable

instance [Countable X] : Countable (CliffordLamp X) :=
  (PresentedGroup.mk_surjective (relators X)).countable

end CliffordLamp
end GroupApproximation
