import GroupApproximation.Algebra.HNNRetraction
import GroupApproximation.Algebra.FreeProductOrder
import GroupApproximation.Algebra.HNNTrivialAssociated
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The variant Adian--Rabin tower

`Computability.RabinConstruction` records a variant of Rabin's construction
whose associated subgroups are all either cyclic on an element of infinite
order or free on a family that a retraction exhibits.  This file builds that
tower and proves the half the roadmap calls missing: **the base embeds**.

The tower over a group `Γ` with a distinguished element `w`:

1. `A = Γ * ℤ`, writing `s` for the generator of the `ℤ` factor.  For a chosen
   finite generating family `x` of `Γ`, put `sᵢ = s · xᵢ`.  Every `sᵢ` has
   infinite order, whatever the `xᵢ` do, because the retraction to `ℤ` does not
   see `Γ` (`HNNRetraction.zpow_inr_mul_inl_ne_one`).
2. `B = A * F`, `F` free of rank `n`.  Write `tᵢ` for its free generators.
   *This is the step that replaces Rabin's layer of `n` Baumslag--Solitar HNN
   extensions.*  All that layer was ever for was to produce a free subgroup for
   the next stage to act on, and a free factor produces one outright.
3. `K = HNN(B)` with stable letter `u` conjugating `⟨t₀,…,tₙ₋₁⟩` onto
   `⟨t₀s₀,…,tₙ₋₁sₙ₋₁⟩`.  Both are free on the displayed families, by the *same*
   witness: `killLeft` kills `A`, so it sends `tᵢ` and `tᵢsᵢ` alike to the `i`th
   free generator.  This is the step that does the killing: `u = 1` turns
   `u tᵢ u⁻¹ = tᵢsᵢ` into `sᵢ = 1` for every `i` at once.

The cascade that forces `u = 1` when `w = 1` continues with three cyclic HNN
layers and is not built here; what is built here is the part that carries the
embedding, and `base_injective` is the statement that `Γ` embeds in `K`.
-/

namespace GroupApproximation
namespace RabinVariantTower

open Monoid HNNRetraction

variable {Γ : Type} [Group Γ]

/-- Stage 1: `Γ * ℤ`, written as an HNN extension with trivial associated
subgroups.  That description is chosen deliberately: it is the one in which the
witness `⁅w, s⁆` can be shown to have infinite order, because with trivial
associated subgroups every word in the stable letter is Britton-reduced
(`HNNTrivialAssociated.commElt_pow_ne_one`). -/
abbrev Base (Γ : Type) [Group Γ] : Type :=
  HNNExtension Γ (⊥ : Subgroup Γ) (⊥ : Subgroup Γ) (MulEquiv.refl _)

/-- The free letter adjoined in stage 1. -/
def s : Base Γ := HNNExtension.t

/-- The base group, inside stage 1. -/
def baseOf : Γ →* Base Γ := HNNExtension.of

/-- `sᵢ = s · xᵢ`.  The change of generators: these have infinite order even
when the `xᵢ` do not, because the retraction killing the base sees only `s`. -/
def sgen (x : Γ) : Base Γ := s * baseOf x

theorem zpow_sgen_ne_one (x : Γ) {n : ℤ} (hn : n ≠ 0) : (sgen x) ^ n ≠ 1 :=
  zpow_t_mul_of_ne_one _ x hn

theorem baseOf_injective : Function.Injective (baseOf (Γ := Γ)) :=
  HNNExtension.of_injective _

/-- Stage 2: adjoin a free group of rank `n` as a free factor. -/
abbrev Mid (Γ : Type) [Group Γ] (n : ℕ) : Type :=
  Monoid.Coprod (Base Γ) (FreeGroup (Fin n))

/-- The `i`th free letter of stage 2. -/
def t {n : ℕ} (i : Fin n) : Mid Γ n :=
  Monoid.Coprod.inr (FreeGroup.of i)

/-- `Γ`, inside stage 2. -/
def midOfBase {n : ℕ} : Base Γ →* Mid Γ n := Monoid.Coprod.inl

theorem midOfBase_injective {n : ℕ} :
    Function.Injective (midOfBase (Γ := Γ) (n := n)) :=
  Monoid.Coprod.inl_injective

/-- The retraction of stage 2 onto its free factor. -/
def midRetract {n : ℕ} : Mid Γ n →* FreeGroup (Fin n) := killLeft

@[simp] theorem midRetract_t {n : ℕ} (i : Fin n) :
    midRetract (t (Γ := Γ) i) = FreeGroup.of i := by
  simp [midRetract, t]

@[simp] theorem midRetract_inl {n : ℕ} (g : Base Γ) :
    midRetract (midOfBase (n := n) g) = 1 := by
  simp [midRetract, midOfBase]

/-- The family the stable letter conjugates *onto*: `tᵢsᵢ`. -/
def ts {n : ℕ} (x : Fin n → Γ) (i : Fin n) : Mid Γ n :=
  t i * midOfBase (sgen (x i))

@[simp] theorem midRetract_ts {n : ℕ} (x : Fin n → Γ) (i : Fin n) :
    midRetract (ts x i) = FreeGroup.of i := by
  simp [ts]

/-! ## Both families are free, by the same retraction -/

theorem lift_t_injective {n : ℕ} :
    Function.Injective (FreeGroup.lift (t (Γ := Γ) (n := n))) :=
  freeGroupLift_injective midRetract _ (by simp)

theorem lift_ts_injective {n : ℕ} (x : Fin n → Γ) :
    Function.Injective (FreeGroup.lift (ts (Γ := Γ) x)) :=
  freeGroupLift_injective midRetract _ (by simp)

/-- The source subgroup of the stable letter: `⟨t₀,…,tₙ₋₁⟩`. -/
def srcSub (Γ : Type) [Group Γ] (n : ℕ) : Subgroup (Mid Γ n) :=
  (FreeGroup.lift (t (Γ := Γ) (n := n))).range

/-- The target subgroup: `⟨t₀s₀,…,tₙ₋₁sₙ₋₁⟩`. -/
def tgtSub {n : ℕ} (x : Fin n → Γ) : Subgroup (Mid Γ n) :=
  (FreeGroup.lift (ts (Γ := Γ) x)).range

/-- **The identification the stable letter implements.**  Both subgroups are
free on the displayed families, so the map `tᵢ ↦ tᵢsᵢ` is an isomorphism
between them. -/
noncomputable def stepEquiv {n : ℕ} (x : Fin n → Γ) :
    srcSub Γ n ≃* tgtSub x :=
  (MonoidHom.ofInjective (lift_t_injective (Γ := Γ) (n := n))).symm.trans
    (MonoidHom.ofInjective (lift_ts_injective x))

/-- Stage 3: adjoin the stable letter. -/
abbrev Top (Γ : Type) [Group Γ] {n : ℕ} (x : Fin n → Γ) : Type :=
  HNNExtension (Mid Γ n) (srcSub Γ n) (tgtSub x) (stepEquiv x)

/-- `Γ`, inside the top of the tower. -/
noncomputable def topOfBase {n : ℕ} (x : Fin n → Γ) : Γ →* Top Γ x :=
  (HNNExtension.of).comp (midOfBase.comp baseOf)

/-- **The embedding half, for the part of the tower built here.**  `Γ` embeds
in the top of the tower: the free-product inclusions are injective and so is
`HNNExtension.of`. -/
theorem base_injective {n : ℕ} (x : Fin n → Γ) :
    Function.Injective (topOfBase x) := by
  have h1 : Function.Injective (baseOf : Γ →* Base Γ) := baseOf_injective
  have h2 : Function.Injective (midOfBase : Base Γ →* Mid Γ n) :=
    Monoid.Coprod.inl_injective
  have h3 := HNNExtension.of_injective (stepEquiv x)
  intro a b hab
  exact h1 (h2 (h3 hab))

/-- **The killing relation.**  In the top of the tower the stable letter
conjugates `tᵢ` to `tᵢsᵢ`; setting it to `1` therefore forces `sᵢ = 1`, which
is what makes the collapse half reach the free group. -/
theorem conj_t_eq_ts {n : ℕ} (x : Fin n → Γ) (i : Fin n) :
    (HNNExtension.of (ts x i) : Top Γ x)
      = HNNExtension.t * HNNExtension.of (t i) * HNNExtension.t⁻¹ := by
  have hmem : t (Γ := Γ) i ∈ srcSub Γ n :=
    ⟨FreeGroup.of i, by simp⟩
  have h := HNNExtension.equiv_eq_conj (φ := stepEquiv x) ⟨t i, hmem⟩
  have hval : ((stepEquiv x ⟨t (Γ := Γ) i, hmem⟩ : tgtSub x) : Mid Γ n) = ts x i := by
    show (FreeGroup.lift (ts (Γ := Γ) x))
        ((MonoidHom.ofInjective (lift_t_injective (Γ := Γ) (n := n))).symm
          ⟨t i, hmem⟩) = _
    have hsym : (MonoidHom.ofInjective (lift_t_injective (Γ := Γ) (n := n))).symm
        ⟨t i, hmem⟩ = FreeGroup.of i := by
      apply (MonoidHom.ofInjective (lift_t_injective (Γ := Γ) (n := n))).injective
      rw [MulEquiv.apply_symm_apply]
      refine Subtype.ext ?_
      show t (Γ := Γ) i = FreeGroup.lift (t (Γ := Γ) (n := n)) (FreeGroup.of i)
      simp
    rw [hsym]
    simp
  rw [hval] at h
  exact h

/-! ## The cascade layers

Above the stable letter `u` the construction is a chain of HNN extensions along
*cyclic* associated subgroups: `⟨u⟩ ≅ ⟨u²⟩`, then `⟨b⟩ ≅ ⟨b²⟩`, then
`⟨z⟩ ≅ ⟨c⟩` with `z = ⁅w, s⁆`.  Each is legitimate for the same reason --- both
generators have infinite order --- and each contributes one implication to the
collapse, because `x y x⁻¹ = y²` with `x = 1` forces `y = 1`.

The layer is built once here, generically. -/

section CyclicLayer

variable {G : Type*} [Group G]

/-- An element of infinite order generates an infinite cyclic subgroup: the
`ℤ`-power map is injective. -/
theorem zpowersHom_injective {x : G} (h : ∀ n : ℤ, n ≠ 0 → x ^ n ≠ 1) :
    Function.Injective (zpowersHom G x) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  refine h (Multiplicative.toAdd a) ?_ ha
  intro h0
  exact hne (by
    have : a = Multiplicative.ofAdd (Multiplicative.toAdd a) := rfl
    rw [this, h0]
    rfl)

/-- The identification of two infinite cyclic subgroups. -/
noncomputable def cycEquiv {x y : G} (hx : Function.Injective (zpowersHom G x))
    (hy : Function.Injective (zpowersHom G y)) :
    (zpowersHom G x).range ≃* (zpowersHom G y).range :=
  (MonoidHom.ofInjective hx).symm.trans (MonoidHom.ofInjective hy)

/-- **One cascade layer**: adjoin a stable letter conjugating `⟨x⟩` onto
`⟨y⟩`. -/
abbrev CycLayer {x y : G} (hx : Function.Injective (zpowersHom G x))
    (hy : Function.Injective (zpowersHom G y)) : Type _ :=
  HNNExtension G (zpowersHom G x).range (zpowersHom G y).range (cycEquiv hx hy)

theorem mem_range_self (x : G) : x ∈ (zpowersHom G x).range :=
  ⟨Multiplicative.ofAdd (1 : ℤ), by simp⟩

/-- **The relation the layer imposes.**  This is the implication the collapse
runs on: with the stable letter trivial it reads `y = x`, and in the cascade
`y = x²`, which forces `x = 1`. -/
theorem cyc_conj {x y : G} (hx : Function.Injective (zpowersHom G x))
    (hy : Function.Injective (zpowersHom G y)) :
    (HNNExtension.of y : CycLayer hx hy)
      = HNNExtension.t * HNNExtension.of x * HNNExtension.t⁻¹ := by
  have h := HNNExtension.equiv_eq_conj (φ := cycEquiv hx hy) ⟨x, mem_range_self x⟩
  have hval : ((cycEquiv hx hy ⟨x, mem_range_self x⟩ :
      (zpowersHom G y).range) : G) = y := by
    show (zpowersHom G y) ((MonoidHom.ofInjective hx).symm ⟨x, mem_range_self x⟩) = y
    have hsym : (MonoidHom.ofInjective hx).symm ⟨x, mem_range_self x⟩
        = Multiplicative.ofAdd (1 : ℤ) := by
      apply (MonoidHom.ofInjective hx).injective
      rw [MulEquiv.apply_symm_apply]
      refine Subtype.ext ?_
      show x = zpowersHom G x (Multiplicative.ofAdd (1 : ℤ))
      simp
    rw [hsym]
    simp
  rw [hval] at h
  exact h

/-- The base of a cascade layer embeds in it. -/
theorem cycLayer_of_injective {x y : G} (hx : Function.Injective (zpowersHom G x))
    (hy : Function.Injective (zpowersHom G y)) :
    Function.Injective (HNNExtension.of : G →* CycLayer hx hy) :=
  HNNExtension.of_injective _

end CyclicLayer

/-! ## The full tower

Three cascade layers on top of `Top`, and the base still embeds.  The `k`-layer
needs `z = ⁅w, s⁆` to have infinite order, which is exactly the condition
`w ≠ 1` (`FreeProductOrder.pow_commutator_ne_one`); it is taken as a hypothesis
here so that the tower is stated for any element with that property. -/

section FullTower

variable {G : Type*} [Group G]

theorem sq_infinite {g : G} (h : ∀ m : ℤ, m ≠ 0 → g ^ m ≠ 1) :
    ∀ m : ℤ, m ≠ 0 → (g ^ (2 : ℤ)) ^ m ≠ 1 := by
  intro m hm hc
  refine h (2 * m) (by omega) ?_
  rw [zpow_mul]
  exact hc

variable {Γ : Type} [Group Γ] {n : ℕ} (x : Fin n → Γ)

/-- The stable letter of the killing layer has infinite order. -/
theorem u_infinite : ∀ m : ℤ, m ≠ 0 → (HNNExtension.t : Top Γ x) ^ m ≠ 1 :=
  fun _ hm => zpow_t_ne_one _ hm

/-! Each cascade layer is an opaque `def` carrying its own `Group` instance,
with its stable letter and its inclusion exposed by name.  They are not
`abbrev`s on purpose: the layers nest, and a reducible layer unfolds its whole
predecessor --- including the `cycEquiv` and injectivity proofs sitting in its
type --- into every elaboration above it, which is exponential in the number of
layers.  With the types opaque each step is one unfolding. -/

/-- Cascade layer one: `b`, with `b u b⁻¹ = u²`. -/
noncomputable def Casc1 : Type :=
  CycLayer (zpowersHom_injective (u_infinite x))
    (zpowersHom_injective (sq_infinite (u_infinite x)))

noncomputable instance : Group (Casc1 x) :=
  inferInstanceAs (Group (CycLayer (zpowersHom_injective (u_infinite x))
    (zpowersHom_injective (sq_infinite (u_infinite x)))))

/-- The inclusion of the killing layer into the first cascade layer. -/
noncomputable def casc1Of : Top Γ x →* Casc1 x :=
  (HNNExtension.of : Top Γ x →*
    CycLayer (zpowersHom_injective (u_infinite x))
      (zpowersHom_injective (sq_infinite (u_infinite x))))

/-- The stable letter `b`. -/
noncomputable def bLetter : Casc1 x :=
  (HNNExtension.t : CycLayer (zpowersHom_injective (u_infinite x))
    (zpowersHom_injective (sq_infinite (u_infinite x))))

theorem b_infinite : ∀ p : ℤ, p ≠ 0 → (bLetter x) ^ p ≠ 1 :=
  fun _ hp => zpow_t_ne_one _ hp

theorem casc1Of_injective : Function.Injective (casc1Of x) :=
  HNNExtension.of_injective _

/-- `b u b⁻¹ = u²`. -/
theorem casc1_conj :
    casc1Of x ((HNNExtension.t : Top Γ x) ^ (2 : ℤ))
      = bLetter x * casc1Of x HNNExtension.t * (bLetter x)⁻¹ :=
  cyc_conj _ _

/-- Cascade layer two: `c`, with `c b c⁻¹ = b²`. -/
noncomputable def Casc2 : Type :=
  CycLayer (zpowersHom_injective (b_infinite x))
    (zpowersHom_injective (sq_infinite (b_infinite x)))

noncomputable instance : Group (Casc2 x) :=
  inferInstanceAs (Group (CycLayer (zpowersHom_injective (b_infinite x))
    (zpowersHom_injective (sq_infinite (b_infinite x)))))

/-- The inclusion of the first cascade layer into the second. -/
noncomputable def casc2Of : Casc1 x →* Casc2 x :=
  (HNNExtension.of : Casc1 x →*
    CycLayer (zpowersHom_injective (b_infinite x))
      (zpowersHom_injective (sq_infinite (b_infinite x))))

/-- The stable letter `c`. -/
noncomputable def cLetter : Casc2 x :=
  (HNNExtension.t : CycLayer (zpowersHom_injective (b_infinite x))
    (zpowersHom_injective (sq_infinite (b_infinite x))))

theorem c_infinite : ∀ p : ℤ, p ≠ 0 → (cLetter x) ^ p ≠ 1 :=
  fun _ hp => zpow_t_ne_one _ hp

theorem casc2Of_injective : Function.Injective (casc2Of x) :=
  HNNExtension.of_injective _

/-- `c b c⁻¹ = b²`. -/
theorem casc2_conj :
    casc2Of x ((bLetter x) ^ (2 : ℤ))
      = cLetter x * casc2Of x (bLetter x) * (cLetter x)⁻¹ :=
  cyc_conj _ _

/-- `Γ`, inside `Casc2`. -/
noncomputable def casc2OfBase : Γ →* Casc2 x :=
  (casc2Of x).comp ((casc1Of x).comp (topOfBase x))

theorem casc2OfBase_injective : Function.Injective (casc2OfBase x) := by
  intro a b hab
  exact base_injective x (casc1Of_injective x (casc2Of_injective x hab))

/-- The base of stage 2, inside `Casc2`. -/
noncomputable def casc2OfMid : Mid Γ n →* Casc2 x :=
  (casc2Of x).comp ((casc1Of x).comp HNNExtension.of)

theorem casc2OfMid_injective : Function.Injective (casc2OfMid x) := by
  intro a b hab
  exact HNNExtension.of_injective _ (casc1Of_injective x (casc2Of_injective x hab))

/-- **The full tower**: adjoin `k` along `⟨z⟩ ≅ ⟨c⟩`. -/
noncomputable def Full {z : Casc2 x} (hz : ∀ p : ℤ, p ≠ 0 → z ^ p ≠ 1) : Type :=
  CycLayer (zpowersHom_injective hz) (zpowersHom_injective (c_infinite x))

noncomputable instance {z : Casc2 x} (hz : ∀ p : ℤ, p ≠ 0 → z ^ p ≠ 1) :
    Group (Full x hz) :=
  inferInstanceAs (Group (CycLayer (zpowersHom_injective hz)
    (zpowersHom_injective (c_infinite x))))

/-- The inclusion of the second cascade layer into the full tower. -/
noncomputable def fullOf {z : Casc2 x} (hz : ∀ p : ℤ, p ≠ 0 → z ^ p ≠ 1) :
    Casc2 x →* Full x hz :=
  (HNNExtension.of : Casc2 x →*
    CycLayer (zpowersHom_injective hz) (zpowersHom_injective (c_infinite x)))

/-- The stable letter `k`. -/
noncomputable def kLetter {z : Casc2 x} (hz : ∀ p : ℤ, p ≠ 0 → z ^ p ≠ 1) :
    Full x hz :=
  (HNNExtension.t : CycLayer (zpowersHom_injective hz)
    (zpowersHom_injective (c_infinite x)))

theorem fullOf_injective {z : Casc2 x} (hz : ∀ p : ℤ, p ≠ 0 → z ^ p ≠ 1) :
    Function.Injective (fullOf x hz) :=
  HNNExtension.of_injective _

/-- `k z k⁻¹ = c`. -/
theorem full_conj {z : Casc2 x} (hz : ∀ p : ℤ, p ≠ 0 → z ^ p ≠ 1) :
    fullOf x hz (cLetter x)
      = kLetter x hz * fullOf x hz z * (kLetter x hz)⁻¹ :=
  cyc_conj _ _

/-- **The embedding half.**  `Γ` embeds in the full tower. -/
theorem full_base_injective {z : Casc2 x} (hz : ∀ p : ℤ, p ≠ 0 → z ^ p ≠ 1) :
    Function.Injective ((fullOf x hz).comp (casc2OfBase x)) := by
  intro a b hab
  exact casc2OfBase_injective x (fullOf_injective x hz hab)

end FullTower

/-! ## The collapse half

The other direction of the biconditional, and like the collapse in
`Computability.RabinConstruction` it is stated about an *arbitrary* group
carrying the relations, so it survives any re-encoding of the presentation.

The chain is the cascade read downwards.  `z = 1` makes `c = 1`; a
Baumslag--Solitar relation `x y x⁻¹ = y²` with `x = 1` forces `y = 1`, which
takes `c = 1` to `b = 1` to `u = 1`; and `u = 1` turns the killing relation
`u tᵢ u⁻¹ = tᵢ sᵢ` into `sᵢ = 1` for every `i` at once.  With one index
carrying `xⱼ = 1` --- the letter `s` itself --- that gives `s = 1`, and then
every `xᵢ = 1`.

What is left standing is generated by the `tᵢ` and the last stable letter, with
every relation now trivial: a free group, which is MF.  That the collapse
reaches a free group rather than the trivial group is the whole reason the
associated subgroups above could be taken cyclic. -/

section Collapse

variable {H : Type*} [Group H]

theorem eq_one_of_eq_sq {y : H} (h : y = y ^ 2) : y = 1 := by
  have h' : y = y * y := by rwa [sq] at h
  have h2 : y * 1 = y * y := by rw [mul_one]; exact h'
  exact (mul_left_cancel h2).symm

theorem eq_one_of_conj_eq_sq {x y : H} (h : x * y * x⁻¹ = y ^ 2) (hx : x = 1) :
    y = 1 := by
  apply eq_one_of_eq_sq
  rw [← h, hx]
  simp

/-- **The collapse.**  Any group carrying the variant relations, in which the
witness `z` is trivial, has all of `c`, `b`, `u`, `s` and every `xᵢ` trivial. -/
theorem collapse_of_relations {n : ℕ} {S : H} {X T : Fin n → H} {U B C K Z : H}
    {j : Fin n} (hj : X j = 1)
    (hk : K * Z * K⁻¹ = C)
    (hc : C * B * C⁻¹ = B ^ 2)
    (hb : B * U * B⁻¹ = U ^ 2)
    (hu : ∀ i, U * T i * U⁻¹ = T i * (S * X i))
    (hz : Z = 1) :
    C = 1 ∧ B = 1 ∧ U = 1 ∧ S = 1 ∧ ∀ i, X i = 1 := by
  have hC : C = 1 := by rw [← hk, hz, mul_one, mul_inv_cancel]
  have hB : B = 1 := eq_one_of_conj_eq_sq hc hC
  have hU : U = 1 := eq_one_of_conj_eq_sq hb hB
  have hSX : ∀ i, S * X i = 1 := by
    intro i
    have h := hu i
    rw [hU, one_mul, inv_one, mul_one] at h
    exact (mul_left_cancel (a := T i) (by rw [mul_one, ← h])).symm
  have hS : S = 1 := by
    have := hSX j
    rwa [hj, mul_one] at this
  refine ⟨hC, hB, hU, hS, fun i => ?_⟩
  have := hSX i
  rwa [hS, one_mul] at this

end Collapse

end RabinVariantTower
end GroupApproximation
