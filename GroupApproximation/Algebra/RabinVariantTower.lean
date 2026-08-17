import GroupApproximation.Algebra.HNNRetraction
import GroupApproximation.Algebra.FreeProductOrder
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

/-- Stage 1: `Γ * ℤ`. -/
abbrev Base (Γ : Type) [Group Γ] : Type := Monoid.Coprod Γ (Multiplicative ℤ)

/-- The free letter adjoined in stage 1. -/
def s : Base Γ := Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))

/-- `sᵢ = s · xᵢ`.  The change of generators: these have infinite order even
when the `xᵢ` do not. -/
def sgen (x : Γ) : Base Γ := s * Monoid.Coprod.inl x

theorem zpow_sgen_ne_one (x : Γ) {n : ℤ} (hn : n ≠ 0) : (sgen x) ^ n ≠ 1 :=
  zpow_inr_mul_inl_ne_one x hn

/-- Stage 2: adjoin a free group of rank `n` as a free factor. -/
abbrev Mid (Γ : Type) [Group Γ] (n : ℕ) : Type :=
  Monoid.Coprod (Base Γ) (FreeGroup (Fin n))

/-- The `i`th free letter of stage 2. -/
def t {n : ℕ} (i : Fin n) : Mid Γ n :=
  Monoid.Coprod.inr (FreeGroup.of i)

/-- `Γ`, inside stage 2. -/
def midOfBase {n : ℕ} : Base Γ →* Mid Γ n := Monoid.Coprod.inl

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
  (HNNExtension.of).comp (midOfBase.comp Monoid.Coprod.inl)

/-- **The embedding half, for the part of the tower built here.**  `Γ` embeds
in the top of the tower: the free-product inclusions are injective and so is
`HNNExtension.of`. -/
theorem base_injective {n : ℕ} (x : Fin n → Γ) :
    Function.Injective (topOfBase x) := by
  have h1 : Function.Injective (Monoid.Coprod.inl : Γ →* Base Γ) :=
    Monoid.Coprod.inl_injective
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

end RabinVariantTower
end GroupApproximation
