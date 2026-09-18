/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BHPalomar.GraphProducts.FreeProductMap
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-!
# Transvections and twisted conjugations of `H ∗ F(x, y)`

Fix a group `H` and put `P = H ∗ F(x, y)`, `Q = H ∗ ⟨y⟩`, with `j : Q → P` the inclusion.

* `rhoEnd a` (`ρ_a`, for `a ∈ Q`) fixes `H` and `y` and sends `x ↦ x a`.
  Then `ρ_a ρ_b = ρ_(ab)`, because `ρ_a` fixes `j(Q)` (`rhoEnd_mul`).
* `gammaEnd h` (`γ_h`, for `h ∈ H`) fixes `H`, sends `x ↦ x h` and `y ↦ h⁻¹ y h`. Then
  `γ_h γ_k = γ_(hk)` (`gammaEnd_mul`).
* The two conjugation relations used for the retract amalgam are:
  - `gamma_rho_comm`: `γ_h ρ_k = ρ_k γ_h` when `h` and `k` commute in `H`;
  - `gamma_rho_conj`: `γ_h ρ_(y l y⁻¹) = ρ_(y (h l h⁻¹) y⁻¹) γ_h`.
* `piHom : P → (H ∗ H) ⋊ ℤ` kills `x`, sends `H` to the first factor and `y` to the swap.
  It shows that `h⁻¹ y h = y` forces `h = 1` (`eq_one_of_conj_y`), and it separates
  `y H y⁻¹` from `H` (`piHom_conj_y`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.BHPalomar.GraphProducts

open Monoid

variable {H : Type} [Group H]

/-- `P = H ∗ F(x, y)`, with `x = of 0` and `y = of 1`. -/
abbrev TwP (H : Type) [Group H] := Coprod H (FreeGroup (Fin 2))

/-- `Q = H ∗ ⟨y⟩`. -/
abbrev TwQ (H : Type) [Group H] := Coprod H (FreeGroup Unit)

local notation "𝕩" => Coprod.inr (FreeGroup.of (0 : Fin 2))
local notation "𝕪" => Coprod.inr (FreeGroup.of (1 : Fin 2))
local notation "𝕢" => Coprod.inr (FreeGroup.of ())

/-- The inclusion `j : H ∗ ⟨y⟩ → H ∗ F(x, y)`. -/
def tj : TwQ H →* TwP H := Coprod.map (MonoidHom.id H) (FreeGroup.map fun _ => (1 : Fin 2))

@[simp] theorem tj_inl (h : H) : tj (Coprod.inl h : TwQ H) = (Coprod.inl h : TwP H) := rfl

@[simp] theorem tj_inr_of (u : Unit) : tj (Coprod.inr (FreeGroup.of u) : TwQ H) = (𝕪 : TwP H) := by
  simp only [tj, Coprod.map_apply_inr, FreeGroup.map.of]

/-! ### Transvections `ρ_a` -/

/-- `ρ_a`: fixes `H` and `y`, sends `x ↦ x · j(a)`. -/
def rhoEnd (a : TwQ H) : TwP H →* TwP H :=
  Coprod.lift Coprod.inl (FreeGroup.lift ![𝕩 * tj a, 𝕪])

@[simp] theorem rhoEnd_inl (a : TwQ H) (h : H) : rhoEnd a (Coprod.inl h) = Coprod.inl h := by
  simp [rhoEnd]

@[simp] theorem rhoEnd_x (a : TwQ H) : rhoEnd a 𝕩 = 𝕩 * tj a := by
  simp [rhoEnd]

@[simp] theorem rhoEnd_y (a : TwQ H) : rhoEnd a 𝕪 = 𝕪 := by
  simp [rhoEnd]

theorem rhoEnd_tj (a b : TwQ H) : rhoEnd a (tj b) = tj b := by
  have hc : (rhoEnd a).comp tj = tj := by
    apply Coprod.hom_ext
    · ext h
      simp
    · apply FreeGroup.ext_hom
      intro u
      simp
  exact DFunLike.congr_fun hc b

theorem rhoEnd_mul (a b : TwQ H) : rhoEnd (a * b) = (rhoEnd a).comp (rhoEnd b) := by
  apply Coprod.hom_ext
  · ext h
    simp
  · apply FreeGroup.ext_hom
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp [map_mul, rhoEnd_tj, mul_assoc]
    · simp

theorem rhoEnd_one : rhoEnd (1 : TwQ H) = MonoidHom.id (TwP H) := by
  apply Coprod.hom_ext
  · ext h
    simp
  · apply FreeGroup.ext_hom
    rw [Fin.forall_fin_two]
    exact ⟨by simp, by simp⟩

/-- `a ↦ ρ_a` as a homomorphism `H ∗ ⟨y⟩ → Aut(P)`. -/
def rho : TwQ H →* MulAut (TwP H) := autOfEnd rhoEnd rhoEnd_mul rhoEnd_one

@[simp] theorem rho_apply (a : TwQ H) (p : TwP H) : rho a p = rhoEnd a p := rfl

/-! ### Twisted conjugations `γ_h` -/

/-- `γ_h`: fixes `H`, sends `x ↦ x h` and `y ↦ h⁻¹ y h`. -/
def gammaEnd (h : H) : TwP H →* TwP H :=
  Coprod.lift Coprod.inl (FreeGroup.lift ![𝕩 * Coprod.inl h, (Coprod.inl h)⁻¹ * 𝕪 * Coprod.inl h])

@[simp] theorem gammaEnd_inl (h k : H) : gammaEnd h (Coprod.inl k) = Coprod.inl k := by
  simp [gammaEnd]

@[simp] theorem gammaEnd_x (h : H) : gammaEnd h 𝕩 = 𝕩 * Coprod.inl h := by
  simp [gammaEnd]

@[simp] theorem gammaEnd_y (h : H) :
    gammaEnd h 𝕪 = (Coprod.inl h)⁻¹ * 𝕪 * Coprod.inl h := by
  simp [gammaEnd]

theorem gammaEnd_mul (h k : H) : gammaEnd (h * k) = (gammaEnd h).comp (gammaEnd k) := by
  apply Coprod.hom_ext
  · ext l
    simp
  · apply FreeGroup.ext_hom
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp [map_mul, mul_assoc]
    · simp [map_mul, map_inv, mul_inv_rev, mul_assoc]

theorem gammaEnd_one : gammaEnd (1 : H) = MonoidHom.id (TwP H) := by
  apply Coprod.hom_ext
  · ext h
    simp
  · apply FreeGroup.ext_hom
    rw [Fin.forall_fin_two]
    exact ⟨by simp, by simp⟩

/-- `h ↦ γ_h` as a homomorphism `H → Aut(P)`. -/
def gamma : H →* MulAut (TwP H) := autOfEnd gammaEnd gammaEnd_mul gammaEnd_one

@[simp] theorem gamma_apply (h : H) (p : TwP H) : gamma h p = gammaEnd h p := rfl

/-! ### The two conjugation relations -/

/-- `γ_h ρ_k = ρ_k γ_h` when `h` and `k` commute. -/
theorem gamma_rho_comm (h k : H) (hk : h * k = k * h) :
    (gammaEnd h).comp (rhoEnd (Coprod.inl k)) = (rhoEnd (Coprod.inl k)).comp (gammaEnd h) := by
  have hk' : (Coprod.inl h : TwP H) * Coprod.inl k = Coprod.inl k * Coprod.inl h := by
    rw [← map_mul, ← map_mul, hk]
  apply Coprod.hom_ext
  · ext l
    simp
  · apply FreeGroup.ext_hom
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp [map_mul, mul_assoc, hk']
    · simp [map_mul, map_inv]

/-- `γ_h ρ_(y l y⁻¹) = ρ_(y (h l h⁻¹) y⁻¹) γ_h`. -/
theorem gamma_rho_conj (h l : H) :
    (gammaEnd h).comp (rhoEnd (𝕢 * Coprod.inl l * 𝕢⁻¹)) =
      (rhoEnd (𝕢 * Coprod.inl (h * l * h⁻¹) * 𝕢⁻¹)).comp (gammaEnd h) := by
  apply Coprod.hom_ext
  · ext k
    simp
  · apply FreeGroup.ext_hom
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp only [MonoidHom.comp_apply, rhoEnd_x, gammaEnd_x, map_mul, map_inv, tj_inl,
        tj_inr_of, gammaEnd_inl, gammaEnd_y, rhoEnd_inl]
      group
    · simp [map_mul, map_inv]

/-! ### Separating `H` from `y H y⁻¹` -/

/-- `H ∗ H`, as a free product over `Bool`. -/
abbrev HH (H : Type) [Group H] := CoprodI (fun _ : Bool => H)

/-- The swap of the two factors of `H ∗ H`. -/
def swapHom : HH H →* HH H := CoprodI.lift fun b => CoprodI.of (i := !b)

@[simp] theorem swapHom_of (b : Bool) (h : H) :
    swapHom (CoprodI.of (i := b) h : HH H) = CoprodI.of (i := !b) h := by
  simp [swapHom]

theorem swapHom_comp_swapHom : (swapHom : HH H →* HH H).comp swapHom = MonoidHom.id (HH H) := by
  apply CoprodI.ext_hom
  intro b
  ext h
  simp

/-- The swap as an automorphism. -/
def swapAut : MulAut (HH H) :=
  MonoidHom.toMulEquiv swapHom swapHom swapHom_comp_swapHom swapHom_comp_swapHom

/-- `ℤ` acting on `H ∗ H` by powers of the swap. -/
def swapZ : Multiplicative ℤ →* MulAut (HH H) := zpowersHom (MulAut (HH H)) swapAut

theorem swapZ_one_apply (n : HH H) : swapZ (Multiplicative.ofAdd 1) n = swapHom n := by
  simp [swapZ, swapAut]

/-- `(H ∗ H) ⋊ ℤ`. -/
abbrev Pi2 (H : Type) [Group H] := HH H ⋊[swapZ] Multiplicative ℤ

/-- `π : P → (H ∗ H) ⋊ ℤ`: `h ↦ h` in the first factor, `x ↦ 1`, `y ↦` the generator. -/
def piHom : TwP H →* Pi2 H :=
  Coprod.lift (SemidirectProduct.inl.comp (CoprodI.of (i := false)))
    (FreeGroup.lift ![1, SemidirectProduct.inr (Multiplicative.ofAdd 1)])

@[simp] theorem piHom_inl (h : H) :
    piHom (Coprod.inl h : TwP H) = SemidirectProduct.inl (CoprodI.of (i := false) h) := by
  simp [piHom]

@[simp] theorem piHom_y : piHom (𝕪 : TwP H) = SemidirectProduct.inr (Multiplicative.ofAdd 1) := by
  simp [piHom]

theorem conj_inr_inl {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} (g : G) (n : N) :
    (SemidirectProduct.inr g * SemidirectProduct.inl n * (SemidirectProduct.inr g)⁻¹ :
      N ⋊[φ] G) = SemidirectProduct.inl (φ g n) := by
  rw [← map_inv, ← SemidirectProduct.inl_aut]

/-- `π(y h y⁻¹)` is `h` in the second factor. -/
theorem piHom_conj_y (h : H) :
    piHom (𝕪 * Coprod.inl h * 𝕪⁻¹ : TwP H) = SemidirectProduct.inl (CoprodI.of (i := true) h) := by
  rw [map_mul, map_mul, map_inv, piHom_y, piHom_inl, conj_inr_inl, swapZ_one_apply, swapHom_of]
  rfl

/-- Kill the first factor of `H ∗ H`. -/
def killFalse : HH H →* H := CoprodI.lift fun b => bif b then MonoidHom.id H else 1

@[simp] theorem killFalse_true (h : H) : killFalse (CoprodI.of (i := true) h : HH H) = h := by
  simp [killFalse]

@[simp] theorem killFalse_false (h : H) : killFalse (CoprodI.of (i := false) h : HH H) = 1 := by
  simp [killFalse]

/-- **In `H ∗ F(x, y)`, no nontrivial element of `H` commutes with `y`.** -/
theorem eq_one_of_conj_y (h : H) (hy : (Coprod.inl h)⁻¹ * 𝕪 * Coprod.inl h = (𝕪 : TwP H)) :
    h = 1 := by
  have hc : 𝕪 * Coprod.inl h * 𝕪⁻¹ = (Coprod.inl h : TwP H) := by
    calc 𝕪 * Coprod.inl h * 𝕪⁻¹
        = Coprod.inl h * ((Coprod.inl h)⁻¹ * 𝕪 * Coprod.inl h) * 𝕪⁻¹ := by group
      _ = Coprod.inl h := by rw [hy]; group
  have h2 := congrArg piHom hc
  rw [piHom_conj_y, piHom_inl, SemidirectProduct.inl_inj] at h2
  have h3 := congrArg killFalse h2
  rwa [killFalse_true, killFalse_false] at h3

end GroupApproximation.BHPalomar.GraphProducts
