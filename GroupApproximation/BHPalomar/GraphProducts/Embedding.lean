/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BHPalomar.GraphProducts.Semidirect
import GroupApproximation.BHPalomar.GraphProducts.Twist

/-!
# The retract amalgam embeds in `Aut_H(H ∗ F₂)`

Let `ι : C → X` have a retraction `r`, `L = ker r`, and embed `X` and `K` in a group `H` so
that the images of `C` and `K` commute. Then `G = X *_C (C × K)` embeds in `Aut_H(H ∗ F(x, y))`
(`retractAmalgam_embeds_in_relAut`). This is Steps 1–5 of the route
`pbh-graph-product-closure-proof`:

* `k ↦ ρ_k`, `l ↦ ρ_(y l y⁻¹)`, `c ↦ γ_c` defines `Φ : (K ∗ L) ⋊ C → Aut_H(H ∗ F₂)`, using
  the relations `gamma_rho_comm` and `gamma_rho_conj`;
* `Φ` is injective: on `y`, `Φ(n, c)` is conjugation by `c`, so `c = 1`
  (`eq_one_of_conj_y`); then `Φ(n) = ρ_(w n)` with `w : K ∗ L → H ∗ ⟨y⟩` injective, since
  after `π : H ∗ F₂ → (H ∗ H) ⋊ ℤ` it is the free product of the embeddings of `K` and `L`
  (`lift_of_comp_injective`);
* `G → (K ∗ L) ⋊ C` is injective (`psi_injective`).

Nothing here is imported from the literature.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace GroupApproximation.BHPalomar.GraphProducts

open Monoid

local notation "𝕩" => Coprod.inr (FreeGroup.of (0 : Fin 2))
local notation "𝕪" => Coprod.inr (FreeGroup.of (1 : Fin 2))
local notation "𝕢" => Coprod.inr (FreeGroup.of ())

variable {X C K H : Type} [Group X] [Group C] [Group K] [Group H] (D : RetractData X C K H)

/-- The factors of `N = K ∗ L` into `H ∗ ⟨y⟩`: `l ↦ y φ(l) y⁻¹` and `k ↦ ψ(k)`. -/
def wT : ∀ b : Bool, ↥(factorT D b) →* TwQ H
  | true => (MulAut.conj (𝕢 : TwQ H)).toMonoidHom.comp
      (Coprod.inl.comp (D.φ.comp ((MonoidHom.fst X K).comp (factorT D true).subtype)))
  | false => Coprod.inl.comp (D.ψ.comp ((MonoidHom.snd X K).comp (factorT D false).subtype))

theorem wT_true_apply (s : ↥(factorT D true)) :
    wT D true s = (𝕢 : TwQ H) * Coprod.inl (D.φ (s : X × K).1) * 𝕢⁻¹ := rfl

theorem wT_false_apply (s : ↥(factorT D false)) :
    wT D false s = (Coprod.inl (D.ψ (s : X × K).2) : TwQ H) := rfl

/-- `w : K ∗ L → H ∗ ⟨y⟩`. -/
def W : NN D →* TwQ H := Monoid.CoprodI.lift (wT D)

@[simp] theorem W_of (b : Bool) (t : ↥(factorT D b)) :
    W D (Monoid.CoprodI.of (i := b) t) = wT D b t :=
  Monoid.CoprodI.lift_of _ _

/-- The factors of `N` into `H`, one per copy of `H` in `H ∗ H`. -/
def uT : ∀ b : Bool, ↥(factorT D b) →* H
  | true => D.φ.comp ((MonoidHom.fst X K).comp (factorT D true).subtype)
  | false => D.ψ.comp ((MonoidHom.snd X K).comp (factorT D false).subtype)

theorem uT_true_apply (s : ↥(factorT D true)) : uT D true s = D.φ (s : X × K).1 := rfl

theorem uT_false_apply (s : ↥(factorT D false)) : uT D false s = D.ψ (s : X × K).2 := rfl

theorem uT_injective (b : Bool) : Function.Injective (uT D b) := by
  cases b <;> intro s t hst
  · rw [uT_false_apply, uT_false_apply] at hst
    have h1 := (mem_factorT_false D).mp s.2
    have h2 := (mem_factorT_false D).mp t.2
    apply Subtype.ext
    exact Prod.ext (h1.trans h2.symm) (D.hψ hst)
  · rw [uT_true_apply, uT_true_apply] at hst
    have h1 := (mem_factorT_true D).mp s.2
    have h2 := (mem_factorT_true D).mp t.2
    apply Subtype.ext
    exact Prod.ext (D.hφ hst) (h1.2.trans h2.2.symm)

theorem piHom_jW : (piHom.comp tj).comp (W D) = SemidirectProduct.inl.comp
    (Monoid.CoprodI.lift fun b =>
      (Monoid.CoprodI.of (M := fun _ : Bool => H) (i := b)).comp (uT D b)) := by
  apply Monoid.CoprodI.ext_hom
  intro b
  ext t : 1
  simp only [MonoidHom.comp_apply, W_of, Monoid.CoprodI.lift_of]
  cases b
  · rw [wT_false_apply, tj_inl, piHom_inl, uT_false_apply]
  · rw [wT_true_apply, map_mul tj, map_mul tj, map_inv tj, tj_inl, tj_inr_of, piHom_conj_y,
      uT_true_apply]

/-- **`w` is injective**, even after `j : H ∗ ⟨y⟩ → H ∗ F₂`. -/
theorem jW_injective : Function.Injective (tj.comp (W D)) := by
  have h : Function.Injective ((piHom.comp tj).comp (W D)) := by
    rw [piHom_jW]
    exact SemidirectProduct.inl_injective.comp (lift_of_comp_injective (uT D) (uT_injective D))
  intro a b hab
  apply h
  show piHom (tj (W D a)) = piHom (tj (W D b))
  exact congrArg piHom hab

/-! ### The homomorphism `Φ` -/

/-- `Φ` on `N`: `n ↦ ρ_(w n)`. -/
def phiN : NN D →* MulAut (TwP H) := rho.comp (W D)

/-- `Φ` on `C`: `c ↦ γ_(φ(ι c))`. -/
def phiC : C →* MulAut (TwP H) := gamma.comp (D.φ.comp D.ι)

theorem rho_gamma_of_end {a a' : TwQ H} {h : H}
    (e : (gammaEnd h).comp (rhoEnd a) = (rhoEnd a').comp (gammaEnd h)) :
    rho a' = gamma h * rho a * (gamma h)⁻¹ := by
  apply eq_mul_inv_of_mul_eq
  ext p
  simp only [MulAut.mul_apply, rho_apply, gamma_apply]
  exact (DFunLike.congr_fun e p).symm

theorem phi_compat (c : C) :
    (phiN D).comp (act D c).toMonoidHom = (MulAut.conj (phiC D c)).toMonoidHom.comp (phiN D) := by
  apply Monoid.CoprodI.ext_hom
  intro b
  ext t : 1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, act_of, phiN, phiC, W_of,
    MulAut.conj_apply]
  cases b
  · rw [wT_false_apply, wT_false_apply, conjT_snd]
    exact rho_gamma_of_end (gamma_rho_comm _ _ (D.comm c _))
  · rw [wT_true_apply, wT_true_apply, conjT_fst, map_mul D.φ, map_mul D.φ, map_inv D.φ]
    exact rho_gamma_of_end (gamma_rho_conj _ _)

/-- `Φ : (K ∗ L) ⋊ C → Aut(H ∗ F₂)`. -/
def PhiS : SS D →* MulAut (TwP H) := SemidirectProduct.lift (phiN D) (phiC D) (phi_compat D)

theorem PhiS_mk (n : NN D) (c : C) :
    PhiS D ⟨n, c⟩ = rho (W D n) * gamma (D.φ (D.ι c)) := rfl

theorem PhiS_mem (s : SS D) : PhiS D s ∈ relAut H 2 := by
  obtain ⟨n, c⟩ := s
  rw [mem_relAut, PhiS_mk]
  intro h
  simp [MulAut.mul_apply]

/-- **`Φ` is injective.** -/
theorem PhiS_injective : Function.Injective (PhiS D) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨n, c⟩ hs
  rw [PhiS_mk] at hs
  have hy := congrArg (fun α : MulAut (TwP H) => α 𝕪) hs
  simp only [MulAut.mul_apply, MulAut.one_apply, rho_apply, gamma_apply, gammaEnd_y, map_mul,
    map_inv, rhoEnd_inl, rhoEnd_y] at hy
  have hc1 : D.φ (D.ι c) = 1 := eq_one_of_conj_y _ hy
  have hι : D.ι c = 1 := D.hφ (by rw [hc1, map_one])
  have hc : c = 1 := by
    calc c = D.r (D.ι c) := (D.hr c).symm
      _ = 1 := by rw [hι, map_one]
  subst hc
  simp only [map_one, mul_one] at hs
  have hx := congrArg (fun α : MulAut (TwP H) => α 𝕩) hs
  simp only [MulAut.one_apply, rho_apply, rhoEnd_x] at hx
  have hw : tj (W D n) = 1 := mul_left_cancel (hx.trans (mul_one _).symm)
  have hn : n = 1 := (injective_iff_map_eq_one _).mp (jW_injective D) n hw
  subst hn
  rfl

/-- **Steps 1–5**: `X *_C (C × K)` embeds in `Aut_H(H ∗ F₂)`. -/
theorem retractData_embeds :
    ∃ f : RetractAmalgam D.ι K →* relAut H 2, Function.Injective f := by
  refine ⟨((PhiS D).comp (Psi D)).codRestrict (relAut H 2) (fun a => PhiS_mem D _), ?_⟩
  intro a b hab
  have h : PhiS D (Psi D a) = PhiS D (Psi D b) := congrArg Subtype.val hab
  exact psi_injective D (PhiS_injective D h)

/-- **The retract amalgam `X *_C (C × K)` embeds in `Aut_H(H ∗ F₂)`** whenever `X` and `K`
embed in `H` with `C` and `K` commuting. -/
theorem retractAmalgam_embeds_in_relAut (ι : C →* X) (r : X →* C) (hr : ∀ c, r (ι c) = c)
    (φ : X →* H) (hφ : Function.Injective φ) (ψ : K →* H) (hψ : Function.Injective ψ)
    (comm : ∀ c k, φ (ι c) * ψ k = ψ k * φ (ι c)) :
    ∃ f : RetractAmalgam ι K →* relAut H 2, Function.Injective f :=
  retractData_embeds ⟨ι, r, hr, φ, hφ, ψ, hψ, comm⟩

end GroupApproximation.BHPalomar.GraphProducts
