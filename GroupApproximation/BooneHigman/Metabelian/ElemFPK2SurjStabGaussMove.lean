import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabFactorEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability: moving the middle row by `St_n` (lane bh-met-82)

`SurjStabGaussForm x w` says that `x` has a conjugate
`stab g₁ · padCol v · padRow w · padCol c · padRow w' · stab g₂`.  This is
`SurjStabFactorDisj` without the disjointness clause and with the middle row `w` fixed.

## What is proved (any unital ring `R`)

* `surjStabGauss_form_move`: `SurjStabGaussForm x w → SurjStabGaussForm x (w ᵥ* padMat h)` for
  every `h : St_n(R)`.
* `surjStabGauss_reach_step`: an elementary column operation `w ↦ w + e_j (w_i t)` (`i ≠ j`) is
  realised by `h = x_{ij}(t)`.

Truth check.  Put `H = stab h`.  Then `padRow (w ᵥ* padMat h) = H⁻¹ · padRow w · H`
(`stab_conj_padRow`) and `padCol (padMat h⁻¹ *ᵥ c) = H⁻¹ · padCol c · H` (`stab_conj_padCol`
at `h⁻¹`).  So inserting `H H⁻¹` between consecutive factors gives
`stab g₁ · P V U V · stab g₂ =
stab (g₁ h) · (H⁻¹ P H) (H⁻¹ V H) (H⁻¹ U H) (H⁻¹ V H) · stab (h⁻¹ g₂)`,
and each conjugated factor has the same shape.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- `x` has a conjugate `stab g₁ · padCol v · padRow w · padCol c · padRow w' · stab g₂`, with
the middle row `w` given and no constraint on the supports. -/
def SurjStabGaussForm (x : St (n + 1) R) (w : Fin n → R) : Prop :=
  ∃ (z : St (n + 1) R) (g₁ g₂ : St n R) (v c w' : Fin n → R),
    z * x * z⁻¹ = stab n R g₁ * padCol v * padRow w * padCol c * padRow w' * stab n R g₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabGaussForm

/-- `w'` lies in the right `St_n`-orbit of the row vector `w`. -/
def SurjStabGaussReach (w w' : Fin n → R) : Prop :=
  ∃ h : St n R, w ᵥ* padMat h = w'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabGaussReach

theorem surjStabGauss_reach_refl (w : Fin n → R) : SurjStabGaussReach w w :=
  ⟨1, by rw [map_one, Matrix.vecMul_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_reach_refl

theorem surjStabGauss_reach_trans {w w' w'' : Fin n → R} (h₁ : SurjStabGaussReach w w')
    (h₂ : SurjStabGaussReach w' w'') : SurjStabGaussReach w w'' := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨a * b, by rw [map_mul, ← Matrix.vecMul_vecMul, ha, hb]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_reach_trans

/-- An elementary column operation `w ↦ w + e_j (w_i t)` is realised by `x_{ij}(t)`. -/
theorem surjStabGauss_reach_step (w : Fin n → R) (i j : Fin n) (hij : i ≠ j) (t : R) :
    SurjStabGaussReach w (w + Pi.single j (w i * t)) :=
  ⟨x i j hij t, by rw [padMat_x, Matrix.vecMul_add, Matrix.vecMul_one, surjStab_vecMul_single]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_reach_step

/-- The form is invariant under `w ↦ w ᵥ* padMat h` (conjugate every factor by `stab h`). -/
theorem surjStabGauss_form_move {x : St (n + 1) R} {w : Fin n → R}
    (hF : SurjStabGaussForm x w) (h : St n R) : SurjStabGaussForm x (w ᵥ* padMat h) := by
  obtain ⟨z, g₁, g₂, v, c, w', hz⟩ := hF
  have hr := stab_conj_padRow h w
  have hw := stab_conj_padRow h w'
  have hc := stab_conj_padCol h⁻¹ c
  rw [map_inv (stab n R) h, inv_inv] at hc
  have hv : padCol (padMat h⁻¹ *ᵥ v) = (stab n R h)⁻¹ * (padCol v * stab n R h) := by
    rw [surjStab_padCol_mul_stab h v, inv_mul_cancel_left]
  refine ⟨z, g₁ * h, h⁻¹ * g₂, padMat h⁻¹ *ᵥ v, padMat h⁻¹ *ᵥ c, w' ᵥ* padMat h, ?_⟩
  rw [hz, ← hr, ← hc, ← hw, hv, map_mul (stab n R) g₁ h, map_mul (stab n R) h⁻¹ g₂,
    map_inv (stab n R) h]
  simp only [mul_assoc, mul_inv_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_form_move

/-- Transport of the form along the orbit relation. -/
theorem surjStabGauss_form_of_reach {x : St (n + 1) R} {w w' : Fin n → R}
    (hF : SurjStabGaussForm x w) (hr : SurjStabGaussReach w w') : SurjStabGaussForm x w' := by
  obtain ⟨h, rfl⟩ := hr
  exact surjStabGauss_form_move hF h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_form_of_reach

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
