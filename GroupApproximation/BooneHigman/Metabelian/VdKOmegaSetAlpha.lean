import GroupApproximation.BooneHigman.Metabelian.VdKOmegaSetCompat
import GroupApproximation.Meta.AxiomGuard

/-!
# Building `Ω` on `P̃ × X`, part 2: the explicit `α`, and `β` from row data

Lane `bh-met-93a`.  Unconditional, for every commutative `R`, every `n` and every set `X`.

The carrier is `Ω = P̃ × X`, where `P̃ = R^n ⋊ St_n(R)` is the parabolic and `X` is any set.

* `vdkOmegaSet_alpha X`: `P̃` acts on `Ω` by left multiplication on the first factor.  It is
  written down explicitly, with no reference to `St_{n+1}(R)` or to `stab`.
* `vdkOmegaSet_alpha_free`: `St_n(R)` (indeed all of `P̃`) acts freely, so the freeness clause
  holds at every `ω₀ = (1, x₀)`.
* `vdkOmegaSet_RowRel X ρ`: the generator relations for a row action `ρ : R^n →* Perm Ω`.
  Only Steinberg generators `x_{ij}(c)` and unit vectors `b e_k` occur.
* `vdkOmegaSet_beta X ρ hall`: from `RowRel` (via `vdkOmegaSet_compatAt_all`), `ρ` and `α`
  on `St_n(R)` glue to an action of the opposite parabolic `P̃⁻`.  It agrees with `α` on
  `St_n(R)` by construction (`vdkOmegaSet_beta_inr`), and its row part is `ρ`
  (`vdkOmegaSet_rv_beta`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

variable {n : ℕ} {R : Type*} [CommRing R] (X : Type*)

/-- Left multiplication by `p` on the first factor of `P̃ × X`. -/
def vdkOmegaSet_perm (p : vdkParPres_Tilde n R) : Equiv.Perm (vdkParPres_Tilde n R × X) where
  toFun ω := (p * ω.1, ω.2)
  invFun ω := (p⁻¹ * ω.1, ω.2)
  left_inv ω := Prod.ext (inv_mul_cancel_left p ω.1) rfl
  right_inv ω := Prod.ext (mul_inv_cancel_left p ω.1) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_perm

theorem vdkOmegaSet_perm_apply (p : vdkParPres_Tilde n R) (ω : vdkParPres_Tilde n R × X) :
    vdkOmegaSet_perm X p ω = (p * ω.1, ω.2) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_perm_apply

/-- **The explicit `α`.**  `P̃` acts on `P̃ × X` by left multiplication on the first factor. -/
def vdkOmegaSet_alpha : vdkParPres_Tilde n R →* Equiv.Perm (vdkParPres_Tilde n R × X) where
  toFun := vdkOmegaSet_perm X
  map_one' := Equiv.ext fun ω ↦ Prod.ext (one_mul ω.1) rfl
  map_mul' p q := Equiv.ext fun ω ↦ Prod.ext (mul_assoc p q ω.1) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_alpha

/-- **Freeness.**  `St_n(R)` acts freely on `P̃ × X` through `α`, at every `(1, x₀)`. -/
theorem vdkOmegaSet_alpha_free (x₀ : X) (g : St n R)
    (h : vdkOmegaSet_alpha X (vdkParPres_inr g) (1, x₀) = (1, x₀)) : g = 1 := by
  have h1 : vdkParPres_inr g * 1 = 1 := congrArg Prod.fst h
  rw [mul_one] at h1
  have h2 : (SemidirectProduct.inr g : vdkParPres_Tilde n R) = SemidirectProduct.inr 1 := by
    rw [map_one]
    exact h1
  exact SemidirectProduct.inr_injective h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_alpha_free

/-- The generator relations for a row action `ρ` on `P̃ × X`.  For every Steinberg generator
`x_{ij}(c)` of `St_n(R)` and every unit row vector `b e_k`,
`ρ(b e_k · M_{x_{ij}(c)}⁻¹) = α(x_{ij}(c)) ρ(b e_k) α(x_{ij}(c))⁻¹`.  Here
`vdkOmega_rowAct g w` is `w ↦ w M_g⁻¹`, and `M_{x_{ij}(c)}⁻¹ = 1 - c E_{ij}`. -/
def vdkOmegaSet_RowRel
    (ρ : Multiplicative (Fin n → R) →* Equiv.Perm (vdkParPres_Tilde n R × X)) : Prop :=
  ∀ (i j : Fin n) (h : i ≠ j) (c : R) (k : Fin n) (b : R),
    ρ (vdkOmega_rowAct (x i j h c) (Multiplicative.ofAdd (Pi.single k b))) =
      vdkOmegaSet_alpha X (vdkParPres_inr (x i j h c)) *
        ρ (Multiplicative.ofAdd (Pi.single k b)) *
          (vdkOmegaSet_alpha X (vdkParPres_inr (x i j h c)))⁻¹

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_RowRel

/-- The generator relations give the lift condition at every `g : St_n(R)`. -/
theorem vdkOmegaSet_compatAt_all
    (ρ : Multiplicative (Fin n → R) →* Equiv.Perm (vdkParPres_Tilde n R × X))
    (hrel : vdkOmegaSet_RowRel X ρ) (g : St n R) :
    vdkOmegaSet_CompatAt vdkOmega_rowAct ρ ((vdkOmegaSet_alpha X).comp vdkParPres_inr) g := by
  have hgen : ∀ gen : SteinbergGenerator (Fin n) R,
      (PresentedGroup.of gen : St n R) ∈ vdkOmegaSet_compatSubgroup vdkOmega_rowAct ρ
        ((vdkOmegaSet_alpha X).comp vdkParPres_inr) := by
    rintro ⟨i, j, hij, c⟩
    exact vdkOmegaSet_compatAt_of_single vdkOmega_rowAct ρ
      ((vdkOmegaSet_alpha X).comp vdkParPres_inr) (x i j hij c) (hrel i j hij c)
  exact PresentedGroup.generated_by _ _ hgen g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_compatAt_all

/-- **The `β`.**  The action of the opposite parabolic `P̃⁻` glued from `ρ` and from `α`
restricted to `St_n(R)`. -/
def vdkOmegaSet_beta
    (ρ : Multiplicative (Fin n → R) →* Equiv.Perm (vdkParPres_Tilde n R × X))
    (hall : ∀ g : St n R,
      vdkOmegaSet_CompatAt vdkOmega_rowAct ρ ((vdkOmegaSet_alpha X).comp vdkParPres_inr) g) :
    vdkOmega_TildeMinus n R →* Equiv.Perm (vdkParPres_Tilde n R × X) :=
  SemidirectProduct.lift ρ ((vdkOmegaSet_alpha X).comp vdkParPres_inr)
    (vdkOmegaSet_lift_of_compatAt vdkOmega_rowAct ρ _ hall)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_beta

variable (ρ : Multiplicative (Fin n → R) →* Equiv.Perm (vdkParPres_Tilde n R × X))
  (hall : ∀ g : St n R,
    vdkOmegaSet_CompatAt vdkOmega_rowAct ρ ((vdkOmegaSet_alpha X).comp vdkParPres_inr) g)

theorem vdkOmegaSet_beta_inr (g : St n R) :
    vdkOmegaSet_beta X ρ hall (vdkOmega_inrMinus g) = vdkOmegaSet_alpha X (vdkParPres_inr g) :=
  SemidirectProduct.lift_inr ρ ((vdkOmegaSet_alpha X).comp vdkParPres_inr)
    (vdkOmegaSet_lift_of_compatAt vdkOmega_rowAct ρ _ hall) g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_beta_inr

/-- **`Agree`, for free.**  `α` and `β` agree on `St_n(R)`. -/
theorem vdkOmegaSet_agree :
    vdkOmega_Agree (vdkOmegaSet_alpha X) (vdkOmegaSet_beta X ρ hall) := by
  intro g
  exact (vdkOmegaSet_beta_inr X ρ hall g).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_agree

/-- The row part of `β` is `ρ`. -/
theorem vdkOmegaSet_rv_beta (w : Fin n → R) :
    vdkOmega_rv (vdkOmegaSet_beta X ρ hall) w = ρ (Multiplicative.ofAdd w) :=
  SemidirectProduct.lift_inl ρ ((vdkOmegaSet_alpha X).comp vdkParPres_inr)
    (vdkOmegaSet_lift_of_compatAt vdkOmega_rowAct ρ _ hall) (Multiplicative.ofAdd w)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_rv_beta

end GroupApproximation.BooneHigman.Metabelian.ElemFP
