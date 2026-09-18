import GroupApproximation.BooneHigman.Metabelian.VdKOmegaRhoCoord
import GroupApproximation.Meta.AxiomGuard

/-!
# `vdkOmegaFree`, part 1: every `G`-equivariant bijection is a `vdkOmegaRho_equiv`

Lane `bh-met-93j`.  Generic group theory, unconditional.

Let `Ψ : (N ⋊[φ] G) × X ≃ (N' ⋊[φ'] G) × X'` commute with left multiplication by every
`inr g` (`vdkOmegaFree_Equivariant`).  Read off

* `σ (u, x) = (Ψ (inl u, x)).1.right` (`vdkOmegaFree_sigma`),
* `θ (u, x) = dec (Ψ (inl u, x))` (`vdkOmegaFree_theta`, a bijection `N × X ≃ N' × X'`).

Then `vdkOmegaRho_equiv φ φ' θ σ = Ψ` (`vdkOmegaFree_equiv_eq`).  This is the converse
direction that `VdKOmegaRhoCoord` states but does not formalize.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section Decomp

variable {N G N' : Type*} [Group N] [Group G] [Group N']
  {φ : G →* MulAut N} {φ' : G →* MulAut N'} {X X' : Type*}

/-- `F` commutes with left multiplication by every `inr g` on the first factor. -/
def vdkOmegaFree_Equivariant (F : (N ⋊[φ] G) × X → (N' ⋊[φ'] G) × X') : Prop :=
  ∀ (g : G) (p : N ⋊[φ] G) (x : X),
    F (SemidirectProduct.inr g * p, x) = (SemidirectProduct.inr g * (F (p, x)).1, (F (p, x)).2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Equivariant

theorem vdkOmegaFree_equivariant_symm (Ψ : (N ⋊[φ] G) × X ≃ (N' ⋊[φ'] G) × X')
    (hΨ : vdkOmegaFree_Equivariant Ψ) : vdkOmegaFree_Equivariant Ψ.symm := by
  intro g q x'
  have hy : Ψ ((Ψ.symm (q, x')).1, (Ψ.symm (q, x')).2) = (q, x') :=
    Ψ.apply_symm_apply (q, x')
  rw [Equiv.symm_apply_eq, hΨ g (Ψ.symm (q, x')).1 (Ψ.symm (q, x')).2]
  exact (congrArg (fun y : (N' ⋊[φ'] G) × X' ↦ (SemidirectProduct.inr g * y.1, y.2)) hy).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_equivariant_symm

theorem vdkOmegaFree_coord_inl (u : N) :
    vdkOmegaRho_coord (SemidirectProduct.inl u : N ⋊[φ] G) = u := by
  have e := vdkOmegaRho_coord_enc (φ := φ) (1 : G) u
  rwa [map_one, one_mul] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_coord_inl

theorem vdkOmegaFree_inl_coord (p : N ⋊[φ] G) :
    (SemidirectProduct.inl (vdkOmegaRho_coord p) : N ⋊[φ] G) =
      (SemidirectProduct.inr p.right)⁻¹ * p :=
  eq_inv_mul_of_mul_eq (vdkOmegaRho_enc_coord p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_inl_coord

/-- For equivariant `F`, `dec ∘ F` only depends on `dec`. -/
theorem vdkOmegaFree_dec_inl_dec (F : (N ⋊[φ] G) × X → (N' ⋊[φ'] G) × X')
    (hF : vdkOmegaFree_Equivariant F) (ω : (N ⋊[φ] G) × X) :
    vdkOmegaRho_dec (F ((SemidirectProduct.inl (vdkOmegaRho_dec ω).1 : N ⋊[φ] G),
      (vdkOmegaRho_dec ω).2)) = vdkOmegaRho_dec (F ω) := by
  have e1 : (SemidirectProduct.inl (vdkOmegaRho_coord ω.1) : N ⋊[φ] G) =
      SemidirectProduct.inr ω.1.right⁻¹ * ω.1 := by
    rw [map_inv]
    exact vdkOmegaFree_inl_coord ω.1
  have e : ((SemidirectProduct.inl (vdkOmegaRho_dec ω).1 : N ⋊[φ] G), (vdkOmegaRho_dec ω).2) =
      (SemidirectProduct.inr ω.1.right⁻¹ * ω.1, ω.2) := Prod.ext e1 rfl
  rw [e, hF ω.1.right⁻¹ ω.1 ω.2]
  exact vdkOmegaRho_dec_inr_mul _ _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_dec_inl_dec

variable (Ψ : (N ⋊[φ] G) × X ≃ (N' ⋊[φ'] G) × X')

/-- `σ (u, x) = (Ψ (inl u, x)).1.right`. -/
def vdkOmegaFree_sigma (c : N × X) : G :=
  (Ψ ((SemidirectProduct.inl c.1 : N ⋊[φ] G), c.2)).1.right

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_sigma

/-- `θ (u, x) = dec (Ψ (inl u, x))`. -/
def vdkOmegaFree_thetaFun (c : N × X) : N' × X' :=
  vdkOmegaRho_dec (Ψ ((SemidirectProduct.inl c.1 : N ⋊[φ] G), c.2))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_thetaFun

/-- `θ⁻¹ (u', x') = dec (Ψ⁻¹ (inl u', x'))`. -/
def vdkOmegaFree_thetaInv (c : N' × X') : N × X :=
  vdkOmegaRho_dec (Ψ.symm ((SemidirectProduct.inl c.1 : N' ⋊[φ'] G), c.2))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_thetaInv

variable {Ψ} (hΨ : vdkOmegaFree_Equivariant Ψ)

include hΨ in
theorem vdkOmegaFree_thetaInv_thetaFun (c : N × X) :
    vdkOmegaFree_thetaInv Ψ (vdkOmegaFree_thetaFun Ψ c) = c := by
  have e := vdkOmegaFree_dec_inl_dec Ψ.symm (vdkOmegaFree_equivariant_symm Ψ hΨ)
    (Ψ ((SemidirectProduct.inl c.1 : N ⋊[φ] G), c.2))
  rw [Equiv.symm_apply_apply] at e
  exact e.trans (Prod.ext (vdkOmegaFree_coord_inl (φ := φ) c.1) rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_thetaInv_thetaFun

include hΨ in
theorem vdkOmegaFree_thetaFun_thetaInv (c : N' × X') :
    vdkOmegaFree_thetaFun Ψ (vdkOmegaFree_thetaInv Ψ c) = c := by
  have e := vdkOmegaFree_dec_inl_dec Ψ hΨ
    (Ψ.symm ((SemidirectProduct.inl c.1 : N' ⋊[φ'] G), c.2))
  rw [Equiv.apply_symm_apply] at e
  exact e.trans (Prod.ext (vdkOmegaFree_coord_inl (φ := φ') c.1) rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_thetaFun_thetaInv

include hΨ in
/-- **The `θ` read off from `Ψ`**, a bijection of `G`-orbit spaces `N × X ≃ N' × X'`. -/
def vdkOmegaFree_theta : N × X ≃ N' × X' where
  toFun := vdkOmegaFree_thetaFun Ψ
  invFun := vdkOmegaFree_thetaInv Ψ
  left_inv c := vdkOmegaFree_thetaInv_thetaFun hΨ c
  right_inv c := vdkOmegaFree_thetaFun_thetaInv hΨ c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_theta

theorem vdkOmegaFree_enc_sigma_theta (c : N × X) :
    vdkOmegaRho_enc φ' (vdkOmegaFree_sigma Ψ c) (vdkOmegaFree_theta hΨ c) =
      Ψ ((SemidirectProduct.inl c.1 : N ⋊[φ] G), c.2) :=
  vdkOmegaRho_enc_dec (Ψ ((SemidirectProduct.inl c.1 : N ⋊[φ] G), c.2))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_enc_sigma_theta

/-- **The decomposition.**  `vdkOmegaRho_fwd` with the `θ`, `σ` read off from `Ψ` is `Ψ`. -/
theorem vdkOmegaFree_fwd_eq (ω : (N ⋊[φ] G) × X) :
    vdkOmegaRho_fwd φ φ' (vdkOmegaFree_theta hΨ) (vdkOmegaFree_sigma Ψ) ω = Ψ ω := by
  have e1 : Ψ ω = Ψ (SemidirectProduct.inr ω.1.right *
      (SemidirectProduct.inl (vdkOmegaRho_dec ω).1 : N ⋊[φ] G), (vdkOmegaRho_dec ω).2) :=
    congrArg Ψ (vdkOmegaRho_enc_dec ω).symm
  rw [vdkOmegaRho_fwd, e1, hΨ ω.1.right _ (vdkOmegaRho_dec ω).2,
    ← vdkOmegaFree_enc_sigma_theta hΨ (vdkOmegaRho_dec ω), ← vdkOmegaRho_enc_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_fwd_eq

theorem vdkOmegaFree_bwd_eq (ω' : (N' ⋊[φ'] G) × X') :
    vdkOmegaRho_bwd φ φ' (vdkOmegaFree_theta hΨ) (vdkOmegaFree_sigma Ψ) ω' = Ψ.symm ω' := by
  rw [Equiv.eq_symm_apply, ← vdkOmegaFree_fwd_eq hΨ, vdkOmegaRho_fwd_bwd]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_bwd_eq

/-- **Endpoint.**  Every `G`-equivariant bijection is a `vdkOmegaRho_equiv`. -/
theorem vdkOmegaFree_equiv_eq :
    vdkOmegaRho_equiv φ φ' (vdkOmegaFree_theta hΨ) (vdkOmegaFree_sigma Ψ) = Ψ :=
  Equiv.ext fun ω ↦ vdkOmegaFree_fwd_eq hΨ ω

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_equiv_eq

end Decomp

end GroupApproximation.BooneHigman.Metabelian.ElemFP
