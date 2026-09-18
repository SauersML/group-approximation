import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Row actions from equivariant bijections, part 1: coordinates on `N ⋊ G`

Lane `bh-met-93g`.  Generic group theory, unconditional.

Every element of `N ⋊[φ] G` is uniquely `inr g * inl u`.  Write `g = p.right` and
`u = vdkOmegaRho_coord p`.  Left multiplication by `inr g'` changes `g` to `g' * g` and leaves
`u` unchanged (`vdkOmegaRho_coord_inr_mul`).

So for two semidirect products `N ⋊[φ] G` and `N' ⋊[φ'] G` with the same `G`, a bijection
`θ : N × X ≃ N' × X'` of `G`-orbit spaces and a map `σ : N × X → G` give an explicit bijection

  `vdkOmegaRho_equiv φ φ' θ σ : (N ⋊[φ] G) × X ≃ (N' ⋊[φ'] G) × X'`,
  `(inr g * inl u, x) ↦ (inr (g * σ (u, x)) * inl (θ (u, x)).1, (θ (u, x)).2)`.

It commutes with left multiplication by every `inr g` (`vdkOmegaRho_fwd_inr_mul`), i.e. it is
`G`-equivariant.  Every `G`-equivariant bijection has this form, but only this direction is
used or formalized.

`vdkOmegaRho_left A Y` is the left multiplication action of a group `A` on `A × Y`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section Left

variable (A : Type*) [Group A] (Y : Type*)

/-- Left multiplication by `a` on the first factor of `A × Y`. -/
def vdkOmegaRho_leftPerm (a : A) : Equiv.Perm (A × Y) where
  toFun ω := (a * ω.1, ω.2)
  invFun ω := (a⁻¹ * ω.1, ω.2)
  left_inv ω := Prod.ext (inv_mul_cancel_left a ω.1) rfl
  right_inv ω := Prod.ext (mul_inv_cancel_left a ω.1) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_leftPerm

/-- The left multiplication action of `A` on `A × Y`. -/
def vdkOmegaRho_left : A →* Equiv.Perm (A × Y) where
  toFun := vdkOmegaRho_leftPerm A Y
  map_one' := Equiv.ext fun ω ↦ Prod.ext (one_mul ω.1) rfl
  map_mul' p q := Equiv.ext fun ω ↦ Prod.ext (mul_assoc p q ω.1) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_left

end Left

section Coord

variable {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}

/-- The `N`-coordinate of `p = inr p.right * inl u`, namely `u`. -/
def vdkOmegaRho_coord (p : N ⋊[φ] G) : N :=
  ((SemidirectProduct.inr p.right)⁻¹ * p).left

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_coord

theorem vdkOmegaRho_right_inr_mul_inl (g : G) (u : N) :
    ((SemidirectProduct.inr g : N ⋊[φ] G) * SemidirectProduct.inl u).right = g := by
  rw [SemidirectProduct.mul_right, SemidirectProduct.right_inr, SemidirectProduct.right_inl,
    mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_right_inr_mul_inl

theorem vdkOmegaRho_coord_enc (g : G) (u : N) :
    vdkOmegaRho_coord ((SemidirectProduct.inr g : N ⋊[φ] G) * SemidirectProduct.inl u) = u := by
  rw [vdkOmegaRho_coord, vdkOmegaRho_right_inr_mul_inl, inv_mul_cancel_left,
    SemidirectProduct.left_inl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_coord_enc

theorem vdkOmegaRho_enc_coord (p : N ⋊[φ] G) :
    SemidirectProduct.inr p.right * SemidirectProduct.inl (vdkOmegaRho_coord p) = p := by
  have hy : ((SemidirectProduct.inr p.right)⁻¹ * p : N ⋊[φ] G).right = 1 := by
    rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, SemidirectProduct.right_inr,
      inv_mul_cancel]
  have e := SemidirectProduct.inl_left_mul_inr_right
    ((SemidirectProduct.inr p.right)⁻¹ * p : N ⋊[φ] G)
  rw [hy, map_one, mul_one] at e
  rw [vdkOmegaRho_coord, e, mul_inv_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_enc_coord

theorem vdkOmegaRho_coord_inr_mul (g : G) (p : N ⋊[φ] G) :
    vdkOmegaRho_coord (SemidirectProduct.inr g * p) = vdkOmegaRho_coord p := by
  have e : ((SemidirectProduct.inr (g * p.right))⁻¹ * (SemidirectProduct.inr g * p) :
      N ⋊[φ] G) = (SemidirectProduct.inr p.right)⁻¹ * p := by
    rw [map_mul]
    group
  rw [vdkOmegaRho_coord, vdkOmegaRho_coord, SemidirectProduct.mul_right,
    SemidirectProduct.right_inr, e]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_coord_inr_mul

end Coord

section Equiv

variable {N G N' : Type*} [Group N] [Group G] [Group N']
  {φ : G →* MulAut N} {φ' : G →* MulAut N'} {X X' : Type*}

variable (φ) in
/-- `(g, (u, x)) ↦ (inr g * inl u, x)`. -/
def vdkOmegaRho_enc (g : G) (c : N × X) : (N ⋊[φ] G) × X :=
  (SemidirectProduct.inr g * SemidirectProduct.inl c.1, c.2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_enc

/-- `(inr g * inl u, x) ↦ (u, x)`, the projection to the `G`-orbit space `N × X`. -/
def vdkOmegaRho_dec (ω : (N ⋊[φ] G) × X) : N × X :=
  (vdkOmegaRho_coord ω.1, ω.2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_dec

theorem vdkOmegaRho_right_enc (g : G) (c : N × X) : (vdkOmegaRho_enc φ g c).1.right = g :=
  vdkOmegaRho_right_inr_mul_inl g c.1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_right_enc

theorem vdkOmegaRho_dec_enc (g : G) (c : N × X) : vdkOmegaRho_dec (vdkOmegaRho_enc φ g c) = c :=
  Prod.ext (vdkOmegaRho_coord_enc g c.1) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_dec_enc

theorem vdkOmegaRho_enc_dec (ω : (N ⋊[φ] G) × X) :
    vdkOmegaRho_enc φ ω.1.right (vdkOmegaRho_dec ω) = ω :=
  Prod.ext (vdkOmegaRho_enc_coord ω.1) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_enc_dec

theorem vdkOmegaRho_dec_inr_mul (g : G) (p : N ⋊[φ] G) (x : X) :
    vdkOmegaRho_dec (SemidirectProduct.inr g * p, x) = vdkOmegaRho_dec (p, x) :=
  Prod.ext (vdkOmegaRho_coord_inr_mul g p) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_dec_inr_mul

theorem vdkOmegaRho_enc_mul (g s : G) (c : N × X) :
    vdkOmegaRho_enc φ (g * s) c =
      (SemidirectProduct.inr g * (vdkOmegaRho_enc φ s c).1, (vdkOmegaRho_enc φ s c).2) := by
  refine Prod.ext ?_ rfl
  show (SemidirectProduct.inr (g * s) * SemidirectProduct.inl c.1 : N ⋊[φ] G) =
    SemidirectProduct.inr g * (SemidirectProduct.inr s * SemidirectProduct.inl c.1)
  rw [map_mul, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_enc_mul

variable (θ : N × X ≃ N' × X') (σ : N × X → G)

variable (φ φ') in
/-- The forward map `(inr g * inl u, x) ↦ (inr (g * σ (u, x)) * inl (θ (u, x)).1, (θ (u, x)).2)`.
-/
def vdkOmegaRho_fwd (ω : (N ⋊[φ] G) × X) : (N' ⋊[φ'] G) × X' :=
  vdkOmegaRho_enc φ' (ω.1.right * σ (vdkOmegaRho_dec ω)) (θ (vdkOmegaRho_dec ω))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_fwd

variable (φ φ') in
/-- The backward map, inverse to `vdkOmegaRho_fwd`. -/
def vdkOmegaRho_bwd (ω' : (N' ⋊[φ'] G) × X') : (N ⋊[φ] G) × X :=
  vdkOmegaRho_enc φ (ω'.1.right * (σ (θ.symm (vdkOmegaRho_dec ω')))⁻¹)
    (θ.symm (vdkOmegaRho_dec ω'))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_bwd

theorem vdkOmegaRho_bwd_fwd (ω : (N ⋊[φ] G) × X) :
    vdkOmegaRho_bwd φ φ' θ σ (vdkOmegaRho_fwd φ φ' θ σ ω) = ω := by
  simp only [vdkOmegaRho_bwd, vdkOmegaRho_fwd, vdkOmegaRho_dec_enc, vdkOmegaRho_right_enc,
    Equiv.symm_apply_apply, mul_inv_cancel_right, vdkOmegaRho_enc_dec]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_bwd_fwd

theorem vdkOmegaRho_fwd_bwd (ω' : (N' ⋊[φ'] G) × X') :
    vdkOmegaRho_fwd φ φ' θ σ (vdkOmegaRho_bwd φ φ' θ σ ω') = ω' := by
  simp only [vdkOmegaRho_bwd, vdkOmegaRho_fwd, vdkOmegaRho_dec_enc, vdkOmegaRho_right_enc,
    Equiv.apply_symm_apply, inv_mul_cancel_right, vdkOmegaRho_enc_dec]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_fwd_bwd

variable (φ φ') in
/-- **The explicit bijection** `(N ⋊[φ] G) × X ≃ (N' ⋊[φ'] G) × X'`. -/
def vdkOmegaRho_equiv : (N ⋊[φ] G) × X ≃ (N' ⋊[φ'] G) × X' where
  toFun := vdkOmegaRho_fwd φ φ' θ σ
  invFun := vdkOmegaRho_bwd φ φ' θ σ
  left_inv ω := vdkOmegaRho_bwd_fwd θ σ ω
  right_inv ω' := vdkOmegaRho_fwd_bwd θ σ ω'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_equiv

/-- **Equivariance.**  The forward map commutes with left multiplication by `inr g`. -/
theorem vdkOmegaRho_fwd_inr_mul (g : G) (p : N ⋊[φ] G) (x : X) :
    vdkOmegaRho_fwd φ φ' θ σ (SemidirectProduct.inr g * p, x) =
      (SemidirectProduct.inr g * (vdkOmegaRho_fwd φ φ' θ σ (p, x)).1,
        (vdkOmegaRho_fwd φ φ' θ σ (p, x)).2) := by
  rw [vdkOmegaRho_fwd, vdkOmegaRho_fwd, vdkOmegaRho_dec_inr_mul]
  simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inr]
  rw [mul_assoc g, vdkOmegaRho_enc_mul g]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_fwd_inr_mul

/-- Equivariance, in the form used to get `vdkOmega_Agree`. -/
theorem vdkOmegaRho_bwd_inr_mul_fwd (g : G) (p : N ⋊[φ] G) (x : X) :
    vdkOmegaRho_bwd φ φ' θ σ (SemidirectProduct.inr g * (vdkOmegaRho_fwd φ φ' θ σ (p, x)).1,
      (vdkOmegaRho_fwd φ φ' θ σ (p, x)).2) = (SemidirectProduct.inr g * p, x) := by
  rw [← vdkOmegaRho_fwd_inr_mul, vdkOmegaRho_bwd_fwd]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_bwd_inr_mul_fwd

end Equiv

end GroupApproximation.BooneHigman.Metabelian.ElemFP
