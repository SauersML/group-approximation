import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJRedMain
import GroupApproximation.Meta.AxiomGuard

/-!
# The odd-`p` Nagao torus, part 1: the twisted torus `T(α, β)`

Lane `bh-met-94b`.  Write `t_mi(γ) = C(h_mi(γ))`, `t_mL(β) = C(h_mL(β))` (for a third index
`i`), `W = w_mL(-1)` and `x'(f) = x_Lm(f)`.  Put `T(α, β) = t_mL(β)⁻¹ t_mi(α β)`.  Then

* `k2PolyNagaoTorus_T_mul_x`: `T(α, β) x'(f) = x'(β α⁻¹ f) T(α, β)`;
* `k2PolyNagaoTorus_W_conj_T`: `W⁻¹ T(α, β) W = T(β, α)`.

These two identities are exactly what is needed to push `T` through the Euclidean
normal form `σ₀` (part 2).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl
  (w h w_inv w_conj_x_col_i w_conj_x_col_j)

variable {I : Type} [Fintype I] [DecidableEq I]

section CommRing

variable {R : Type*} [CommRing R]

/-- `h_mi(u) x_Lm(t) h_mi(u)⁻¹ = x_Lm(t u⁻¹)` for a third index `i`. -/
theorem k2PolyNagaoTorus_h_conj_x {m L i : I} (hmL : m ≠ L) (hmi : m ≠ i) (hLi : L ≠ i)
    (u : Rˣ) (t : R) :
    h m i hmi u * x L m hmL.symm t * (h m i hmi u)⁻¹ =
      x L m hmL.symm (t * ((u⁻¹ : Rˣ) : R)) := by
  have e : h m i hmi u * x L m hmL.symm t * (h m i hmi u)⁻¹ =
      w m i hmi u * (w m i hmi (-1 : Rˣ) * x L m hmL.symm t * (w m i hmi (-1 : Rˣ))⁻¹) *
        (w m i hmi u)⁻¹ := by
    rw [show h m i hmi u = w m i hmi u * w m i hmi (-1 : Rˣ) from rfl]
    group
  rw [e, w_conj_x_col_i m i L hmi hmL.symm hLi (-1 : Rˣ) t,
    w_conj_x_col_j m i L hmi hmL.symm hLi u]
  exact congrArg (x L m hmL.symm) (by simp only [Units.val_neg, Units.val_one]; ring)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_h_conj_x

end CommRing

section Field

variable {F : Type*} [Field F]

/-- Over a field, `w_mL(1) h_mi(c) w_mL(1)⁻¹ = h_mL(c)⁻¹ h_mi(c)`. -/
theorem k2PolyNagaoTorus_field_w_conj_h {m L i : I} (hmL : m ≠ L) (hmi : m ≠ i)
    (hLi : L ≠ i) (c : Fˣ) :
    w m L hmL (1 : Fˣ) * h m i hmi c * (w m L hmL (1 : Fˣ))⁻¹ =
      (h m L hmL c)⁻¹ * h m i hmi c := by
  have e := FieldK2.h_conj_w m L i hmL hmi hLi c 1
  rw [mul_one c] at e
  have hh : h m L hmL c = w m L hmL c * (w m L hmL (1 : Fˣ))⁻¹ := by
    rw [w_inv]
    rfl
  rw [hh, ← e]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_field_w_conj_h

end Field

section GroupLemmas

/-- If `B X B⁻¹ = Y` and `A Y = Z A`, then `(A B) X = Z (A B)`. -/
theorem k2PolyNagaoTorus_grp_comm {G : Type*} [Group G] {A B X Y Z : G}
    (h1 : B * X * B⁻¹ = Y) (h2 : A * Y = Z * A) : A * B * X = Z * (A * B) := by
  subst h1
  calc A * B * X = A * (B * X * B⁻¹) * B := by group
    _ = Z * A * B := by rw [h2]
    _ = Z * (A * B) := by group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_grp_comm

/-- `f(β⁻¹)⁻¹ (f(α β)⁻¹ M) = f(α)⁻¹ M` for a hom `f` out of a commutative group. -/
theorem k2PolyNagaoTorus_hom_aux {G H : Type*} [CommGroup G] [Group H] (f : G →* H)
    (α β : G) (M : H) : (f β⁻¹)⁻¹ * ((f (α * β))⁻¹ * M) = (f α)⁻¹ * M := by
  simp only [map_inv, map_mul]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_hom_aux

end GroupLemmas

/-- The twisted torus element `T(α, β) = t_mL(β)⁻¹ t_mi(α β)`. -/
noncomputable def k2PolyNagaoTorus_T (p : ℕ) [Fact p.Prime] {m L i : I} (hmL : m ≠ L)
    (hmi : m ≠ i) (hLi : L ≠ i) (α β : (ZMod p)ˣ) : SteinbergGroup I (Polynomial (ZMod p)) :=
  (k2PolyDeg_torus p m L i hmL hmi hLi β)⁻¹ * k2PolyDeg_torus p m i L hmi hmL hLi.symm (α * β)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_T

variable {p : ℕ} [Fact p.Prime] {m L i : I} (hmL : m ≠ L) (hmi : m ≠ i) (hLi : L ≠ i)

/-- `t_mi(γ) x'(f) t_mi(γ)⁻¹ = x'(f γ⁻¹)`. -/
theorem k2PolyNagaoTorus_tmi_conj_x (γ : (ZMod p)ˣ) (f : Polynomial (ZMod p)) :
    k2PolyDeg_torus p m i L hmi hmL hLi.symm γ * x L m hmL.symm f *
        (k2PolyDeg_torus p m i L hmi hmL hLi.symm γ)⁻¹ =
      x L m hmL.symm (f * Polynomial.C ((γ⁻¹ : (ZMod p)ˣ) : ZMod p)) := by
  rw [k2PolyDeg_torus_apply]
  exact k2PolyNagaoTorus_h_conj_x hmL hmi hLi _ f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_tmi_conj_x

/-- `W⁻¹ t_mi(c) W = t_mL(c)⁻¹ t_mi(c)`. -/
theorem k2PolyNagaoTorus_W_conj_tmi (c : (ZMod p)ˣ) :
    (w m L hmL (-1 : (Polynomial (ZMod p))ˣ))⁻¹ * k2PolyDeg_torus p m i L hmi hmL hLi.symm c *
        w m L hmL (-1 : (Polynomial (ZMod p))ˣ) =
      (k2PolyDeg_torus p m L i hmL hmi hLi c)⁻¹ * k2PolyDeg_torus p m i L hmi hmL hLi.symm c := by
  have hW : ringMap (Polynomial.C : ZMod p →+* Polynomial (ZMod p))
      (w m L hmL (1 : (ZMod p)ˣ)) = (w m L hmL (-1 : (Polynomial (ZMod p))ˣ))⁻¹ := by
    rw [k2PolyDeg_ringMap_w, map_one, w_inv, neg_neg]
  have e := congrArg (ringMap (Polynomial.C : ZMod p →+* Polynomial (ZMod p)))
    (k2PolyNagaoTorus_field_w_conj_h hmL hmi hLi c)
  simp only [map_mul, map_inv] at e
  rw [hW, inv_inv] at e
  rw [k2PolyNagaoWeyl_torus_eq hmi hmL hLi.symm, k2PolyNagaoWeyl_torus_eq hmL hmi hLi]
  exact e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_W_conj_tmi

/-- `T(α, β) x'(f) = x'(β α⁻¹ f) T(α, β)`. -/
theorem k2PolyNagaoTorus_T_mul_x (α β : (ZMod p)ˣ) (f : Polynomial (ZMod p)) :
    k2PolyNagaoTorus_T p hmL hmi hLi α β * x L m hmL.symm f =
      x L m hmL.symm (Polynomial.C ((β * α⁻¹ : (ZMod p)ˣ) : ZMod p) * f) *
        k2PolyNagaoTorus_T p hmL hmi hLi α β := by
  have hu : β⁻¹⁻¹ * (α * β)⁻¹ * β⁻¹⁻¹ = β * α⁻¹ := by
    rw [inv_inv, mul_inv_rev, mul_inv_cancel_left]
    exact mul_comm _ _
  have hc : Polynomial.C ((β⁻¹⁻¹ : (ZMod p)ˣ) : ZMod p) *
      (f * Polynomial.C (((α * β)⁻¹ : (ZMod p)ˣ) : ZMod p)) *
        Polynomial.C ((β⁻¹⁻¹ : (ZMod p)ˣ) : ZMod p) =
      Polynomial.C ((β * α⁻¹ : (ZMod p)ˣ) : ZMod p) * f := by
    rw [← hu]
    simp only [Units.val_mul, map_mul]
    ring
  have e1 := k2PolyNagaoTorus_tmi_conj_x hmL hmi hLi (α * β) f
  have h2 : (k2PolyDeg_torus p m L i hmL hmi hLi β)⁻¹ *
      x L m hmL.symm (f * Polynomial.C (((α * β)⁻¹ : (ZMod p)ˣ) : ZMod p)) =
      x L m hmL.symm (Polynomial.C ((β * α⁻¹ : (ZMod p)ˣ) : ZMod p) * f) *
        (k2PolyDeg_torus p m L i hmL hmi hLi β)⁻¹ := by
    rw [← map_inv (k2PolyDeg_torus p m L i hmL hmi hLi) β,
      k2PolyNagaoWeyl_torus_mul_x hmL hmi hLi β⁻¹, hc]
  rw [k2PolyNagaoTorus_T]
  exact k2PolyNagaoTorus_grp_comm e1 h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_T_mul_x

/-- `W⁻¹ T(α, β) W = T(β, α)`. -/
theorem k2PolyNagaoTorus_W_conj_T (α β : (ZMod p)ˣ) :
    (w m L hmL (-1 : (Polynomial (ZMod p))ˣ))⁻¹ * k2PolyNagaoTorus_T p hmL hmi hLi α β *
        w m L hmL (-1 : (Polynomial (ZMod p))ˣ) = k2PolyNagaoTorus_T p hmL hmi hLi β α := by
  have e : (w m L hmL (-1 : (Polynomial (ZMod p))ˣ))⁻¹ * k2PolyNagaoTorus_T p hmL hmi hLi α β *
        w m L hmL (-1 : (Polynomial (ZMod p))ˣ) =
      ((w m L hmL (-1 : (Polynomial (ZMod p))ˣ))⁻¹ * k2PolyDeg_torus p m L i hmL hmi hLi β *
          w m L hmL (-1 : (Polynomial (ZMod p))ˣ))⁻¹ *
        ((w m L hmL (-1 : (Polynomial (ZMod p))ˣ))⁻¹ *
          k2PolyDeg_torus p m i L hmi hmL hLi.symm (α * β) *
            w m L hmL (-1 : (Polynomial (ZMod p))ˣ)) := by
    rw [k2PolyNagaoTorus_T]
    group
  rw [e, k2PolyNagaoWeyl_W_conj_torus hmL hmi hLi β,
    k2PolyNagaoTorus_W_conj_tmi hmL hmi hLi (α * β), k2PolyNagaoTorus_T, mul_comm β α]
  exact k2PolyNagaoTorus_hom_aux (k2PolyDeg_torus p m L i hmL hmi hLi) α β _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_W_conj_T

end GroupApproximation.BooneHigman.Metabelian.ElemFP
