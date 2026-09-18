import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWeylAlg
import GroupApproximation.Meta.AxiomGuard

/-!
# The Weyl check of `σ`, part 2: Weyl-element conjugation identities

Lane `bh-met-93d`.  Two indices `m ≠ L` with a third index `n`, `W = w_mL(-1)`,
`x' t = x_Lm(t)`, `x t = x_mL(t)`.  Over any commutative ring:

* `k2PolyNagaoWeyl_W_conj`: `W x'(t) W⁻¹ = x(-t)`; `k2PolyNagaoWeyl_W_inv_conj`:
  `W⁻¹ x'(t) W = x(-t)`;
* `k2PolyNagaoWeyl_w_conj_x`: `w(u) x(s) w(u)⁻¹ = x'(-(u⁻¹ s u⁻¹))`;
* `k2PolyNagaoWeyl_h_conj`: `h(u) x'(t) h(u)⁻¹ = x'(u⁻¹ t u⁻¹)`;
* `k2PolyNagaoWeyl_middle`: `W⁻¹ x'(-u) W x'(-u⁻¹) W = h(u) x'(u)`.

Over a field: `k2PolyNagaoWeyl_field_w_conj_h`: `w(1) h(u) w(1)⁻¹ = h(u⁻¹)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_inv)

variable {I : Type} [Fintype I] [DecidableEq I]

section CommRing

variable {R : Type*} [CommRing R] {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)

include hmn hLn

/-- `W x'(t) W⁻¹ = x(-t)`. -/
theorem k2PolyNagaoWeyl_W_conj (t : R) :
    w m L hmL (-1 : Rˣ) * x L m hmL.symm t * (w m L hmL (-1 : Rˣ))⁻¹ = x m L hmL (-t) := by
  rw [k2PolyDeg_w_conj_self_symm_eq m L n hmL hmn hLn]
  exact congrArg (x m L hmL) (by rw [Units.val_neg, Units.val_one]; ring)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_W_conj

/-- `W⁻¹ x'(t) W = x(-t)`. -/
theorem k2PolyNagaoWeyl_W_inv_conj (t : R) :
    (w m L hmL (-1 : Rˣ))⁻¹ * x L m hmL.symm t * w m L hmL (-1 : Rˣ) = x m L hmL (-t) := by
  rw [w_inv m L hmL (-1 : Rˣ), neg_neg, ← w_inv m L hmL (1 : Rˣ),
    k2PolyDeg_w_conj_self_symm_eq m L n hmL hmn hLn]
  exact congrArg (x m L hmL) (by rw [Units.val_one, one_mul, mul_one])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_W_inv_conj

/-- `w(u) x(s) w(u)⁻¹ = x'(-(u⁻¹ s u⁻¹))`. -/
theorem k2PolyNagaoWeyl_w_conj_x (u : Rˣ) (s : R) :
    w m L hmL u * x m L hmL s * (w m L hmL u)⁻¹ =
      x L m hmL.symm (-(((u⁻¹ : Rˣ) : R) * s * ((u⁻¹ : Rˣ) : R))) := by
  have e := k2PolyDeg_w_conj_self_symm_eq m L n hmL hmn hLn (-u)
    (-(((u⁻¹ : Rˣ) : R) * s * ((u⁻¹ : Rˣ) : R)))
  have hU : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := Units.mul_inv u
  have hc : -(((-u : Rˣ) : R) * -(((u⁻¹ : Rˣ) : R) * s * ((u⁻¹ : Rˣ) : R)) *
      ((-u : Rˣ) : R)) = s := by
    rw [Units.val_neg]
    linear_combination s * ((u : R) * ((u⁻¹ : Rˣ) : R) + 1) * hU
  rw [← w_inv, inv_inv, hc] at e
  rw [← e]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_w_conj_x

/-- `h(u) x'(t) h(u)⁻¹ = x'(u⁻¹ t u⁻¹)`. -/
theorem k2PolyNagaoWeyl_h_conj (u : Rˣ) (t : R) :
    h m L hmL u * x L m hmL.symm t * (h m L hmL u)⁻¹ =
      x L m hmL.symm (((u⁻¹ : Rˣ) : R) * t * ((u⁻¹ : Rˣ) : R)) := by
  have e : h m L hmL u * x L m hmL.symm t * (h m L hmL u)⁻¹ =
      w m L hmL u * (w m L hmL (-1 : Rˣ) * x L m hmL.symm t * (w m L hmL (-1 : Rˣ))⁻¹) *
        (w m L hmL u)⁻¹ := by
    rw [show h m L hmL u = w m L hmL u * w m L hmL (-1 : Rˣ) from rfl]
    group
  rw [e, k2PolyNagaoWeyl_W_conj hmL hmn hLn, k2PolyNagaoWeyl_w_conj_x hmL hmn hLn]
  exact congrArg (x L m hmL.symm) (by ring)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_h_conj

/-- The middle identity `W⁻¹ x'(-u) W x'(-u⁻¹) W = h(u) x'(u)`. -/
theorem k2PolyNagaoWeyl_middle (u : Rˣ) :
    (w m L hmL (-1 : Rˣ))⁻¹ * x L m hmL.symm (-(u : R)) * w m L hmL (-1 : Rˣ) *
        x L m hmL.symm (-((u⁻¹ : Rˣ) : R)) * w m L hmL (-1 : Rˣ) =
      h m L hmL u * x L m hmL.symm (u : R) := by
  have e1 : (w m L hmL (-1 : Rˣ))⁻¹ * x L m hmL.symm (-(u : R)) * w m L hmL (-1 : Rˣ) =
      x m L hmL (u : R) := by
    rw [k2PolyNagaoWeyl_W_inv_conj hmL hmn hLn, neg_neg]
  have e3 : x L m hmL.symm (u : R) =
      (w m L hmL (-1 : Rˣ))⁻¹ * x m L hmL (-(u : R)) * w m L hmL (-1 : Rˣ) := by
    rw [← k2PolyNagaoWeyl_W_conj hmL hmn hLn]
    group
  have hw : h m L hmL u = x m L hmL (u : R) * x L m hmL.symm (-((u⁻¹ : Rˣ) : R)) *
      x m L hmL (u : R) * w m L hmL (-1 : Rˣ) := rfl
  rw [e1, hw, e3, x_neg m L hmL (u : R)]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_middle

end CommRing

end GroupApproximation.BooneHigman.Metabelian.ElemFP
