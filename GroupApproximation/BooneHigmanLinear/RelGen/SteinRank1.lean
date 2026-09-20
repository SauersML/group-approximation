import GroupApproximation.BooneHigmanLinear.K2Poly.SymbolCentral
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# Stein's theorem, part 1: the rank-one identity over a commutative ring

Lane bh-pal-wire, k2-poly H.L3 (towards L–S Theorem 4.8). Over a commutative ring `R`, with a
third index `k ∉ {i, j}`:

* `cr_w_eq_alt`: `w_ij(u) = x_ji(-u⁻¹) x_ij(u) x_ji(-u⁻¹)`. This is the ring version of
  `ElemFP.FieldK2.w_eq_alt`, proved from `K2Poly.cr_w_conj_x_self(_symm)`.
* `cr_h_conj_self`: `h_ij(v) x_ij(r) h_ij(v)⁻¹ = x_ij(v r v)`.
* **`rank1_unit`**: for a unit `s` and a unit `u = 1 + s t`,

    `x_ji(t) x_ij(s) = x_ij(s u⁻¹) · ({-s, u⁻¹} h_ij(u⁻¹)) · x_ji(t u⁻¹)`,

  where `{a, b} = csym i j hij a b = h(ab) h(a)⁻¹ h(b)⁻¹`. This is the Steinberg-group form of the
  UDL decomposition of `[[1, s], [t, 1 + st]]`.

  The proof writes `x_ij(s) = x_ji(s⁻¹) w(s) x_ji(s⁻¹)` and
  `x_ji(u s⁻¹) = x_ij(s u⁻¹) w(v) x_ij(s u⁻¹)` with `v = -s u⁻¹`. It moves `x_ij(s u⁻¹)` past `w(s)` and uses
  `w(v) w(s) = h(v) h(-s)⁻¹ = {-s, u⁻¹} h(u⁻¹)`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_inv)
open GroupApproximation.BooneHigmanLinear.K2Poly (cr_w_conj_x_self cr_w_conj_x_self_symm
  cr_h_conj_split csym)

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

/-- `w_ij(u) = x_ji(-u⁻¹) x_ij(u) x_ji(-u⁻¹)`, over a commutative ring. -/
theorem cr_w_eq_alt (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) :
    w i j hij u = x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * x i j hij (u : R) *
      x j i hij.symm (-((u⁻¹ : Rˣ) : R)) := by
  have h1 : w i j hij u * x i j hij (u : R) * (w i j hij u)⁻¹ =
      x j i hij.symm (-((u⁻¹ : Rˣ) : R)) := by
    rw [cr_w_conj_x_self i j k hij hik hjk u, Units.inv_mul, one_mul]
  have h2 : w i j hij u * x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * (w i j hij u)⁻¹ =
      x i j hij (u : R) := by
    rw [cr_w_conj_x_self_symm i j k hij hik hjk u]
    congr 1
    linear_combination (u : R) * Units.mul_inv u
  have hy : x j i hij.symm (-((u⁻¹ : Rˣ) : R)) =
      (w i j hij u)⁻¹ * x i j hij (u : R) * w i j hij u := by
    rw [← h2]
    group
  have hw : w i j hij u =
      x i j hij (u : R) * x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * x i j hij (u : R) := rfl
  calc w i j hij u
      = (w i j hij u)⁻¹ * (x i j hij (u : R) * x j i hij.symm (-((u⁻¹ : Rˣ) : R)) *
          x i j hij (u : R)) * w i j hij u := by rw [← hw]; group
    _ = (w i j hij u)⁻¹ * (x i j hij (u : R) *
          (w i j hij u * x i j hij (u : R) * (w i j hij u)⁻¹) * x i j hij (u : R)) *
          w i j hij u := by rw [h1]
    _ = ((w i j hij u)⁻¹ * x i j hij (u : R) * w i j hij u) * x i j hij (u : R) *
          ((w i j hij u)⁻¹ * x i j hij (u : R) * w i j hij u) := by group
    _ = _ := by rw [← hy]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cr_w_eq_alt

/-- `h_ij(v) x_ij(r) h_ij(v)⁻¹ = x_ij(v r v)`, over a commutative ring. -/
theorem cr_h_conj_self (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (v : Rˣ) (r : R) :
    h i j hij v * x i j hij r * (h i j hij v)⁻¹ = x i j hij ((v : R) * r * (v : R)) := by
  rw [cr_h_conj_split, cr_w_conj_x_self i j k hij hik hjk (-1), cr_w_conj_x_self_symm i j k hij
    hik hjk v]
  congr 1
  simp only [inv_neg, inv_one, Units.val_neg, Units.val_one]
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cr_h_conj_self

/-- **The rank-one identity.** For units `s` and `u = 1 + s t`,
`x_ji(t) x_ij(s) = x_ij(s u⁻¹) · ({-s, u⁻¹} h_ij(u⁻¹)) · x_ji(t u⁻¹)`. -/
theorem rank1_unit (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (s u : Rˣ) (t : R)
    (hu : (u : R) = 1 + (s : R) * t) :
    x j i hij.symm t * x i j hij (s : R) =
      x i j hij ((s : R) * ((u⁻¹ : Rˣ) : R)) * (csym i j hij (-s) u⁻¹ * h i j hij u⁻¹) *
        x j i hij.symm (t * ((u⁻¹ : Rˣ) : R)) := by
  have Hs : (s : R) * ((s⁻¹ : Rˣ) : R) = 1 := Units.mul_inv s
  have Hs' : ((s⁻¹ : Rˣ) : R) * (s : R) = 1 := Units.inv_mul s
  have Hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := Units.mul_inv u
  have hvval : (((-s) * u⁻¹ : Rˣ) : R) = -((s : R) * ((u⁻¹ : Rˣ) : R)) := by
    rw [Units.val_mul, Units.val_neg, neg_mul]
  have hvinv : ((((-s) * u⁻¹)⁻¹ : Rˣ) : R) = -((u : R) * ((s⁻¹ : Rˣ) : R)) := by
    rw [mul_inv_rev, inv_inv, inv_neg, Units.val_mul, Units.val_neg, mul_neg]
  -- `x_ij(s) = x_ji(s⁻¹) w(s) x_ji(s⁻¹)`.
  have hx : x i j hij (s : R) =
      x j i hij.symm ((s⁻¹ : Rˣ) : R) * w i j hij s * x j i hij.symm ((s⁻¹ : Rˣ) : R) := by
    rw [cr_w_eq_alt i j k hij hik hjk s]
    simp only [x_neg]
    group
  -- `x_ji(t) x_ji(s⁻¹) = x_ji(-v⁻¹)` with `v = -s u⁻¹`.
  have hy1 : x j i hij.symm t * x j i hij.symm ((s⁻¹ : Rˣ) : R) =
      x j i hij.symm (-(((((-s) * u⁻¹)⁻¹ : Rˣ)) : R)) := by
    rw [x_mul, hvinv, neg_neg]
    congr 1
    linear_combination (-((s⁻¹ : Rˣ) : R)) * hu + (-t) * Hs
  -- `x_ji(-v⁻¹) = x_ij(-v) w(v) x_ij(-v)`.
  have hy2 : x j i hij.symm (-(((((-s) * u⁻¹)⁻¹ : Rˣ)) : R)) =
      x i j hij (-((((-s) * u⁻¹ : Rˣ)) : R)) * w i j hij ((-s) * u⁻¹) *
        x i j hij (-((((-s) * u⁻¹ : Rˣ)) : R)) := by
    rw [w]
    simp only [x_neg]
    group
  -- `x_ij(-v) w(s) = w(s) x_ji(-(u⁻¹ s⁻¹))`.
  have hc1 : x i j hij (-((((-s) * u⁻¹ : Rˣ)) : R)) * w i j hij s =
      w i j hij s * x j i hij.symm (-(((u⁻¹ : Rˣ) : R) * ((s⁻¹ : Rˣ) : R))) := by
    have e := cr_w_conj_x_self_symm i j k hij hik hjk s
      (-(((u⁻¹ : Rˣ) : R) * ((s⁻¹ : Rˣ) : R)))
    have e' : x i j hij (-((((-s) * u⁻¹ : Rˣ)) : R)) =
        w i j hij s * x j i hij.symm (-(((u⁻¹ : Rˣ) : R) * ((s⁻¹ : Rˣ) : R))) *
          (w i j hij s)⁻¹ := by
      rw [e]
      congr 1
      rw [hvval]
      linear_combination (-((s : R) * ((u⁻¹ : Rˣ) : R))) * Hs'
    rw [e']
    group
  -- `w(v) w(s) = h(v) h(-s)⁻¹ = {-s, u⁻¹} h(u⁻¹)`.
  have hww : w i j hij ((-s) * u⁻¹) * w i j hij s = csym i j hij (-s) u⁻¹ * h i j hij u⁻¹ := by
    simp only [csym, h]
    rw [← w_inv i j hij 1, ← w_inv i j hij s]
    group
  -- `x_ji(-(u⁻¹ s⁻¹)) x_ji(s⁻¹) = x_ji(t u⁻¹)`.
  have hy3 : x j i hij.symm (-(((u⁻¹ : Rˣ) : R) * ((s⁻¹ : Rˣ) : R))) *
      x j i hij.symm ((s⁻¹ : Rˣ) : R) = x j i hij.symm (t * ((u⁻¹ : Rˣ) : R)) := by
    rw [x_mul]
    congr 1
    linear_combination (-((s⁻¹ : Rˣ) : R)) * Hu +
      (((u⁻¹ : Rˣ) : R) * ((s⁻¹ : Rˣ) : R)) * hu + (((u⁻¹ : Rˣ) : R) * t) * Hs
  have hxc : x i j hij (-((((-s) * u⁻¹ : Rˣ)) : R)) =
      x i j hij ((s : R) * ((u⁻¹ : Rˣ) : R)) := by
    rw [hvval, neg_neg]
  calc x j i hij.symm t * x i j hij (s : R)
      = (x j i hij.symm t * x j i hij.symm ((s⁻¹ : Rˣ) : R)) * w i j hij s *
          x j i hij.symm ((s⁻¹ : Rˣ) : R) := by
        rw [hx]; group
    _ = x i j hij (-((((-s) * u⁻¹ : Rˣ)) : R)) * w i j hij ((-s) * u⁻¹) *
          (x i j hij (-((((-s) * u⁻¹ : Rˣ)) : R)) * w i j hij s) *
          x j i hij.symm ((s⁻¹ : Rˣ) : R) := by
        rw [hy1, hy2]; group
    _ = x i j hij (-((((-s) * u⁻¹ : Rˣ)) : R)) *
          (w i j hij ((-s) * u⁻¹) * w i j hij s) *
          (x j i hij.symm (-(((u⁻¹ : Rˣ) : R) * ((s⁻¹ : Rˣ) : R))) *
            x j i hij.symm ((s⁻¹ : Rˣ) : R)) := by
        rw [hc1]; group
    _ = _ := by rw [hww, hy3, hxc]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.rank1_unit

end GroupApproximation.BooneHigmanLinear.RelGen
