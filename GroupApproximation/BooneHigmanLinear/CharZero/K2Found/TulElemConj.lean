import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulElem
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's elementary `X(v, w)`: projection, conjugation, commutation

Continuing `TulElem` (M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Lemma 1.1):
* `pm_ex`: `π(X_r(v, w)) = 1 + v w`;
* `E_conj_st`: `y X(v, w) y⁻¹ = X(π(y) v, w π(y)⁻¹)` for every `y ∈ St(A)`;
* `ex_conj_x` (T 1.1(c)): `x_ij(a) X(v, w) x_ij(-a) = X(x_ij(a) v, w x_ij(-a))` when `w` has a
  zero `r ∉ {i, j}`;
* `ex_commute_ex` (T 1.1(e), common-zero case): `X(v, w)` and `X(v', w')` commute when `w, w'`
  have a common zero and `w v' = w' v = 0`;
* `ex_of_apply_one`: `X_r(v, w) = X(v, w)` when `v_r = 1`; in particular `X(e_i, a e_j) = x_ij(a)`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (U Elements IsUnimodular eUnit)

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A] (hX : Elements I A)

theorem conj_mul_conj {G : Type*} [Group G] (y a b : G) :
    y * (a * b) * y⁻¹ = y * a * y⁻¹ * (y * b * y⁻¹) := by
  group

theorem eUnit_mulVec (v w y : I → A) (h : w ⬝ᵥ v = 0) :
    (eUnit v w h : Matrix I I A) *ᵥ y = y + (w ⬝ᵥ y) • v := by
  rw [VdK.eUnit_val, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem vecMul_eUnit_inv (v w x : I → A) (h : w ⬝ᵥ v = 0) :
    x ᵥ* (((eUnit v w h)⁻¹ : (Matrix I I A)ˣ) : Matrix I I A) = x - (x ⬝ᵥ v) • w := by
  change x ᵥ* (1 - vecMulVec v w) = _
  rw [vecMul_sub, vecMul_one, vecMul_vecMulVec]

/-- `y X(v, w) y⁻¹ = X(π(y) v, w π(y)⁻¹)`. -/
theorem E_conj_st (y : SteinbergGroup I A) {v w : I → A} (h : (v, w) ∈ U I A) :
    y * E hX v w * y⁻¹ =
      E hX ((((projection y : elementaryGroup I A) : (Matrix I I A)ˣ) : Matrix I I A) *ᵥ v)
        (w ᵥ* ((((projection y : elementaryGroup I A) : (Matrix I I A)ˣ)⁻¹ : (Matrix I I A)ˣ) :
          Matrix I I A)) := by
  have h' : ((((projection y : elementaryGroup I A) : (Matrix I I A)ˣ) : Matrix I I A) *ᵥ v,
      w ᵥ* ((((projection y : elementaryGroup I A) : (Matrix I I A)ˣ)⁻¹ : (Matrix I I A)ˣ) :
        Matrix I I A)) ∈ U I A :=
    RelPres.smulPair_mem_U (I := I) (A := A)
      ((projection y : elementaryGroup I A) : (Matrix I I A)ˣ) h
  rw [E_of_mem hX h, RelPres.elt_conj hX y (v, w) h]
  exact (E_of_mem hX h').symm

#audit_axioms E_conj_st

theorem pm_E {v w : I → A} (h : (v, w) ∈ U I A) :
    ((projection (E hX v w) : elementaryGroup I A) : (Matrix I I A)ˣ) =
      eUnit v w (VdK.mem_U.1 h).2 := by
  rw [E_of_mem hX h]
  exact hX.proj (v, w) h

/-- `π(X_r(v, w)) = 1 + v w`. -/
theorem pm_ex {r : I} {v w : I → A} (hr : w r = 0) (hw : w ⬝ᵥ v = 0) :
    ((projection (ex hX r v w) : elementaryGroup I A) : (Matrix I I A)ˣ) = eUnit v w hw := by
  have h₁ : (Pi.single r (1 : A), (v r - 1) • w) ∈ U I A :=
    memU (isUnimodular_single r) (smul_dot _ (dot_single hr))
  have h₂ : (v + (1 - v r) • Pi.single r (1 : A), w) ∈ U I A :=
    memU (isUnimodular_of_apply (tl_apply v r)) (dot_tl hr hw _)
  rw [ex, map_mul, Subgroup.coe_mul, pm_E hX h₁, pm_E hX h₂]
  apply Units.ext
  change (1 + vecMulVec (Pi.single r 1) ((v r - 1) • w)) *
    (1 + vecMulVec (v + (1 - v r) • Pi.single r 1) w) = 1 + vecMulVec v w
  rw [add_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec, smul_dotProduct,
    dot_tl hr hw, smul_zero, zero_smul, vecMulVec_zero, add_zero]
  simp only [add_vecMulVec, smul_vecMulVec, vecMulVec_smul]
  module

#audit_axioms pm_ex

/-- `X_r(v, w) = X(v, w)` when `v_r = 1`. -/
theorem ex_of_apply_one {r : I} {v w : I → A} (h : v r = 1) : ex hX r v w = E hX v w := by
  rw [ex, h, sub_self, zero_smul, zero_smul, E_zero, one_mul, add_zero]

#audit_axioms ex_of_apply_one

/-- `x_ij(a) = X_i(e_i, a e_j)`. -/
theorem x_eq_ex {i j : I} (hij : i ≠ j) (a : A) :
    x i j hij a = ex hX i (Pi.single i 1) (Pi.single j a) := by
  rw [ex_of_apply_one hX (v := Pi.single i 1) (r := i) (by simp), x_eq_E hX hij]

#audit_axioms x_eq_ex

/-- **T 1.1(c)**, when `w` has a zero `r ∉ {i, j}`: `x_ij(a) X(v, w) x_ij(-a) = X(x_ij(a) v,
w x_ij(-a))`, where `x_ij(a) v = v + a v_j e_i` and `w x_ij(-a) = w - a w_i e_j`. -/
theorem ex_conj_x {i j r : I} (hij : i ≠ j) (hri : r ≠ i) (hrj : r ≠ j) {v w : I → A}
    (hr : w r = 0) (hw : w ⬝ᵥ v = 0) (a : A) :
    x i j hij a * ex hX r v w * (x i j hij a)⁻¹ =
      ex hX r (v + (a * v j) • Pi.single i 1) (w - (a * w i) • Pi.single j 1) := by
  have hp := VdK.stdPair_mem hij a
  have hq1 : (Pi.single r (1 : A), (v r - 1) • w) ∈ U I A :=
    memU (isUnimodular_single r) (smul_dot _ (dot_single hr))
  have hq2 : (v + (1 - v r) • Pi.single r (1 : A), w) ∈ U I A :=
    memU (isUnimodular_of_apply (tl_apply v r)) (dot_tl hr hw _)
  have hsa : (Pi.single j a : I → A) = a • Pi.single j 1 := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  have hvr : (v + (a * v j) • Pi.single i 1 : I → A) r = v r := by
    simp [Pi.single_eq_of_ne hri]
  have hvj : (v + (1 - v r) • Pi.single r 1 : I → A) j = v j := by
    simp [Pi.single_eq_of_ne hrj.symm]
  have c1 : Pi.single r (1 : A) + (Pi.single j a ⬝ᵥ Pi.single r 1) • Pi.single i 1 =
      Pi.single r 1 := by
    rw [dotProduct_single_one, Pi.single_eq_of_ne hrj, zero_smul, add_zero]
  have c2 : (v r - 1) • w - (((v r - 1) • w) ⬝ᵥ Pi.single i 1) • Pi.single j a =
      ((v + (a * v j) • Pi.single i 1 : I → A) r - 1) • (w - (a * w i) • Pi.single j 1) := by
    rw [hvr, smul_dotProduct, dotProduct_single_one, smul_eq_mul, hsa]
    module
  have c3 : v + (1 - v r) • Pi.single r (1 : A) +
      (Pi.single j a ⬝ᵥ (v + (1 - v r) • Pi.single r 1)) • Pi.single i 1 =
      v + (a * v j) • Pi.single i 1 +
        (1 - (v + (a * v j) • Pi.single i 1 : I → A) r) • Pi.single r 1 := by
    rw [single_dotProduct, hvj, hvr]
    module
  have c4 : w - (w ⬝ᵥ Pi.single i 1) • Pi.single j a = w - (a * w i) • Pi.single j (1 : A) := by
    rw [dotProduct_single_one, hsa]
    module
  rw [x_eq_E hX hij, ex, ex, conj_mul_conj, E_conj hX hp hq1, E_conj hX hp hq2, c1, c2, c3, c4]

#audit_axioms ex_conj_x

/-- **T 1.1(e)**, common-zero case: `X_r(v, w)` and `X_t(v', w')` commute when `w_t = 0`,
`w v' = 0` and `w' v = 0`. -/
theorem ex_commute_ex {r t : I} {v w v' w' : I → A} (hr : w r = 0) (hw : w ⬝ᵥ v = 0)
    (ht : w' t = 0) (hw' : w' ⬝ᵥ v' = 0) (hwt : w t = 0) (h₁ : w ⬝ᵥ v' = 0)
    (h₂ : w' ⬝ᵥ v = 0) : Commute (ex hX r v w) (ex hX t v' w') := by
  have hq1 : (Pi.single t (1 : A), (v' t - 1) • w') ∈ U I A :=
    memU (isUnimodular_single t) (smul_dot _ (dot_single ht))
  have hq2 : (v' + (1 - v' t) • Pi.single t (1 : A), w') ∈ U I A :=
    memU (isUnimodular_of_apply (tl_apply v' t)) (dot_tl ht hw' _)
  have key : ex hX r v w * (E hX (Pi.single t 1) ((v' t - 1) • w') *
      E hX (v' + (1 - v' t) • Pi.single t 1) w') * (ex hX r v w)⁻¹ =
      E hX (Pi.single t 1) ((v' t - 1) • w') * E hX (v' + (1 - v' t) • Pi.single t 1) w' := by
    rw [conj_mul_conj, E_conj_st hX _ hq1, E_conj_st hX _ hq2, pm_ex hX hr hw, eUnit_mulVec,
      eUnit_mulVec, vecMul_eUnit_inv, vecMul_eUnit_inv, dot_single hwt, smul_dot _ h₂,
      dot_tl hwt h₁, h₂]
    simp only [zero_smul, add_zero, sub_zero]
  exact mul_inv_eq_iff_eq_mul.mp key

#audit_axioms ex_commute_ex

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
