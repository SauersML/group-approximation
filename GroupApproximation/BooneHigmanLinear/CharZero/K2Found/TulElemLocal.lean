import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulElemConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's Lemma 1.1(d), and 1.1(e) in general

Continuing `TulElem` and `TulElemConj` (M. S. Tulenbaev, *The Steinberg group of a polynomial
ring*, Lemma 1.1):
* `ex_smul_left` (T 1.1(d)): `X(c v, w) = X(v, c w)` when `w` has two zeros. It follows from the
  relations of `Elements`, via three applications of (1.3).
* `IsLocal hX`: `X(v, w) = X_r(v, w)` for unimodular `v` when `w` has two zeros. Tulenbaev states
  this as part of van der Kallen's theorem ("if `w` has two zero coordinates, then
  `X_{v,w} = X(v, w)`"). For vdK's construction of `X_{v,w}` as a product of elementary
  `X(v, w_ij)`, it is the grouping argument for T 1.1(b). It is a hypothesis here.
* `ex_commute_gen` (T 1.1(e)): under `IsLocal`, `X(v, w)` and `X(v', w')` commute when each row
  kills each column and each row has two zeros.
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

theorem ex_zero_right (r : I) (v : I → A) : ex hX r v 0 = 1 := by
  rw [ex, smul_zero, E_zero, E_zero, one_mul]

/-- T 1.1(d) for a column vanishing at the two zeros `r, s` of `w`. -/
theorem ex_smul_of_zero {r s : I} (hrs : r ≠ s) {p w : I → A} (hr : w r = 0) (hs : w s = 0)
    (hw : w ⬝ᵥ p = 0) (hpr : p r = 0) (hps : p s = 0) (c : A) :
    ex hX r (c • p) w = ex hX r p (c • w) := by
  have hsr : (Pi.single r (1 : A)) s = 0 := Pi.single_eq_of_ne hrs.symm 1
  have hrs' : (Pi.single s (1 : A)) r = 0 := Pi.single_eq_of_ne hrs 1
  have hwp : w ⬝ᵥ (c • p) = 0 := by rw [dotProduct_smul, hw, smul_zero]
  have hA := E_frame hX (v := p + Pi.single r 1) (v' := Pi.single s 1) (w := w)
    (u := Pi.single s 1) c
    (by rw [single_one_dotProduct, Pi.add_apply, hps, hsr, add_zero])
    (by rw [single_one_dotProduct, Pi.single_eq_same]) (dot_add_single hr hw) (dot_single hs)
    (isUnimodular_of_apply (r := r) (by rw [Pi.add_apply, hpr, Pi.single_eq_same, zero_add]))
  have hB := E_frame hX (v := Pi.single r 1) (v' := c • p + Pi.single r 1 + Pi.single s 1)
    (w := w) (u := Pi.single s 1) (c - 1) (by rw [single_one_dotProduct, hsr])
    (by rw [single_one_dotProduct, Pi.add_apply, Pi.add_apply, Pi.smul_apply, hps, smul_zero,
      hsr, Pi.single_eq_same, zero_add, zero_add])
    (dot_single hr) (dot_add_single hs (dot_add_single hr hwp)) (isUnimodular_single r)
  have hC := E_frame hX (v := Pi.single s 1) (v' := c • p + Pi.single r 1) (w := w)
    (u := Pi.single r 1) 1 (by rw [single_one_dotProduct, hrs'])
    (by rw [single_one_dotProduct, Pi.add_apply, Pi.smul_apply, hpr, smul_zero,
      Pi.single_eq_same, zero_add])
    (dot_single hs) (dot_add_single hr hwp) (isUnimodular_single s)
  rw [one_smul, one_smul] at hC
  have e1 : c • (p + Pi.single r (1 : A)) + Pi.single s 1 =
      (c - 1) • Pi.single r 1 + (c • p + Pi.single r 1 + Pi.single s 1) := by module
  have e2 : c • p + Pi.single r (1 : A) + Pi.single s 1 =
      Pi.single s 1 + (c • p + Pi.single r 1) := by
    abel
  rw [e1, hB, e2, hC] at hA
  have hcomm := E_row_commute hX (w := w) (isUnimodular_single s)
    (isUnimodular_of_apply (r := r) (by rw [Pi.add_apply, Pi.smul_apply, hpr, smul_zero,
      Pi.single_eq_same, zero_add])) (dot_single hs) (dot_add_single hr hwp) 1 1
  rw [one_smul] at hcomm
  rw [hcomm.eq, ← mul_assoc] at hA
  have hA' := mul_right_cancel hA
  rw [ex, ex, Pi.smul_apply, hpr, smul_zero, zero_sub, sub_zero, one_smul, ← hA', ← mul_assoc,
    E_mul hX (isUnimodular_single r) (smul_dot _ (smul_dot _ (dot_single hr)))
      (smul_dot _ (dot_single hr)),
    show (-1 : A) • c • w + (c - 1) • w = (-1 : A) • w by module]

#audit_axioms ex_smul_of_zero

/-- **T 1.1(d)**: `X(c v, w) = X(v, c w)` when `w` has two zeros `r ≠ s`. -/
theorem ex_smul_left {r s : I} (hrs : r ≠ s) {v w : I → A} (hr : w r = 0) (hs : w s = 0)
    (hw : w ⬝ᵥ v = 0) (c : A) : ex hX r (c • v) w = ex hX r v (c • w) := by
  have hcr : (c • w) r = 0 := by rw [Pi.smul_apply, hr, smul_zero]
  have hcs : (c • w) s = 0 := by rw [Pi.smul_apply, hs, smul_zero]
  have h1 : (c • v) r • w = v r • c • w := by
    rw [Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm]
  have h2 : (c • v) s • w = v s • c • w := by
    rw [Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm]
  have h3 : qz r s (c • v) = c • qz r s v := by
    rw [qz, qz, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    module
  have hwc : w ⬝ᵥ (c • v) = 0 := by rw [dotProduct_smul, hw, smul_zero]
  rw [ex_decomp hX hrs hr hs hwc,
    ex_decomp hX hrs (w := c • w) hcr hcs (smul_dot c hw), h1, h2, h3,
    ex_smul_of_zero hX hrs hr hs (dot_qz hr hs hw) (qz_apply_left hrs v) (qz_apply_right hrs v)]

#audit_axioms ex_smul_left

/-- **Locality of van der Kallen's elements** (vdK; Tulenbaev §1): `X(v, w) = X_r(v, w)` for
unimodular `v` when `w` has two zeros `r ≠ s`. -/
def IsLocal : Prop :=
  ∀ (v w : I → A) (r s : I), r ≠ s → w r = 0 → w s = 0 → w ⬝ᵥ v = 0 → IsUnimodular v →
    E hX v w = ex hX r v w

omit [DecidableEq I] in
theorem dot_smul_zero {x y : I → A} (c : A) (h : x ⬝ᵥ y = 0) : x ⬝ᵥ (c • y) = 0 := by
  rw [dotProduct_smul, h, smul_zero]

/-- **T 1.1(e)**: under `IsLocal`, `X_r(v, w)` and `X_t(v', w')` commute when both rows kill both
columns and `w'` has two zeros `t ≠ t'`. -/
theorem ex_commute_gen (hL : IsLocal hX) {r t t' : I} (htt : t ≠ t') {v w v' w' : I → A}
    (hr : w r = 0) (ht : w' t = 0) (ht' : w' t' = 0) (hwv : w ⬝ᵥ v = 0) (hwv' : w ⬝ᵥ v' = 0)
    (hw'v : w' ⬝ᵥ v = 0) (hw'v' : w' ⬝ᵥ v' = 0) : Commute (ex hX r v w) (ex hX t v' w') := by
  have hq1 : (Pi.single t (1 : A), (v' t - 1) • w') ∈ U I A :=
    memU (isUnimodular_single t) (smul_dot _ (dot_single ht))
  have hq2 : (v' + (1 - v' t) • Pi.single t (1 : A), w') ∈ U I A :=
    memU (isUnimodular_of_apply (tl_apply v' t)) (dot_tl ht hw'v' _)
  have hμ : w ⬝ᵥ (v' + (1 - v' t) • Pi.single t (1 : A)) = (1 - v' t) * w t := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_single_one, hwv', zero_add, smul_eq_mul]
  have hu1 : IsUnimodular (Pi.single t (1 : A) + w t • v) := ⟨Pi.single t 1 - v t • w, by
    rw [sub_dotProduct, smul_dotProduct, single_one_dotProduct, dotProduct_add, dotProduct_smul,
      hwv, dotProduct_single_one, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_zero,
      add_zero, smul_eq_mul, smul_eq_mul]
    ring⟩
  have hu2 : IsUnimodular (v' + (1 - v' t) • Pi.single t (1 : A) + ((1 - v' t) * w t) • v) :=
    ⟨Pi.single t 1 - v t • w, by
      rw [sub_dotProduct, smul_dotProduct, single_one_dotProduct, dotProduct_add, dotProduct_smul,
        hwv, hμ, Pi.add_apply, tl_apply v' t, Pi.smul_apply, smul_zero, add_zero, smul_eq_mul,
        smul_eq_mul]
      ring⟩
  -- the row `x = (v'_t - 1) w'` has the zeros `t, t'` and kills `v, v'`
  have hxt : ((v' t - 1) • w') t = 0 := by rw [Pi.smul_apply, ht, smul_zero]
  have hxt' : ((v' t - 1) • w') t' = 0 := by rw [Pi.smul_apply, ht', smul_zero]
  have hxv := smul_dot (v' t - 1) hw'v
  have hw'1 : w' ⬝ᵥ (Pi.single t 1 + w t • v) = 0 := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_single_one, ht, hw'v, smul_zero, add_zero]
  have hw'2 : w' ⬝ᵥ (v' + (1 - v' t) • Pi.single t 1 + ((1 - v' t) * w t) • v) = 0 := by
    rw [dotProduct_add, dotProduct_smul, hw'v, smul_zero, add_zero]
    exact dot_tl ht hw'v' _
  have hcomm := ex_commute_ex hX (r := t) (t := t) (v := v) (w := (w t) • (v' t - 1) • w')
    (v' := v' + (1 - v' t) • Pi.single t 1) (w' := w')
    (by rw [Pi.smul_apply, hxt, smul_zero]) (smul_dot _ hxv) ht (dot_tl ht hw'v' _)
    (by rw [Pi.smul_apply, hxt, smul_zero]) (smul_dot _ (smul_dot _ (dot_tl ht hw'v' _))) hw'v
  have hadd := ex_add_right hX (r := t) (v := v) (w := w t • (v' t - 1) • w')
    (w' := ((1 - v' t) * w t) • w') (by rw [Pi.smul_apply, hxt, smul_zero])
    (by rw [Pi.smul_apply, ht, smul_zero]) (smul_dot _ hxv) (smul_dot _ hw'v)
  have key : ex hX r v w * (E hX (Pi.single t 1) ((v' t - 1) • w') *
      E hX (v' + (1 - v' t) • Pi.single t 1) w') * (ex hX r v w)⁻¹ =
      E hX (Pi.single t 1) ((v' t - 1) • w') * E hX (v' + (1 - v' t) • Pi.single t 1) w' := by
    rw [conj_mul_conj, E_conj_st hX _ hq1, E_conj_st hX _ hq2, pm_ex hX hr hwv, eUnit_mulVec,
      eUnit_mulVec, vecMul_eUnit_inv, vecMul_eUnit_inv, hxv, hw'v, zero_smul, sub_zero, sub_zero,
      dotProduct_single_one, hμ,
      hL _ _ t t' htt hxt hxt' (smul_dot _ hw'1) hu1, hL _ _ t t' htt ht ht' hw'2 hu2,
      ex_add_left hX htt hxt hxt' (smul_dot _ (dot_single ht)) (dot_smul_zero _ hxv),
      ex_add_left hX htt ht ht' (dot_tl ht hw'v' _) (dot_smul_zero _ hw'v),
      ex_of_apply_one hX (Pi.single_eq_same t (1 : A)), ex_smul_left hX htt hxt hxt' hxv,
      ex_smul_left hX htt ht ht' hw'v, mul_assoc, hcomm.left_comm,
      ← hadd,
      show w t • (v' t - 1) • w' + ((1 - v' t) * w t) • w' = 0 by module, ex_zero_right, mul_one,
      ex_of_apply_one hX (tl_apply v' t)]
  exact mul_inv_eq_iff_eq_mul.mp key

#audit_axioms ex_commute_gen

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
