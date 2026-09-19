import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresElt
import Mathlib.Tactic.Module
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's elementary elements `X(v, w)` from van der Kallen's elements (T Lemma 1.1)

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, §1. Let `v` be any column (unimodular
or not) and `w` a row with `w v = 0` and `w_r = 0`. Tulenbaev, after van der Kallen, uses
`X(v, w) = X_r(v_r w) ⁅X'_r(v), X_r(w)⁆`. Given van der Kallen's elements `hX : VdK.Elements I A`,
this equals
`X_r(v, w) = X(e_r, (v_r - 1) w) · X(v + (1 - v_r) e_r, w)` (`ex`),
because `X'_r(v)` conjugates `X_r(w) = X(e_r, w)` to `X(v + (1 - v_r) e_r, w)`. Both pairs lie in
vdK's `U`, since the second column has `r`-th coordinate `1`.

From `hX.mul`, `hX.conj` and Tulenbaev's (1.3) (`RelPres.elt_frame`):
* `ex_indep`: `X_r(v, w) = X_s(v, w)` when `w_r = w_s = 0`;
* `ex_add_right` (T 1.1(b)): additivity in `w` along a common zero;
* `ex_add_left` (T 1.1(a)): additivity in `v` when `w` has two zeros.

`E hX v w` is `hX.elt (v, w)` extended by `1` off `U`, so the statements carry no proof terms.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (U Elements IsUnimodular)

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A] (hX : Elements I A)

section E

/-- `X(v, w)` as a total function: `hX.elt (v, w)` on `U`, and `1` off `U`. -/
noncomputable def E (v w : I → A) : SteinbergGroup I A :=
  if h : (v, w) ∈ U I A then hX.elt (v, w) h else 1

theorem E_of_mem {v w : I → A} (h : (v, w) ∈ U I A) : E hX v w = hX.elt (v, w) h :=
  dif_pos h

omit [DecidableEq I] in
theorem memU {v w : I → A} (hv : IsUnimodular v) (hw : w ⬝ᵥ v = 0) : (v, w) ∈ U I A :=
  VdK.mk_mem_U.2 ⟨hv, hw⟩

theorem isUnimodular_single (r : I) : IsUnimodular (Pi.single r (1 : A)) :=
  ⟨Pi.single r 1, by rw [single_one_dotProduct, Pi.single_eq_same]⟩

theorem isUnimodular_of_apply {v : I → A} {r : I} (h : v r = 1) : IsUnimodular v :=
  ⟨Pi.single r 1, by rw [single_one_dotProduct, h]⟩

theorem dot_single {w : I → A} {r : I} (hr : w r = 0) : w ⬝ᵥ Pi.single r (1 : A) = 0 := by
  rw [dotProduct_single_one, hr]

omit [DecidableEq I] in
theorem smul_dot {w y : I → A} (c : A) (h : w ⬝ᵥ y = 0) : (c • w) ⬝ᵥ y = 0 := by
  rw [smul_dotProduct, h, smul_zero]

theorem dot_tl {v w : I → A} {r : I} (hr : w r = 0) (hw : w ⬝ᵥ v = 0) (c : A) :
    w ⬝ᵥ (v + c • Pi.single r 1) = 0 := by
  rw [dotProduct_add, dotProduct_smul, dot_single hr, hw, smul_zero, add_zero]

omit [DecidableEq I] in
theorem add_dot {v w w' : I → A} (hw : w ⬝ᵥ v = 0) (hw' : w' ⬝ᵥ v = 0) :
    (w + w') ⬝ᵥ v = 0 := by
  rw [add_dotProduct, hw, hw', add_zero]

omit [DecidableEq I] in
theorem dot_add {v v' w : I → A} (hw : w ⬝ᵥ v = 0) (hw' : w ⬝ᵥ v' = 0) :
    w ⬝ᵥ (v + v') = 0 := by
  rw [dotProduct_add, hw, hw', add_zero]

omit [Fintype I] in
theorem tl_apply (v : I → A) (r : I) : (v + (1 - v r) • Pi.single r (1 : A)) r = 1 := by
  simp

theorem E_mul {v w w' : I → A} (hv : IsUnimodular v) (hw : w ⬝ᵥ v = 0) (hw' : w' ⬝ᵥ v = 0) :
    E hX v w * E hX v w' = E hX v (w + w') := by
  rw [E_of_mem hX (memU hv hw), E_of_mem hX (memU hv hw'),
    E_of_mem hX (memU hv (add_dot hw hw'))]
  exact hX.mul _ _ _ _ _ _

#audit_axioms E_mul

theorem E_zero (v : I → A) : E hX v 0 = 1 := by
  by_cases h : (v, (0 : I → A)) ∈ U I A
  · rw [E_of_mem hX h]
    exact RelPres.elt_zero hX v h
  · exact dif_neg h

#audit_axioms E_zero

theorem E_conj {v w v' w' : I → A} (hp : (v, w) ∈ U I A) (hq : (v', w') ∈ U I A) :
    E hX v w * E hX v' w' * (E hX v w)⁻¹ = E hX (v' + (w ⬝ᵥ v') • v) (w' - (w' ⬝ᵥ v) • w) := by
  have h : (v' + (w ⬝ᵥ v') • v, w' - (w' ⬝ᵥ v) • w) ∈ U I A := VdK.conjPair_mem hp hq
  rw [E_of_mem hX hp, E_of_mem hX hq, hX.conj]
  exact (E_of_mem hX h).symm

#audit_axioms E_conj

theorem E_commute {v w v' w' : I → A} (hp : (v, w) ∈ U I A) (hq : (v', w') ∈ U I A)
    (h₁ : w ⬝ᵥ v' = 0) (h₂ : w' ⬝ᵥ v = 0) : Commute (E hX v w) (E hX v' w') := by
  have h := E_conj hX hp hq
  rw [h₁, h₂, zero_smul, zero_smul, add_zero, sub_zero] at h
  exact mul_inv_eq_iff_eq_mul.mp h

#audit_axioms E_commute

theorem E_commute' {y y' x x' : I → A} (hy : IsUnimodular y) (hy' : IsUnimodular y')
    (h₁ : x ⬝ᵥ y = 0) (h₂ : x' ⬝ᵥ y' = 0) (h₃ : x ⬝ᵥ y' = 0) (h₄ : x' ⬝ᵥ y = 0) :
    Commute (E hX y x) (E hX y' x') :=
  E_commute hX (memU hy h₁) (memU hy' h₂) h₃ h₄

/-- All `X(y, c w)` with `y` unimodular and `w y = 0` commute. -/
theorem E_row_commute {w y y' : I → A} (hy : IsUnimodular y) (hy' : IsUnimodular y')
    (h : w ⬝ᵥ y = 0) (h' : w ⬝ᵥ y' = 0) (c c' : A) :
    Commute (E hX y (c • w)) (E hX y' (c' • w)) :=
  E_commute' hX hy hy' (smul_dot c h) (smul_dot c' h') (smul_dot c h') (smul_dot c' h)

/-- Tulenbaev's (1.3): `X(b v + v', w) = X(v, b w) X(v', w)` if `u v = 0`, `u v' = 1`. -/
theorem E_frame {v v' w u : I → A} (b : A) (hu : u ⬝ᵥ v = 0) (hu' : u ⬝ᵥ v' = 1)
    (hw : w ⬝ᵥ v = 0) (hw' : w ⬝ᵥ v' = 0) (hv : IsUnimodular v) :
    E hX (b • v + v') w = E hX v (b • w) * E hX v' w := by
  have h₁ : (b • v + v', w) ∈ U I A := memU
    ⟨u, by rw [dotProduct_add, dotProduct_smul, hu, hu', smul_zero, zero_add]⟩
    (by rw [dotProduct_add, dotProduct_smul, hw, hw', smul_zero, add_zero])
  have h₂ : (v, b • w) ∈ U I A := memU hv (smul_dot b hw)
  have h₃ : (v', w) ∈ U I A := memU ⟨u, hu'⟩ hw'
  rw [E_of_mem hX h₁, E_of_mem hX h₂, E_of_mem hX h₃]
  exact RelPres.elt_frame hX v v' w u b hu hu' hw hv h₁ h₂ h₃

#audit_axioms E_frame

theorem x_eq_E {i j : I} (hij : i ≠ j) (a : A) :
    x i j hij a = E hX (Pi.single i 1) (Pi.single j a) := by
  rw [E_of_mem hX (VdK.stdPair_mem hij a)]
  exact (hX.std i j hij a).symm

#audit_axioms x_eq_E

end E

section Elementary

/-- **Tulenbaev's elementary `X_r(v, w)`**, for `w_r = 0`, `w v = 0` and any column `v`:
`X(e_r, (v_r - 1) w) · X(v + (1 - v_r) e_r, w)`. -/
noncomputable def ex (r : I) (v w : I → A) : SteinbergGroup I A :=
  E hX (Pi.single r 1) ((v r - 1) • w) * E hX (v + (1 - v r) • Pi.single r 1) w

/-- `v + (1 - v_r) e_r + (1 - v_s) e_s`, with `r`- and `s`-coordinates `1`. -/
def vhat (r s : I) (v : I → A) : I → A :=
  v + (1 - v r) • Pi.single r 1 + (1 - v s) • Pi.single s 1

omit [Fintype I] in
theorem vhat_apply_left {r s : I} (hrs : r ≠ s) (v : I → A) : vhat r s v r = 1 := by
  simp [vhat, Pi.single_eq_of_ne hrs]

theorem dot_vhat {r s : I} {v w : I → A} (hr : w r = 0) (hs : w s = 0) (hw : w ⬝ᵥ v = 0) :
    w ⬝ᵥ vhat r s v = 0 := by
  rw [vhat, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, dot_single hr,
    dot_single hs, hw]
  simp

/-- The two-zero form: `X_r(v, w) = X(e_r, (v_r - 1) w) X(e_s, (v_s - 1) w) X(vhat, w)`. -/
theorem ex_eq_two {r s : I} (hrs : r ≠ s) {v w : I → A} (hr : w r = 0) (hs : w s = 0)
    (hw : w ⬝ᵥ v = 0) :
    ex hX r v w = E hX (Pi.single r 1) ((v r - 1) • w) *
      (E hX (Pi.single s 1) ((v s - 1) • w) * E hX (vhat r s v) w) := by
  have h := E_frame hX (v := Pi.single s 1) (v' := vhat r s v) (w := w) (u := Pi.single r 1)
    (v s - 1) (by rw [single_one_dotProduct, Pi.single_eq_of_ne hrs])
    (by rw [single_one_dotProduct, vhat_apply_left hrs]) (dot_single hs) (dot_vhat hr hs hw)
    (isUnimodular_single s)
  have e : (v s - 1) • Pi.single s (1 : A) + vhat r s v = v + (1 - v r) • Pi.single r 1 := by
    rw [vhat]
    module
  rw [e] at h
  rw [ex, h]

#audit_axioms ex_eq_two

/-- **Independence of the zero coordinate**: `X_r(v, w) = X_s(v, w)` when `w_r = w_s = 0`. -/
theorem ex_indep {r s : I} (hrs : r ≠ s) {v w : I → A} (hr : w r = 0) (hs : w s = 0)
    (hw : w ⬝ᵥ v = 0) : ex hX r v w = ex hX s v w := by
  have hsym : vhat s r v = vhat r s v := by
    rw [vhat, vhat]
    exact add_right_comm _ _ _
  rw [ex_eq_two hX hrs hr hs hw, ex_eq_two hX hrs.symm hs hr hw, hsym]
  exact (E_row_commute hX (isUnimodular_single r) (isUnimodular_single s) (dot_single hr)
    (dot_single hs) _ _).left_comm _

#audit_axioms ex_indep

/-- **T 1.1(b)**: `X(v, w + w') = X(v, w) X(v, w')` along a common zero `r`. -/
theorem ex_add_right {r : I} {v w w' : I → A} (hr : w r = 0) (hr' : w' r = 0)
    (hw : w ⬝ᵥ v = 0) (hw' : w' ⬝ᵥ v = 0) :
    ex hX r v (w + w') = ex hX r v w * ex hX r v w' := by
  have hu := isUnimodular_single (A := A) r
  have ht := isUnimodular_of_apply (tl_apply v r)
  rw [ex, ex, ex, smul_add, ← E_mul hX hu (smul_dot (v r - 1) (dot_single hr))
    (smul_dot (v r - 1) (dot_single hr')), ← E_mul hX ht (dot_tl hr hw _) (dot_tl hr' hw' _)]
  exact ((E_commute' hX ht hu (dot_tl hr hw _) (smul_dot (v r - 1) (dot_single hr'))
    (dot_single hr) (smul_dot (v r - 1) (dot_tl hr' hw' _))).mul_mul_mul_comm _ _).symm

#audit_axioms ex_add_right

/-- `X_r(v, w)` commutes with every `X(y, c w)`, `y` unimodular with `w y = 0`. -/
theorem ex_commute {r : I} {v w y : I → A} (hr : w r = 0) (hw : w ⬝ᵥ v = 0)
    (hy : IsUnimodular y) (h : w ⬝ᵥ y = 0) (c : A) : Commute (ex hX r v w) (E hX y (c • w)) := by
  refine Commute.mul_left (E_row_commute hX (isUnimodular_single r) hy (dot_single hr) h _ _) ?_
  simpa only [one_smul] using
    E_row_commute hX (isUnimodular_of_apply (tl_apply v r)) hy (dot_tl hr hw _) h 1 c

/-- `X_r(v + c e_r, w) = X(e_r, c w) X_r(v, w)`. -/
theorem ex_add_single_self {r : I} {v w : I → A} (hr : w r = 0) (c : A) :
    ex hX r (v + c • Pi.single r 1) w = E hX (Pi.single r 1) (c • w) * ex hX r v w := by
  have h1 : (v + c • Pi.single r (1 : A)) r = v r + c := by simp
  have h2 : v + c • Pi.single r (1 : A) + (1 - (v r + c)) • Pi.single r 1 =
      v + (1 - v r) • Pi.single r 1 := by module
  rw [ex, ex, h1, h2, ← mul_assoc, E_mul hX (isUnimodular_single r) (smul_dot c (dot_single hr))
    (smul_dot (v r - 1) (dot_single hr)), ← add_smul, show c + (v r - 1) = v r + c - 1 by ring]

#audit_axioms ex_add_single_self

/-- `X_r(v + c e_s, w) = X(e_s, c w) X_r(v, w)` when `w_r = w_s = 0`. -/
theorem ex_add_single_ne {r s : I} (hrs : r ≠ s) {v w : I → A} (hr : w r = 0) (hs : w s = 0)
    (hw : w ⬝ᵥ v = 0) (c : A) :
    ex hX r (v + c • Pi.single s 1) w = E hX (Pi.single s 1) (c • w) * ex hX r v w := by
  rw [ex_indep hX hrs hr hs (dot_tl hs hw c), ex_add_single_self hX hs c, ex_indep hX hrs hr hs hw]

#audit_axioms ex_add_single_ne

theorem dot_add_single {v w : I → A} {r : I} (hr : w r = 0) (hw : w ⬝ᵥ v = 0) :
    w ⬝ᵥ (v + Pi.single r 1) = 0 := by
  rw [dotProduct_add, hw, dot_single hr, add_zero]

/-- T 1.1(a) for columns vanishing at the two zeros `r, s` of `w`. -/
theorem ex_add_left_of_zero {r s : I} (hrs : r ≠ s) {v v' w : I → A} (hr : w r = 0)
    (hs : w s = 0) (hw : w ⬝ᵥ v = 0) (hw' : w ⬝ᵥ v' = 0) (hvr : v r = 0) (hvs : v s = 0)
    (hvr' : v' r = 0) (hvs' : v' s = 0) :
    ex hX r (v + v') w = ex hX r v w * ex hX r v' w := by
  have hr0 : (v + v') r = 0 := by rw [Pi.add_apply, hvr, hvr', add_zero]
  have hs0 : (v + v') s = 0 := by rw [Pi.add_apply, hvs, hvs', add_zero]
  have e1 : ex hX r v w =
      E hX (Pi.single r 1) ((-1 : A) • w) * E hX (v + Pi.single r 1) w := by
    rw [ex, hvr, zero_sub, sub_zero, one_smul]
  have e2 : ex hX r v' w =
      E hX (Pi.single s 1) ((-1 : A) • w) * E hX (v' + Pi.single s 1) w := by
    rw [ex_indep hX hrs hr hs hw', ex, hvs', zero_sub, sub_zero, one_smul]
  have ev : vhat r s (v + v') = v + Pi.single r 1 + (v' + Pi.single s 1) := by
    rw [vhat, hr0, hs0, sub_zero, one_smul, one_smul]
    abel
  have hwa := dot_add_single hr hw
  have hva : IsUnimodular (v + Pi.single r (1 : A)) :=
    isUnimodular_of_apply (r := r) (by rw [Pi.add_apply, hvr, Pi.single_eq_same, zero_add])
  have hf := E_frame hX (v := v + Pi.single r 1) (v' := v' + Pi.single s 1) (w := w)
    (u := Pi.single s 1) (1 : A)
    (by rw [single_one_dotProduct, Pi.add_apply, hvs, Pi.single_eq_of_ne hrs.symm, add_zero])
    (by rw [single_one_dotProduct, Pi.add_apply, hvs', Pi.single_eq_same, zero_add])
    hwa (dot_add_single hs hw') hva
  rw [one_smul, one_smul] at hf
  rw [ex_eq_two hX hrs hr hs (dot_add hw hw'), hr0, hs0, zero_sub, ev, hf, e1, e2, mul_assoc,
    (E_commute' hX (isUnimodular_single s) hva (smul_dot (-1) (dot_single hs)) hwa
      (smul_dot (-1) hwa) (dot_single hs)).left_comm]

#audit_axioms ex_add_left_of_zero

/-- `v - v_r e_r - v_s e_s`, which vanishes at `r` and `s`. -/
def qz (r s : I) (v : I → A) : I → A :=
  v - v r • Pi.single r 1 - v s • Pi.single s 1

omit [Fintype I] in
theorem qz_apply_left {r s : I} (hrs : r ≠ s) (v : I → A) : qz r s v r = 0 := by
  simp [qz, Pi.single_eq_of_ne hrs]

omit [Fintype I] in
theorem qz_apply_right {r s : I} (hrs : r ≠ s) (v : I → A) : qz r s v s = 0 := by
  simp [qz, Pi.single_eq_of_ne hrs.symm]

theorem dot_qz {r s : I} {v w : I → A} (hr : w r = 0) (hs : w s = 0) (hw : w ⬝ᵥ v = 0) :
    w ⬝ᵥ qz r s v = 0 := by
  rw [qz, dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, dot_single hr,
    dot_single hs, hw]
  simp

omit [Fintype I] in
theorem qz_add (r s : I) (v v' : I → A) : qz r s (v + v') = qz r s v + qz r s v' := by
  rw [qz, qz, qz, Pi.add_apply, Pi.add_apply]
  module

/-- `X_r(v, w) = X(e_r, v_r w) X(e_s, v_s w) X_r(v - v_r e_r - v_s e_s, w)`. -/
theorem ex_decomp {r s : I} (hrs : r ≠ s) {v w : I → A} (hr : w r = 0) (hs : w s = 0)
    (hw : w ⬝ᵥ v = 0) :
    ex hX r v w = E hX (Pi.single r 1) (v r • w) *
      (E hX (Pi.single s 1) (v s • w) * ex hX r (qz r s v) w) := by
  have hv : v = qz r s v + v s • Pi.single s 1 + v r • Pi.single r 1 := by
    rw [qz]
    module
  have hq := dot_qz hr hs hw
  conv_lhs => rw [hv]
  rw [ex_add_single_self hX hr (v r), ex_add_single_ne hX hrs hr hs hq (v s)]

#audit_axioms ex_decomp

/-- **T 1.1(a)**: `X(v + v', w) = X(v, w) X(v', w)` when `w` has two zeros `r ≠ s`. -/
theorem ex_add_left {r s : I} (hrs : r ≠ s) {v v' w : I → A} (hr : w r = 0) (hs : w s = 0)
    (hw : w ⬝ᵥ v = 0) (hw' : w ⬝ᵥ v' = 0) :
    ex hX r (v + v') w = ex hX r v w * ex hX r v' w := by
  have hu := isUnimodular_single (A := A) r
  have hu' := isUnimodular_single (A := A) s
  have hq := dot_qz hr hs hw
  have hq' := dot_qz hr hs hw'
  rw [ex_decomp hX hrs hr hs (dot_add hw hw'), ex_decomp hX hrs hr hs hw,
    ex_decomp hX hrs hr hs hw', qz_add, ex_add_left_of_zero hX hrs hr hs hq hq'
      (qz_apply_left hrs v) (qz_apply_right hrs v) (qz_apply_left hrs v')
      (qz_apply_right hrs v'),
    Pi.add_apply, Pi.add_apply, add_smul, add_smul,
    ← E_mul hX hu (smul_dot (v r) (dot_single hr)) (smul_dot (v' r) (dot_single hr)),
    ← E_mul hX hu' (smul_dot (v s) (dot_single hs)) (smul_dot (v' s) (dot_single hs))]
  simp only [mul_assoc]
  rw [(ex_commute hX hr hq hu (dot_single hr) (v' r)).left_comm,
    (E_row_commute hX hu' hu (dot_single hs) (dot_single hr) (v s) (v' r)).left_comm,
    (ex_commute hX hr hq hu' (dot_single hs) (v' s)).left_comm]

#audit_axioms ex_add_left

end Elementary

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
