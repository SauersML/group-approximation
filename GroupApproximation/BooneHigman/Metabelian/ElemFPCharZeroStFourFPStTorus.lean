import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPStWeyl
import GroupApproximation.Meta.AxiomGuard

/-!
# Torus elements `H_ab(v) = w_ab(v) w_ab(1)⁻¹` in `St_I(R)` (bh-met-91m)

For distinct `a, b, k` (and `l`) and `H = H_ab(v)`:

* `H x_ak(r) H⁻¹ = x_ak(v r)`, `H x_bk(r) H⁻¹ = x_bk(v⁻¹ r)`,
* `H x_ka(r) H⁻¹ = x_ka(r v⁻¹)`, `H x_kb(r) H⁻¹ = x_kb(r v)`,
* `H x_kl(r) H⁻¹ = x_kl(r)` for `k, l ∉ {a, b}`.

Proof: invert the Weyl conjugations at `v = 1`, then conjugate by `w_ab(v)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- Inverting a conjugation identity. -/
theorem czStFourFP_conj_inv_of {G : Type*} [Group G] {g y z : G} (h : g * y * g⁻¹ = z) :
    g⁻¹ * z * g = y := by
  rw [← h]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_inv_of

/-- Conjugation by `w w₁⁻¹`. -/
theorem czStFourFP_conj_H {G : Type*} [Group G] (w w₁ h : G) :
    w * w₁⁻¹ * h * (w * w₁⁻¹)⁻¹ = w * (w₁⁻¹ * h * w₁) * w⁻¹ := by
  simp only [mul_inv_rev, inv_inv, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_H

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

/-- The torus element `H_ab(v) = w_ab(v) w_ab(1)⁻¹`. -/
def czStFourFP_H (a b : I) (hab : a ≠ b) (v : Rˣ) : SteinbergGroup I R :=
  czStFourFP_w a b hab v * (czStFourFP_w a b hab 1)⁻¹

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H

section Inverse

variable (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (r : R)

theorem czStFourFP_winv_ak : (czStFourFP_w a b hab 1)⁻¹ * SteinbergGroup.x a k hak r *
    czStFourFP_w a b hab 1 = SteinbergGroup.x b k hbk r := by
  have h := czStFourFP_w_conj_bk a b k hab hak hbk 1 r
  rw [Units.val_one, one_mul] at h
  exact czStFourFP_conj_inv_of h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_winv_ak

theorem czStFourFP_winv_bk : (czStFourFP_w a b hab 1)⁻¹ * SteinbergGroup.x b k hbk r *
    czStFourFP_w a b hab 1 = SteinbergGroup.x a k hak (-r) := by
  have h := czStFourFP_w_conj_ak a b k hab hak hbk 1 (-r)
  rw [inv_one, Units.val_one, neg_mul, one_mul, neg_neg] at h
  exact czStFourFP_conj_inv_of h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_winv_bk

theorem czStFourFP_winv_ka : (czStFourFP_w a b hab 1)⁻¹ * SteinbergGroup.x k a hak.symm r *
    czStFourFP_w a b hab 1 = SteinbergGroup.x k b hbk.symm r := by
  have h := czStFourFP_w_conj_kb a b k hab hak hbk 1 r
  rw [inv_one, Units.val_one, mul_one] at h
  exact czStFourFP_conj_inv_of h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_winv_ka

theorem czStFourFP_winv_kb : (czStFourFP_w a b hab 1)⁻¹ * SteinbergGroup.x k b hbk.symm r *
    czStFourFP_w a b hab 1 = SteinbergGroup.x k a hak.symm (-r) := by
  have h := czStFourFP_w_conj_ka a b k hab hak hbk 1 (-r)
  rw [Units.val_one, mul_one, neg_neg] at h
  exact czStFourFP_conj_inv_of h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_winv_kb

end Inverse

section Torus

theorem czStFourFP_H_ak (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (v : Rˣ)
    (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x a k hak r *
      (czStFourFP_H a b hab v)⁻¹ = SteinbergGroup.x a k hak ((v : R) * r) := by
  rw [czStFourFP_H, czStFourFP_conj_H, czStFourFP_winv_ak a b k hab hak hbk,
    czStFourFP_w_conj_bk a b k hab hak hbk]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_ak

theorem czStFourFP_H_bk (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (v : Rˣ)
    (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x b k hbk r *
      (czStFourFP_H a b hab v)⁻¹ = SteinbergGroup.x b k hbk (((v⁻¹ : Rˣ) : R) * r) := by
  rw [czStFourFP_H, czStFourFP_conj_H, czStFourFP_winv_bk a b k hab hak hbk,
    czStFourFP_w_conj_ak a b k hab hak hbk, neg_mul_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_bk

theorem czStFourFP_H_ka (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (v : Rˣ)
    (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x k a hak.symm r *
      (czStFourFP_H a b hab v)⁻¹ =
        SteinbergGroup.x k a hak.symm (r * ((v⁻¹ : Rˣ) : R)) := by
  rw [czStFourFP_H, czStFourFP_conj_H, czStFourFP_winv_ka a b k hab hak hbk,
    czStFourFP_w_conj_kb a b k hab hak hbk]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_ka

theorem czStFourFP_H_kb (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (v : Rˣ)
    (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x k b hbk.symm r *
      (czStFourFP_H a b hab v)⁻¹ = SteinbergGroup.x k b hbk.symm (r * (v : R)) := by
  rw [czStFourFP_H, czStFourFP_conj_H, czStFourFP_winv_kb a b k hab hak hbk,
    czStFourFP_w_conj_ka a b k hab hak hbk, neg_mul, neg_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_kb

theorem czStFourFP_H_kl (a b k l : I) (hab : a ≠ b) (hkl : k ≠ l) (hak : a ≠ k) (hbk : b ≠ k)
    (hal : a ≠ l) (hbl : b ≠ l) (v : Rˣ) (r : R) :
    czStFourFP_H a b hab v * SteinbergGroup.x k l hkl r * (czStFourFP_H a b hab v)⁻¹ =
      SteinbergGroup.x k l hkl r := by
  have h := czStFourFP_w_conj_kl a b k l hab hkl hak hbk hal hbl 1 r
  rw [czStFourFP_H, czStFourFP_conj_H, czStFourFP_conj_inv_of h,
    czStFourFP_w_conj_kl a b k l hab hkl hak hbk hal hbl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_kl

end Torus

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
