import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPStConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugation by the Weyl element `w_ab(v)` in `St_I(R)` (bh-met-91m)

For distinct `a, b, k` (and `l`), with `w = w_ab(v)`:

* `w x_ak(r) w⁻¹ = x_bk(-v⁻¹ r)`, `w x_bk(r) w⁻¹ = x_ak(v r)`,
* `w x_ka(r) w⁻¹ = x_kb(-(r v))`, `w x_kb(r) w⁻¹ = x_ka(r v⁻¹)`,
* `w x_kl(r) w⁻¹ = x_kl(r)` when `k, l ∉ {a, b}`.

Each is three single conjugations (`ElemFPCharZeroStFourFPStConj`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

theorem czStFourFP_w_conj_ak (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (v : Rˣ)
    (r : R) : czStFourFP_w a b hab v * SteinbergGroup.x a k hak r * (czStFourFP_w a b hab v)⁻¹ =
      SteinbergGroup.x b k hbk (-((v⁻¹ : Rˣ) : R) * r) := by
  have h1 := czStFourFP_conj_comm a b a k hab hak hab.symm hak.symm (v : R) r
  have h2 := czStFourFP_conj_adj b a k hab.symm hak hbk (-((v⁻¹ : Rˣ) : R)) r
  have hc : (v : R) * (-((v⁻¹ : Rˣ) : R) * r) + r = 0 := by
    rw [neg_mul, mul_neg, ← mul_assoc, Units.mul_inv, one_mul, neg_add_cancel]
  have h3 : SteinbergGroup.x a b hab (v : R) * (SteinbergGroup.x b k hbk (-((v⁻¹ : Rˣ) : R) * r) *
      SteinbergGroup.x a k hak r) * (SteinbergGroup.x a b hab (v : R))⁻¹ =
      SteinbergGroup.x b k hbk (-((v⁻¹ : Rˣ) : R) * r) := by
    rw [czStFourFP_conj_mul (SteinbergGroup.x a b hab (v : R)),
      czStFourFP_conj_adj a b k hab hbk hak (v : R), h1,
      (SteinbergGroup.x_commute_of_ne a k b k hak hbk hbk.symm hak.symm _ _).eq, mul_assoc,
      SteinbergGroup.x_mul, hc, SteinbergGroup.x_zero, mul_one]
  rw [czStFourFP_w, czStFourFP_conj3, h1, h2, h3]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_w_conj_ak

theorem czStFourFP_w_conj_bk (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (v : Rˣ)
    (r : R) : czStFourFP_w a b hab v * SteinbergGroup.x b k hbk r * (czStFourFP_w a b hab v)⁻¹ =
      SteinbergGroup.x a k hak ((v : R) * r) := by
  have h1 := czStFourFP_conj_adj a b k hab hbk hak (v : R) r
  have hc : -((v⁻¹ : Rˣ) : R) * ((v : R) * r) + r = 0 := by
    rw [neg_mul, ← mul_assoc, Units.inv_mul, one_mul, neg_add_cancel]
  have h2 : SteinbergGroup.x b a hab.symm (-((v⁻¹ : Rˣ) : R)) *
      (SteinbergGroup.x a k hak ((v : R) * r) * SteinbergGroup.x b k hbk r) *
      (SteinbergGroup.x b a hab.symm (-((v⁻¹ : Rˣ) : R)))⁻¹ =
      SteinbergGroup.x a k hak ((v : R) * r) := by
    rw [czStFourFP_conj_mul (SteinbergGroup.x b a hab.symm (-((v⁻¹ : Rˣ) : R))),
      czStFourFP_conj_adj b a k hab.symm hak hbk (-((v⁻¹ : Rˣ) : R)) ((v : R) * r),
      czStFourFP_conj_comm b a b k hab.symm hbk hab hbk.symm (-((v⁻¹ : Rˣ) : R)) r,
      (SteinbergGroup.x_commute_of_ne b k a k hbk hak hak.symm hbk.symm _ _).eq, mul_assoc,
      SteinbergGroup.x_mul, hc, SteinbergGroup.x_zero, mul_one]
  have h3 := czStFourFP_conj_comm a b a k hab hak hab.symm hak.symm (v : R) ((v : R) * r)
  rw [czStFourFP_w, czStFourFP_conj3, h1, h2, h3]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_w_conj_bk

theorem czStFourFP_w_conj_ka (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (v : Rˣ)
    (r : R) : czStFourFP_w a b hab v * SteinbergGroup.x k a hak.symm r *
      (czStFourFP_w a b hab v)⁻¹ = SteinbergGroup.x k b hbk.symm (-(r * (v : R))) := by
  have h1 := czStFourFP_conj_adj' a b k hab hak.symm hbk.symm (v : R) r
  have hc : r + -(-(r * (v : R)) * -((v⁻¹ : Rˣ) : R)) = 0 := by
    rw [neg_mul_neg, mul_assoc, Units.mul_inv, mul_one, add_neg_cancel]
  have h2 : SteinbergGroup.x b a hab.symm (-((v⁻¹ : Rˣ) : R)) *
      (SteinbergGroup.x k a hak.symm r * SteinbergGroup.x k b hbk.symm (-(r * (v : R)))) *
      (SteinbergGroup.x b a hab.symm (-((v⁻¹ : Rˣ) : R)))⁻¹ =
      SteinbergGroup.x k b hbk.symm (-(r * (v : R))) := by
    rw [czStFourFP_conj_mul (SteinbergGroup.x b a hab.symm (-((v⁻¹ : Rˣ) : R))),
      czStFourFP_conj_comm b a k a hab.symm hak.symm hak hab (-((v⁻¹ : Rˣ) : R)) r,
      czStFourFP_conj_adj' b a k hab.symm hbk.symm hak.symm (-((v⁻¹ : Rˣ) : R))
        (-(r * (v : R))),
      ← mul_assoc, (SteinbergGroup.x_commute_of_ne k a k b hak.symm hbk.symm hak hbk _ _).eq,
      mul_assoc, SteinbergGroup.x_mul, hc, SteinbergGroup.x_zero, mul_one]
  have h3 := czStFourFP_conj_comm a b k b hab hbk.symm hbk hab.symm (v : R) (-(r * (v : R)))
  rw [czStFourFP_w, czStFourFP_conj3, h1, h2, h3]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_w_conj_ka

theorem czStFourFP_w_conj_kb (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (v : Rˣ)
    (r : R) : czStFourFP_w a b hab v * SteinbergGroup.x k b hbk.symm r *
      (czStFourFP_w a b hab v)⁻¹ = SteinbergGroup.x k a hak.symm (r * ((v⁻¹ : Rˣ) : R)) := by
  have h1 := czStFourFP_conj_comm a b k b hab hbk.symm hbk hab.symm (v : R) r
  have h2 : SteinbergGroup.x b a hab.symm (-((v⁻¹ : Rˣ) : R)) * SteinbergGroup.x k b hbk.symm r *
      (SteinbergGroup.x b a hab.symm (-((v⁻¹ : Rˣ) : R)))⁻¹ =
      SteinbergGroup.x k b hbk.symm r * SteinbergGroup.x k a hak.symm (r * ((v⁻¹ : Rˣ) : R)) := by
    rw [czStFourFP_conj_adj' b a k hab.symm hbk.symm hak.symm, mul_neg, neg_neg]
  have hc : r + -(r * ((v⁻¹ : Rˣ) : R) * (v : R)) = 0 := by
    rw [mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]
  have h3 : SteinbergGroup.x a b hab (v : R) * (SteinbergGroup.x k b hbk.symm r *
      SteinbergGroup.x k a hak.symm (r * ((v⁻¹ : Rˣ) : R))) *
      (SteinbergGroup.x a b hab (v : R))⁻¹ =
      SteinbergGroup.x k a hak.symm (r * ((v⁻¹ : Rˣ) : R)) := by
    rw [czStFourFP_conj_mul (SteinbergGroup.x a b hab (v : R)), h1,
      czStFourFP_conj_adj' a b k hab hak.symm hbk.symm (v : R), ← mul_assoc,
      (SteinbergGroup.x_commute_of_ne k b k a hbk.symm hak.symm hbk hak _ _).eq, mul_assoc,
      SteinbergGroup.x_mul, hc, SteinbergGroup.x_zero, mul_one]
  rw [czStFourFP_w, czStFourFP_conj3, h1, h2, h3]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_w_conj_kb

theorem czStFourFP_w_conj_kl (a b k l : I) (hab : a ≠ b) (hkl : k ≠ l) (hak : a ≠ k)
    (hbk : b ≠ k) (hal : a ≠ l) (hbl : b ≠ l) (v : Rˣ) (r : R) :
    czStFourFP_w a b hab v * SteinbergGroup.x k l hkl r * (czStFourFP_w a b hab v)⁻¹ =
      SteinbergGroup.x k l hkl r := by
  rw [czStFourFP_w, czStFourFP_conj3,
    czStFourFP_conj_comm a b k l hab hkl hbk hal.symm (v : R) r,
    czStFourFP_conj_comm b a k l hab.symm hkl hak hbl.symm _ r,
    czStFourFP_conj_comm a b k l hab hkl hbk hal.symm (v : R) r]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_w_conj_kl

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
