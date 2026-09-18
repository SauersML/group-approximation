import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWeylEquiv
import GroupApproximation.Meta.AxiomGuard

/-!
# The Weyl check of `σ`, part 5: the columns with `b = 0` or `deg b < deg a`

Lane `bh-met-93d`.  Notation of `ElemFPK2PolyNagaoWeylEquiv`.  For `v = (a, b)` on the
`(m, L)` coordinates, `W v = (-b, a)`, so the Weyl check element at `v` is
`D(a, b) = (pair (-b) a)⁻¹ · W · pair a b`.  Here it is `1` in two cases:

* `k2PolyNagaoWeyl_check_pair_zero`: `b = 0`, `a = C α`.  Then
  `D = t(α) W W t(-α)⁻¹ = t(α) t(-1) t(-α)⁻¹ = 1`.
* `k2PolyNagaoWeyl_check_pair_lt`: `b ≠ 0`, `deg b < deg a`.  With `q = a / b`, `r = a % b`:
  `pair a b = W x'(-q) W pair (-r) (-b)` and `pair (-b) a = x'(-q) W pair r b`.  As `W W = t(-1)`
  commutes with every `x'(f)`, `D = (pair r b)⁻¹ t(-1) pair (-r) (-b)`, which is `1` by torus
  equivariance (`k2PolyNagaoWeyl_torus_mul_pair` at `δ = -1`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- `C(-1) = -1`. -/
theorem k2PolyNagaoWeyl_C_neg_one :
    Polynomial.C ((-1 : (ZMod p)ˣ) : ZMod p) = -1 := by
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_C_neg_one

/-- `C((-1)⁻¹) = -1`. -/
theorem k2PolyNagaoWeyl_C_inv_neg_one :
    Polynomial.C (((-1 : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) = -1 := by
  rw [inv_neg, inv_one, Units.val_neg, Units.val_one, map_neg, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_C_inv_neg_one

variable {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)

include hmn hLn

/-- `W W = t(-1)` commutes with every `x'(f)`. -/
theorem k2PolyNagaoWeyl_WW_comm (f : Polynomial (ZMod p)) :
    w m L hmL (-1 : (Polynomial (ZMod p))ˣ) * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) *
        x L m hmL.symm f =
      x L m hmL.symm f *
        (w m L hmL (-1 : (Polynomial (ZMod p))ˣ) * w m L hmL (-1 : (Polynomial (ZMod p))ˣ)) := by
  rw [k2PolyNagaoWeyl_W_mul_W hmL hmn hLn, k2PolyNagaoWeyl_torus_mul_x hmL hmn hLn,
    k2PolyNagaoWeyl_C_inv_neg_one, neg_one_mul, mul_neg_one, neg_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_WW_comm

/-- **Case `b = 0`.**  The check element at the column `(a, 0)`, `a` a unit, is `1`. -/
theorem k2PolyNagaoWeyl_check_pair_zero {a : Polynomial (ZMod p)} (ha : IsUnit a) :
    (k2PolyNagaoSigma_pair p m L hmL (-0) a)⁻¹ * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) *
      k2PolyNagaoSigma_pair p m L hmL a 0 = 1 := by
  obtain ⟨α, rfl⟩ := k2PolyNagaoWeyl_exists_C_of_isUnit ha
  have hα : Polynomial.C (α : ZMod p) ≠ 0 := Polynomial.C_ne_zero.2 α.ne_zero
  have h0 : (0 : Polynomial (ZMod p)).degree < (Polynomial.C (α : ZMod p)).degree := by
    rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.2 fun h => hα (Polynomial.degree_eq_bot.1 h)
  obtain ⟨hq, hr⟩ := k2PolyNagaoWeyl_divmod_small hα h0
  have hn : -Polynomial.C (α : ZMod p) = Polynomial.C ((-α : (ZMod p)ˣ) : ZMod p) := by
    rw [Units.val_neg, map_neg]
  have e : ∀ A V B : SteinbergGroup I (Polynomial (ZMod p)),
      A * V * (V * B) = A * (V * V) * B := fun A V B => by group
  rw [neg_zero, k2PolyNagaoSigma_pair_zero, k2PolyNagaoSigma_pair_of_ne p m L hmL hα, hq, hr,
    x_zero, one_mul, k2PolyNagaoSigma_pair_zero, hn, k2PolyNagaoWeyl_tau_C hmL hmn hLn,
    k2PolyNagaoWeyl_tau_C hmL hmn hLn, inv_inv, e, k2PolyNagaoWeyl_W_mul_W hmL hmn hLn,
    ← map_mul (k2PolyDeg_torus p m L n hmL hmn hLn), mul_neg_one, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_check_pair_zero

/-- **Case `deg b < deg a`.**  The check element at a coprime column `(a, b)` with `b ≠ 0` and
`deg b < deg a` is `1`. -/
theorem k2PolyNagaoWeyl_check_pair_lt {a b : Polynomial (ZMod p)} (hab : IsCoprime a b)
    (hb : b ≠ 0) (hlt : b.degree < a.degree) :
    (k2PolyNagaoSigma_pair p m L hmL (-b) a)⁻¹ * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) *
      k2PolyNagaoSigma_pair p m L hmL a b = 1 := by
  have ha : a ≠ 0 := Polynomial.ne_zero_of_degree_gt hlt
  obtain ⟨hq0, hr0⟩ := k2PolyNagaoWeyl_divmod_small ha hlt
  obtain ⟨hq1, hr1⟩ := k2PolyNagaoWeyl_divmod_neg_left a hb
  obtain ⟨hq2, hr2⟩ := k2PolyNagaoWeyl_divmod_neg_right a hb
  have h1 : b * (a / b) + a % b = a := EuclideanDomain.div_add_mod a b
  have hcop : IsCoprime (-(a % b)) (-b) := k2PolyNagaoWeyl_isCoprime_of_comb hab
    (x1 := -1) (y1 := -(a / b)) (x2 := 0) (y2 := -1) (by linear_combination -h1) (by ring)
  have hE := k2PolyNagaoWeyl_torus_mul_pair hmL hmn hLn (-(a % b)) (-1) (-b) hcop
  rw [k2PolyNagaoWeyl_C_inv_neg_one, k2PolyNagaoWeyl_C_neg_one, neg_one_mul, neg_one_mul,
    neg_neg, neg_neg] at hE
  have g : ∀ X Y Z V : SteinbergGroup I (Polynomial (ZMod p)), V * V * X = X * (V * V) →
      (X * V * Y)⁻¹ * V * (V * (X * V * Z)) = Y⁻¹ * (V * V * Z) := by
    intro X Y Z V h
    have e1 : (X * V * Y)⁻¹ * V * (V * (X * V * Z)) =
        Y⁻¹ * V⁻¹ * X⁻¹ * (V * V * X) * V * Z := by group
    rw [e1, h]
    group
  rw [k2PolyNagaoSigma_pair_of_ne p m L hmL ha, hq0, hr0, x_zero, one_mul,
    k2PolyNagaoSigma_pair_of_ne p m L hmL hb, hq1, hr1,
    k2PolyNagaoSigma_pair_of_ne p m L hmL (neg_ne_zero.2 hb), hq2, hr2, neg_neg,
    g _ _ _ _ (k2PolyNagaoWeyl_WW_comm hmL hmn hLn (-(a / b))),
    k2PolyNagaoWeyl_W_mul_W hmL hmn hLn, hE, inv_mul_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_check_pair_lt

end GroupApproximation.BooneHigman.Metabelian.ElemFP
