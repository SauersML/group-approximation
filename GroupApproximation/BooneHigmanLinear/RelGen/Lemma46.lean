import GroupApproximation.BooneHigmanLinear.RelGen.ZTools
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# L–S Lemma 4.6 (1)–(3) in type A: `⁅c_α(s, t), x_β(ξ)⁆` for `β ≠ ±α` (k2-poly H.L3)

Lane k2-hl3b. A. Lavrenov and S. Sinchuk, arXiv:1909.02637, §4.1, Lemma 4.6 (1)–(3), for
`α = (i, j)` in type A, with `c_ij(s, t) = ⁅x_ij(s), x_ji(t)⁆` (`RelGen.cElt`) and Mathlib's
`⁅g, h⁆ = g h g⁻¹ h⁻¹`. For `β ≠ ±α` there are five cases, with `k, l ∉ {i, j}`:

* `comm_cElt_x_il`: `⁅c_ij(s,t), x_il(ξ)⁆ = x_jl(s t² ξ) · x_il(s t ξ + s² t² ξ)`;
* `comm_cElt_x_jl`: `⁅c_ij(s,t), x_jl(ξ)⁆ = x_jl(-(s t ξ)) · x_il(-(s² t ξ))`;
* `comm_cElt_x_ki`: `⁅c_ij(s,t), x_ki(ξ)⁆ = x_ki(-(s t ξ)) · x_kj(s² t ξ)`;
* `comm_cElt_x_kj`: `⁅c_ij(s,t), x_kj(ξ)⁆ = x_ki(-(s t² ξ)) · x_kj(s t ξ + s² t² ξ)`;
* `comm_cElt_x_disj`: `⁅c_ij(s,t), x_kl(ξ)⁆ = 1`.

Method: the two root elements that appear span an abelian subgroup, parametrized as `blkL a b =
x_jl(a) x_il(b)` (column `l`) or `blkK a b = x_ki(a) x_kj(b)` (row `k`). Conjugation by `x_ij(u)`
and `x_ji(u)` acts on the parameters by explicit linear maps (`blkL_conj_ij`, ...), and
`c y c⁻¹` is four such conjugations (`cElt_conj_expand`). The coefficients are closed by `ring`.
The membership and `st = 0` consequences are in `RelGen.Lemma46Mem`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

section GroupFacts

variable {G : Type*} [Group G]

theorem ls_conj_self {g y : G} (h : Commute g y) : g * y * g⁻¹ = y := by
  rw [h.eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.ls_conj_self

theorem ls_conj_mul (g y y' : G) : g * (y * y') * g⁻¹ = g * y * g⁻¹ * (g * y' * g⁻¹) := by
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.ls_conj_mul

end GroupFacts

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

section Moves

/-- `x_pq(a) x_qr(b) x_pq(a)⁻¹ = x_pr(ab) x_qr(b)`. -/
theorem x_conj_fwd {p q r : I} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) (a b : R) :
    x p q hpq a * x q r hqr b * (x p q hpq a)⁻¹ = x p r hpr (a * b) * x q r hqr b := by
  rw [← x_commutator p q r hpq hqr hpr a b, commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.x_conj_fwd

/-- `x_qr(b) x_pq(a) x_qr(b)⁻¹ = x_pr(-(ab)) x_pq(a)`. -/
theorem x_conj_rev {p q r : I} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) (a b : R) :
    x q r hqr b * x p q hpq a * (x q r hqr b)⁻¹ = x p r hpr (-(a * b)) * x p q hpq a := by
  rw [x_neg, ← x_commutator p q r hpq hqr hpr a b, commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.x_conj_rev

theorem x_mul_x_congr {p q p' q' : I} {h : p ≠ q} {h' : p' ≠ q'} {a a' b b' : R}
    (ha : a = a') (hb : b = b') : x p q h a * x p' q' h' b = x p q h a' * x p' q' h' b' := by
  rw [ha, hb]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.x_mul_x_congr

/-- `c y c⁻¹` as four conjugations by root elements. -/
theorem cElt_conj_expand (i j : I) (hij : i ≠ j) (s t : R) (y : SteinbergGroup I R) :
    cElt i j hij s t * y * (cElt i j hij s t)⁻¹ =
      x i j hij s * (x j i hij.symm t * (x i j hij (-s) * (x j i hij.symm (-t) * y *
        (x j i hij.symm (-t))⁻¹) * (x i j hij (-s))⁻¹) * (x j i hij.symm t)⁻¹) *
        (x i j hij s)⁻¹ := by
  simp only [cElt, commutatorElement_def, x_neg]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_conj_expand

end Moves

section BlockL

variable {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)

/-- The column-`l` block `x_jl(a) · x_il(b)`. -/
def blkL (a b : R) : SteinbergGroup I R := x j l hjl a * x i l hil b

theorem blkL_comm (a b : R) : x i l hil b * x j l hjl a = x j l hjl a * x i l hil b :=
  (x_commute_of_ne i l j l hil hjl hjl.symm hil.symm b a).eq

theorem blkL_mul (a b a' b' : R) :
    blkL hil hjl a b * blkL hil hjl a' b' = blkL hil hjl (a + a') (b + b') := by
  unfold blkL
  calc x j l hjl a * x i l hil b * (x j l hjl a' * x i l hil b')
      = x j l hjl a * (x i l hil b * x j l hjl a') * x i l hil b' := by group
    _ = x j l hjl a * (x j l hjl a' * x i l hil b) * x i l hil b' := by
        rw [blkL_comm hil hjl a' b]
    _ = x j l hjl a * x j l hjl a' * (x i l hil b * x i l hil b') := by group
    _ = x j l hjl (a + a') * x i l hil (b + b') := by rw [x_mul, x_mul]

theorem blkL_inv (a b : R) : (blkL hil hjl a b)⁻¹ = blkL hil hjl (-a) (-b) := by
  unfold blkL
  rw [mul_inv_rev, ← x_neg, ← x_neg]
  exact blkL_comm hil hjl (-a) (-b)

/-- Conjugation by `x_ji(u)`: `(a, b) ↦ (a + u b, b)`. -/
theorem blkL_conj_ji (hji : j ≠ i) (u a b : R) :
    x j i hji u * blkL hil hjl a b * (x j i hji u)⁻¹ = blkL hil hjl (a + u * b) b := by
  unfold blkL
  rw [ls_conj_mul, ls_conj_self (x_commute_of_ne j i j l hji hjl hji.symm hjl.symm u a),
    x_conj_fwd hji hil hjl u b, ← mul_assoc, x_mul]

/-- Conjugation by `x_ij(u)`: `(a, b) ↦ (a, u a + b)`. -/
theorem blkL_conj_ij (u a b : R) :
    x i j hij u * blkL hil hjl a b * (x i j hij u)⁻¹ = blkL hil hjl a (u * a + b) := by
  unfold blkL
  rw [ls_conj_mul, x_conj_fwd hij hjl hil u a,
    ls_conj_self (x_commute_of_ne i j i l hij hil hij.symm hil.symm u b),
    blkL_comm hil hjl a (u * a), mul_assoc, x_mul]

end BlockL

section BlockK

variable {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)

/-- The row-`k` block `x_ki(a) · x_kj(b)`. -/
def blkK (a b : R) : SteinbergGroup I R := x k i hki a * x k j hkj b

theorem blkK_comm (a b : R) : x k j hkj b * x k i hki a = x k i hki a * x k j hkj b :=
  (x_commute_of_ne k j k i hkj hki hkj.symm hki.symm b a).eq

theorem blkK_mul (a b a' b' : R) :
    blkK hki hkj a b * blkK hki hkj a' b' = blkK hki hkj (a + a') (b + b') := by
  unfold blkK
  calc x k i hki a * x k j hkj b * (x k i hki a' * x k j hkj b')
      = x k i hki a * (x k j hkj b * x k i hki a') * x k j hkj b' := by group
    _ = x k i hki a * (x k i hki a' * x k j hkj b) * x k j hkj b' := by
        rw [blkK_comm hki hkj a' b]
    _ = x k i hki a * x k i hki a' * (x k j hkj b * x k j hkj b') := by group
    _ = x k i hki (a + a') * x k j hkj (b + b') := by rw [x_mul, x_mul]

theorem blkK_inv (a b : R) : (blkK hki hkj a b)⁻¹ = blkK hki hkj (-a) (-b) := by
  unfold blkK
  rw [mul_inv_rev, ← x_neg, ← x_neg]
  exact blkK_comm hki hkj (-a) (-b)

/-- Conjugation by `x_ji(u)`: `(a, b) ↦ (a - b u, b)`. -/
theorem blkK_conj_ji (hji : j ≠ i) (u a b : R) :
    x j i hji u * blkK hki hkj a b * (x j i hji u)⁻¹ = blkK hki hkj (a + -(b * u)) b := by
  unfold blkK
  rw [ls_conj_mul, ls_conj_self (x_commute_of_ne j i k i hji hki hki.symm hji.symm u a),
    x_conj_rev hkj hji hki b u, ← mul_assoc, x_mul]

/-- Conjugation by `x_ij(u)`: `(a, b) ↦ (a, b - a u)`. -/
theorem blkK_conj_ij (u a b : R) :
    x i j hij u * blkK hki hkj a b * (x i j hij u)⁻¹ = blkK hki hkj a (-(a * u) + b) := by
  unfold blkK
  rw [ls_conj_mul, x_conj_rev hki hij hkj a u,
    ls_conj_self (x_commute_of_ne i j k j hij hkj hkj.symm hij.symm u b),
    blkK_comm hki hkj a (-(a * u)), mul_assoc, x_mul]

end BlockK

section Lemma46

/-- **L–S 4.6(2)**, `β = (i, l)`. -/
theorem comm_cElt_x_il {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (s t ξ : R) :
    ⁅cElt i j hij s t, x i l hil ξ⁆ =
      x j l hjl (s * t ^ 2 * ξ) * x i l hil (s * t * ξ + s ^ 2 * t ^ 2 * ξ) := by
  have hy : x i l hil ξ = blkL hil hjl 0 ξ := by rw [blkL, x_zero, one_mul]
  rw [commutatorElement_def, cElt_conj_expand, hy, blkL_conj_ji hil hjl,
    blkL_conj_ij hij hil hjl, blkL_conj_ji hil hjl, blkL_conj_ij hij hil hjl, blkL_inv,
    blkL_mul, blkL]
  exact x_mul_x_congr (by ring) (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.comm_cElt_x_il

/-- **L–S 4.6(1)**, `β = (j, l)`. -/
theorem comm_cElt_x_jl {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (s t ξ : R) :
    ⁅cElt i j hij s t, x j l hjl ξ⁆ =
      x j l hjl (-(s * t * ξ)) * x i l hil (-(s ^ 2 * t * ξ)) := by
  have hy : x j l hjl ξ = blkL hil hjl ξ 0 := by rw [blkL, x_zero, mul_one]
  rw [commutatorElement_def, cElt_conj_expand, hy, blkL_conj_ji hil hjl,
    blkL_conj_ij hij hil hjl, blkL_conj_ji hil hjl, blkL_conj_ij hij hil hjl, blkL_inv,
    blkL_mul, blkL]
  exact x_mul_x_congr (by ring) (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.comm_cElt_x_jl

/-- **L–S 4.6(1)**, `β = (k, i)`. -/
theorem comm_cElt_x_ki {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (s t ξ : R) :
    ⁅cElt i j hij s t, x k i hki ξ⁆ =
      x k i hki (-(s * t * ξ)) * x k j hkj (s ^ 2 * t * ξ) := by
  have hy : x k i hki ξ = blkK hki hkj ξ 0 := by rw [blkK, x_zero, mul_one]
  rw [commutatorElement_def, cElt_conj_expand, hy, blkK_conj_ji hki hkj,
    blkK_conj_ij hij hki hkj, blkK_conj_ji hki hkj, blkK_conj_ij hij hki hkj, blkK_inv,
    blkK_mul, blkK]
  exact x_mul_x_congr (by ring) (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.comm_cElt_x_ki

/-- **L–S 4.6(2)**, `β = (k, j)`. -/
theorem comm_cElt_x_kj {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (s t ξ : R) :
    ⁅cElt i j hij s t, x k j hkj ξ⁆ =
      x k i hki (-(s * t ^ 2 * ξ)) * x k j hkj (s * t * ξ + s ^ 2 * t ^ 2 * ξ) := by
  have hy : x k j hkj ξ = blkK hki hkj 0 ξ := by rw [blkK, x_zero, one_mul]
  rw [commutatorElement_def, cElt_conj_expand, hy, blkK_conj_ji hki hkj,
    blkK_conj_ij hij hki hkj, blkK_conj_ji hki hkj, blkK_conj_ij hij hki hkj, blkK_inv,
    blkK_mul, blkK]
  exact x_mul_x_congr (by ring) (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.comm_cElt_x_kj

/-- **L–S 4.6(3)**, `β ⊥ α`. -/
theorem comm_cElt_x_disj {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) (s t ξ : R) : ⁅cElt i j hij s t, x k l hkl ξ⁆ = 1 := by
  have h1 := x_commute_of_ne i j k l hij hkl hkj.symm hli s ξ
  have h2 := x_commute_of_ne j i k l hij.symm hkl hki.symm hlj t ξ
  have hc : Commute (cElt i j hij s t) (x k l hkl ξ) := by
    rw [show cElt i j hij s t = ⁅x i j hij s, x j i hij.symm t⁆ from rfl, commutatorElement_def]
    exact ((h1.mul_left h2).mul_left h1.inv_left).mul_left h2.inv_left
  exact commutatorElement_eq_one_iff_mul_comm.mpr hc.eq

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.comm_cElt_x_disj

end Lemma46

end GroupApproximation.BooneHigmanLinear.RelGen
