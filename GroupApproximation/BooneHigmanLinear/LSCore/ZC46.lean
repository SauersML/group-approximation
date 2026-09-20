import GroupApproximation.BooneHigmanLinear.LSCore.PDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Lavrenov–Sinchuk's Lemma 4.6 (1)–(3), type A: conjugating `c_β(s, t)` by a root element

For `α = (i, j)` and `c_β(s, t) = ⁅x_β(s), x_{-β}(t)⁆ = x_β(s) z_β(-s, -t)` (`cElt_eq`):
* `c_conj_disj`: `α ⊥ β` gives `c_β(s, t)^{x_α(η)} = c_β(s, t)` (4.6(3));
* `c_conj_obtuse_row` (`β = (j, l)`) and `c_conj_obtuse_col` (`β = (k, i)`), `α + β ∈ Φ` (4.6(1));
* `c_conj_acute_row` (`β = (i, l)`) and `c_conj_acute_col` (`β = (k, j)`), `α - β ∈ Φ` (4.6(2)).
In each case `c_β(s, t)^{x_α(η)} = x_γ(·) x_α(·) c_β(s, t)`, with `γ = α ± β`. The proofs conjugate
`x_β(s)` by (R2) and `z_β(-s, -t)` by Lemma 4.1, then collect the root elements.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.RelGen (zElt cElt)

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

theorem cElt_eq' {p q : I} (hpq : p ≠ q) (s t : R) :
    cElt p q hpq s t = x p q hpq s * zElt p q hpq (-s) (-t) := by
  rw [cElt, commutatorElement_def, zElt, neg_neg, x_neg, x_neg]
  group

/-- **L–S 4.6(3)**: `c_β(s, t)` commutes with `x_α(η)` for `α ⊥ β`. -/
theorem c_conj_disj {p q k l : I} (hpq : p ≠ q) (hkl : k ≠ l) (hkp : k ≠ p) (hkq : k ≠ q)
    (hlp : l ≠ p) (hlq : l ≠ q) (s t η : R) :
    cj (x k l hkl η) (cElt p q hpq s t) = cElt p q hpq s t := by
  rw [cElt_eq', cj_mul, cj_of_commute (x_commute_of_ne k l p q hkl hpq hlp hkq.symm _ _),
    z_conj_disj hpq hkl hkp hkq hlp hlq]

#audit_axioms c_conj_disj

/-- **L–S 4.6(1)**, `α = (i, j)`, `β = (j, l)`. -/
theorem c_conj_obtuse_row {i j l : I} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (s t η : R) :
    cj (x i j hij η) (cElt j l hjl s t) =
      x i l hil (s ^ 2 * t * η) * x i j hij (-(s * t * η)) * cElt j l hjl s t := by
  rw [cElt_eq', cj_mul, cj_x_right hij hjl hil, z_conj_obtuse_row hij hjl hil]
  simp only [mul_assoc]
  rw [mv_rev hij hjl hil,
    (x_commute_of_ne j l i l hjl hil hil.symm hjl.symm _ _).left_comm,
    (x_commute_of_ne i j i l hij hil hij.symm hil.symm _ _).left_comm, x_add_tail, x_add_tail]
  congr 1
  · congr 1
    ring
  · congr 2
    ring

#audit_axioms c_conj_obtuse_row

/-- **L–S 4.6(1)**, `α = (i, j)`, `β = (k, i)`. -/
theorem c_conj_obtuse_col {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (s t η : R) :
    cj (x i j hij η) (cElt k i hki s t) =
      x k j hkj (-(s ^ 2 * t * η)) * x i j hij (-(s * t * η)) * cElt k i hki s t := by
  rw [cElt_eq', cj_mul, cj_x_left hki hij hkj, z_conj_obtuse_col hij hki hkj]
  simp only [mul_assoc]
  rw [mv_fwd hki hij hkj,
    (x_commute_of_ne k i k j hki hkj hki.symm hkj.symm _ _).left_comm,
    (x_commute_of_ne i j k j hij hkj hkj.symm hij.symm _ _).left_comm, x_add_tail, x_add_tail]
  congr 1
  · congr 1
    ring
  · congr 2
    ring

#audit_axioms c_conj_obtuse_col

/-- **L–S 4.6(2)**, `α = (i, j)`, `β = (i, l)`. -/
theorem c_conj_acute_row {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hlj : l ≠ j) (s t η : R) :
    cj (x i j hij η) (cElt i l hil s t) =
      x i j hij (s * t * η + s ^ 2 * t ^ 2 * η) * x l j hlj (s * t ^ 2 * η) *
        cElt i l hil s t := by
  rw [cElt_eq', cj_mul, cj_of_commute (x_commute_of_ne i j i l hij hil hij.symm hil.symm _ _),
    z_conj_acute_row hij hil hlj]
  simp only [mul_assoc]
  rw [(x_commute_of_ne i l i j hil hij hil.symm hij.symm _ _).left_comm, mv_fwd hil hlj hij,
    x_add_tail]
  congr 1
  · congr 1
    ring
  · congr 2
    ring

#audit_axioms c_conj_acute_row

/-- **L–S 4.6(2)**, `α = (i, j)`, `β = (k, j)`. -/
theorem c_conj_acute_col {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (s t η : R) :
    cj (x i j hij η) (cElt k j hkj s t) =
      x i j hij (s * t * η + s ^ 2 * t ^ 2 * η) * x i k hik (-(s * t ^ 2 * η)) *
        cElt k j hkj s t := by
  rw [cElt_eq', cj_mul,
    cj_of_commute (x_commute_of_ne i j k j hij hkj hkj.symm hij.symm _ _),
    z_conj_acute_col hij hik hkj]
  simp only [mul_assoc]
  rw [(x_commute_of_ne k j i j hkj hij hij.symm hkj.symm _ _).left_comm, mv_rev hik hkj hij,
    x_add_tail]
  congr 1
  · congr 1
    ring
  · congr 2
    ring

#audit_axioms c_conj_acute_col

end LSCore
end BooneHigmanLinear
end GroupApproximation
