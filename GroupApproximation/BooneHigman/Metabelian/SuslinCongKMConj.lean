import GroupApproximation.BooneHigman.Metabelian.SuslinCongDecideUnip
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# Krstić–McCool residual, part 1: square-zero matrices over a Euclidean domain are conjugate
into the upper unitriangular group

Lane `bh-met-92s`.

Over a Euclidean domain `D` (e.g. `K[X]`, `K` a field), every `N ∈ M₂(D)` with `N * N = 0` is
`P * (β e₁₂) * P⁻¹` for some `P ∈ GL₂(D)` and `β ∈ D` (`suslinCongKM_sqZero_conj`).  Hence
every unipotent `1 + N` is `P E₁₂(β) P⁻¹` (`suslinCongKM_unip_conj`).

Proof (all elementary): write `N = !![a, b; c, e]`.  `N² = 0` over a domain forces `a + e = 0`.
Let `d = gcd(a, c)`, `a = d v₁`, `c = d v₂`, `d = a x + c y` (Bézout), so `v₁ x + v₂ y = 1`.
`P = !![v₁, -y; v₂, x]` has inverse `!![x, y; -v₂, v₁]`; `N (v₁, v₂)ᵀ = 0` (cancel `d`), and
`N P = P !![0, β; 0, 0]` with `β = x(-a y + b x) + y(-c y + e x)`, using the trace.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- Entrywise equality of `2 × 2` matrices in `!![…]` form. -/
theorem suslinCongKM_mat_eq {D : Type*} {a b c d a' b' c' d' : D} (h1 : a = a') (h2 : b = b')
    (h3 : c = c') (h4 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h1, h2, h3, h4]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongKM_mat_eq

/-- `β e₁₂ = !![0, β; 0, 0]`. -/
theorem suslinCongKM_single_eq {D : Type*} [CommRing D] (β : D) :
    Matrix.single (0 : Fin 2) (1 : Fin 2) β = !![0, β; 0, 0] := by
  rw [Matrix.eta_fin_two (Matrix.single (0 : Fin 2) (1 : Fin 2) β)]
  exact suslinCongKM_mat_eq (Matrix.single_apply_of_ne _ _ _ _ _ (by decide))
    (Matrix.single_apply_same _ _ _) (Matrix.single_apply_of_ne _ _ _ _ _ (by decide))
    (Matrix.single_apply_of_ne _ _ _ _ _ (by decide))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongKM_single_eq

/-- The four scalar equations of `N * N = 0`. -/
theorem suslinCongKM_sq_entries {D : Type*} [CommRing D] {a b c e : D}
    (hN : !![a, b; c, e] * !![a, b; c, e] = 0) :
    a * a + b * c = 0 ∧ a * b + b * e = 0 ∧ c * a + e * c = 0 ∧ c * b + e * e = 0 := by
  rw [Matrix.mul_fin_two] at hN
  exact ⟨Matrix.ext_iff.mpr hN 0 0, Matrix.ext_iff.mpr hN 0 1, Matrix.ext_iff.mpr hN 1 0,
    Matrix.ext_iff.mpr hN 1 1⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongKM_sq_entries

/-- Over a domain, a square-zero `2 × 2` matrix has trace zero. -/
theorem suslinCongKM_trace_zero {D : Type*} [CommRing D] [IsDomain D] {a b c e : D}
    (h1 : a * a + b * c = 0) (h2 : a * b + b * e = 0) (h3 : c * a + e * c = 0)
    (h4 : c * b + e * e = 0) : a + e = 0 := by
  by_contra hne
  have hb : b = 0 := by
    have hb' : b * (a + e) = 0 := by linear_combination h2
    exact (mul_eq_zero.mp hb').resolve_right hne
  have hc : c = 0 := by
    have hc' : c * (a + e) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp hc').resolve_right hne
  have ha : a = 0 := mul_self_eq_zero.mp (by linear_combination h1 - c * hb)
  have he : e = 0 := mul_self_eq_zero.mp (by linear_combination h4 - b * hc)
  exact hne (by rw [ha, he, add_zero])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongKM_trace_zero

