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

/-- **Square-zero matrices are conjugate to `β e₁₂`** (entrywise form). -/
theorem suslinCongKM_sqZero_conj_entries {D : Type*} [EuclideanDomain D] (a b c e : D)
    (hN : !![a, b; c, e] * !![a, b; c, e] = 0) :
    ∃ P : (Matrix (Fin 2) (Fin 2) D)ˣ, ∃ β : D,
      (P : Matrix (Fin 2) (Fin 2) D) * Matrix.single 0 1 β * ↑P⁻¹ = !![a, b; c, e] := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := suslinCongKM_sq_entries hN
  have htr := suslinCongKM_trace_zero h1 h2 h3 h4
  by_cases hd : EuclideanDomain.gcd a c = 0
  · obtain ⟨ha, hc⟩ := EuclideanDomain.gcd_eq_zero_iff.mp hd
    have he : e = 0 := by linear_combination htr - ha
    refine ⟨1, b, ?_⟩
    rw [inv_one, Units.val_one, one_mul, mul_one, suslinCongKM_single_eq, ha, hc, he]
  obtain ⟨d, hd0, hv1', hv2', hB'⟩ :
      ∃ d : D, d ≠ 0 ∧ d ∣ a ∧ d ∣ c ∧ ∃ x y : D, d = a * x + c * y :=
    ⟨_, hd, EuclideanDomain.gcd_dvd_left a c, EuclideanDomain.gcd_dvd_right a c, _, _,
      EuclideanDomain.gcd_eq_gcd_ab a c⟩
  obtain ⟨v1, hv1⟩ := hv1'
  obtain ⟨v2, hv2⟩ := hv2'
  obtain ⟨x, y, hB⟩ := hB'
  have hu : v1 * x + v2 * y = 1 :=
    mul_left_cancel₀ hd0 (by linear_combination (-x) * hv1 + (-y) * hv2 - hB)
  have g1 : a * v1 + b * v2 = 0 :=
    mul_left_cancel₀ hd0 (by linear_combination (-a) * hv1 + (-b) * hv2 + h1)
  have g2 : c * v1 + e * v2 = 0 :=
    mul_left_cancel₀ hd0 (by linear_combination (-c) * hv1 + (-e) * hv2 + h3)
  have hδ : v2 * a * y - v2 * b * x - v1 * c * y + v1 * e * x = 0 := by
    linear_combination (v1 * x + v2 * y) * htr - x * g1 - y * g2
  have hMM : !![v1, -y; v2, x] * !![x, y; -v2, v1] = 1 := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact suslinCongKM_mat_eq (by linear_combination hu) (by ring) (by ring)
      (by linear_combination hu)
  have hMM' : !![x, y; -v2, v1] * !![v1, -y; v2, x] = 1 := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact suslinCongKM_mat_eq (by linear_combination hu) (by ring) (by ring)
      (by linear_combination hu)
  have hPS : !![v1, -y; v2, x] * !![0, x * (-a * y + b * x) + y * (-c * y + e * x); 0, 0] =
      !![a, b; c, e] * !![v1, -y; v2, x] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    exact suslinCongKM_mat_eq (by linear_combination -g1)
      (by linear_combination (-a * y + b * x) * hu + y * hδ) (by linear_combination -g2)
      (by linear_combination (-c * y + e * x) * hu - x * hδ)
  refine ⟨⟨!![v1, -y; v2, x], !![x, y; -v2, v1], hMM, hMM'⟩,
    x * (-a * y + b * x) + y * (-c * y + e * x), ?_⟩
  rw [suslinCongKM_single_eq]
  change !![v1, -y; v2, x] * !![0, x * (-a * y + b * x) + y * (-c * y + e * x); 0, 0] *
    !![x, y; -v2, v1] = _
  rw [hPS, mul_assoc, hMM, mul_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongKM_sqZero_conj_entries

/-- **Square-zero matrices are conjugate to `β e₁₂`** over a Euclidean domain. -/
theorem suslinCongKM_sqZero_conj {D : Type*} [EuclideanDomain D]
    (N : Matrix (Fin 2) (Fin 2) D) (hN : N * N = 0) :
    ∃ P : (Matrix (Fin 2) (Fin 2) D)ˣ, ∃ β : D,
      (P : Matrix (Fin 2) (Fin 2) D) * Matrix.single 0 1 β * ↑P⁻¹ = N := by
  have hN' : !![N 0 0, N 0 1; N 1 0, N 1 1] * !![N 0 0, N 0 1; N 1 0, N 1 1] = 0 := by
    rw [← Matrix.eta_fin_two N]
    exact hN
  obtain ⟨P, β, hP⟩ := suslinCongKM_sqZero_conj_entries _ _ _ _ hN'
  exact ⟨P, β, hP.trans (Matrix.eta_fin_two N).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongKM_sqZero_conj

/-- **Unipotents are conjugate to `E₁₂(β)`** over a Euclidean domain. -/
theorem suslinCongKM_unip_conj {D : Type*} [EuclideanDomain D]
    (σ : (Matrix (Fin 2) (Fin 2) D)ˣ) (hσ : σ ∈ suslinCongDecide_unipSet D) :
    ∃ P : (Matrix (Fin 2) (Fin 2) D)ˣ, ∃ β : D,
      P * elementaryUnit (0 : Fin 2) 1 (by decide) β * P⁻¹ = σ := by
  obtain ⟨N, hN, hval⟩ := hσ
  obtain ⟨P, β, hP⟩ := suslinCongKM_sqZero_conj N hN
  refine ⟨P, β, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, hval]
  change (P : Matrix (Fin 2) (Fin 2) D) * (1 + Matrix.single 0 1 β) * ↑P⁻¹ = 1 + N
  rw [mul_add, mul_one, add_mul, Units.mul_inv, hP]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongKM_unip_conj

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

