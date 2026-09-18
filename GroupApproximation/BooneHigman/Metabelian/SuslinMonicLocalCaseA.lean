import GroupApproximation.BooneHigman.Metabelian.SuslinMonicLocalMennicke
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Local monic induction, case A: unit constant term in the second entry

Lane `bh-met-93i`.  Over every nontrivial commutative ring `R`, for first rows `(f, g)` of
`SL₂(R[X])` with `lc f ∈ Rˣ`, `deg f = n + 1`, `deg g < deg f` and `g(0) ∈ Rˣ`:
with `t = -f(0) g(0)⁻¹`, `f' = f + g · t` has `f'(0) = 0`, the same degree and leading
coefficient, so `f' = X · f₂` with `deg f₂ = n`.  Then `(X, g)` is good (`g ≡ g(0)` mod `X` is a
unit there) and `(-f₂, g)` is good by induction, so `(X f₂, g) = (f', g)` is good by the
Mennicke rule, and `(f, g)` follows by a column move (`suslinMonicLocal_caseA`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- `(X, g)` is good when `g(0)` is a unit. -/
theorem suslinMonicLocal_good_X {R : Type*} [CommRing R] (g : R[X])
    (hu : IsUnit (g.coeff 0)) : suslinMonicLocal_Good (X : R[X]) g := by
  obtain ⟨s, hs⟩ := X_dvd_sub_C (p := g)
  exact suslinMonicLocal_colRight (-s)
    (suslinMonicLocal_good_unitRight X (hu.map C)) (by linear_combination -hs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_good_X

/-- **Case A** of the local monic induction step. -/
theorem suslinMonicLocal_caseA {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (hIH : ∀ f g : R[X], IsUnit f.leadingCoeff → f.natDegree ≤ n → suslinMonicLocal_Good f g)
    {f g : R[X]} (hlc : IsUnit f.leadingCoeff) (hd : f.natDegree = n + 1)
    (hg : g.natDegree < f.natDegree) (hu : IsUnit (g.coeff 0)) :
    suslinMonicLocal_Good f g := by
  obtain ⟨w, hw⟩ := hu
  obtain ⟨t, ht⟩ : ∃ t : R, t = -(f.coeff 0 * ((w⁻¹ : Rˣ) : R)) := ⟨_, rfl⟩
  have h0 : (f + g * C t).coeff 0 = 0 := by
    rw [coeff_add, coeff_mul_C, ← hw, ht]
    linear_combination (-(f.coeff 0)) * Units.mul_inv w
  have hlt : (g * C t).natDegree < f.natDegree := lt_of_le_of_lt (natDegree_mul_C_le g t) hg
  have hdeg' : (f + g * C t).natDegree = f.natDegree :=
    natDegree_add_eq_left_of_natDegree_lt hlt
  have hlc' : (f + g * C t).leadingCoeff = f.leadingCoeff :=
    leadingCoeff_add_of_degree_lt' (degree_lt_degree hlt)
  obtain ⟨f₂, hf₂⟩ := X_dvd_iff.mpr h0
  have hf₂0 : f₂ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hf₂
    rw [hf₂, natDegree_zero] at hdeg'
    omega
  have hd₂ : f₂.natDegree = n := by
    have h := hdeg'
    rw [hf₂, natDegree_X_mul hf₂0, hd] at h
    omega
  have hlc₂ : IsUnit f₂.leadingCoeff := by
    rw [← leadingCoeff_monic_mul (q := f₂) monic_X, ← hf₂, hlc']
    exact hlc
  have hG₂ : suslinMonicLocal_Good (-f₂) g :=
    hIH (-f₂) g (by rw [leadingCoeff_neg]; exact hlc₂.neg) (by rw [natDegree_neg]; omega)
  have hGX : suslinMonicLocal_Good (X * f₂) g :=
    suslinMonicLocal_good_mul_left (suslinMonicLocal_good_X g ⟨w, hw⟩) hG₂
  refine suslinMonicLocal_colLeft (f' := f + g * C t) (C t) ?_ rfl
  rw [hf₂]
  exact hGX

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_caseA

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
