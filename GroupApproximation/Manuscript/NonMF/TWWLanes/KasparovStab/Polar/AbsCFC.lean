import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Absolute value, lane `nm-tww-17a`: square roots from a positivity test

In any non-unital C⋆-algebra `A`, let `a` be self-adjoint. Suppose
`star b * a * b = -(star c * c)` forces `c = 0`, for all `b` and `c`.
Then `a` has a self-adjoint square root: some self-adjoint `s` satisfies `s * s = a`.

This file is the only place where the order on `A` is used. It is the spectral order,
installed with `letI` inside the proof, so no order instance leaks into the statement. The
operator side (`AbsHolds`) only has to check the test, which is a statement about inner
products.

Proof.
* Write `a = p - n` with `p = a⁺ ≥ 0`, `n = a⁻ ≥ 0` and `p n = 0`.
* `n = q q` with `q` self-adjoint. Then `(q p)⋆ (q p) = p q q p = p n p = 0`, so `q p = 0`
  by the C⋆-identity.
* `q a q = q p q - q n q = -(q n q) = -(n n)`, so the test gives `n = 0`.
* So `a = p = s s` with `s` self-adjoint.
-/

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp

/-- **Square roots from a positivity test.** -/
theorem exists_isSelfAdjoint_mul_self_eq_of_test {A : Type*} [NonUnitalCStarAlgebra A] {a : A}
    (ha : IsSelfAdjoint a) (h : ∀ b c : A, star b * a * b = -(star c * c) → c = 0) :
    ∃ s : A, IsSelfAdjoint s ∧ s * s = a := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  haveI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨p, n, hp, hn, hpn, hdec⟩ : ∃ p n : A, 0 ≤ p ∧ 0 ≤ n ∧ p * n = 0 ∧ a = p - n :=
    ⟨_, _, CFC.posPart_nonneg a, CFC.negPart_nonneg a, CFC.posPart_mul_negPart a,
      (CFC.posPart_sub_negPart a ha).symm⟩
  obtain ⟨q, hqsa, hq⟩ := CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self.mp hn
  have hqp : q * p = 0 := by
    have h0 : star (q * p) * (q * p) = 0 := by
      rw [star_mul, hqsa.star_eq, hp.isSelfAdjoint.star_eq]
      calc p * q * (q * p) = p * (q * q) * p := by simp only [mul_assoc]
        _ = 0 := by rw [← hq, hpn, zero_mul]
    exact (CStarRing.star_mul_self_eq_zero_iff (q * p)).mp h0
  have hkey : star q * a * q = -(star n * n) := by
    rw [hdec, hqsa.star_eq, hn.isSelfAdjoint.star_eq, mul_sub, sub_mul, hqp, zero_mul, zero_sub,
      hq]
    simp only [mul_assoc]
  have hn0 : n = 0 := h q n hkey
  obtain ⟨s, hs, hps⟩ := CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self.mp hp
  exact ⟨s, hs, by rw [hdec, hn0, sub_zero, hps]⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.exists_isSelfAdjoint_mul_self_eq_of_test

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp
