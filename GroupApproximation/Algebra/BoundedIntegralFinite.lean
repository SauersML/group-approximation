import GroupApproximation.Algebra.TotalDegreeValuation
import GroupApproximation.Algebra.ValuationExtensionPlaces
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Roots
import GroupApproximation.Meta.AxiomGuard

/-!
# Elements integral over `k[t_1, …, t_d]` with bounded valuations at infinity

A step toward "every countable subgroup of `GL_2` over a field has the Haagerup property"
(`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`, tex lines 1146--1147).

Let `k` be a finite field, `B = k[t_1, …, t_d]` with `d ≥ 1`, `L = k(t_1, …, t_d)` and `K / L` a
finite separable extension.  The places of `K` over the total-degree place of `L`
(`ValuationExtension.exists_places_over`) are finitely many valuations `u_1, …, u_r` with
uniformizers, and (`finite_bounded_integral`) for every `N` the elements of `K` integral over `B`
with `u_j a ≤ exp N` for all `j` form a finite set.

For such `a` with `n = [K : L]` and `π = t_1^{-1}`, the element `π^N a` has `u_j ≤ 1` at every
place, so the minimal polynomial of `π^N a` has integral coefficients at the total-degree place.
That polynomial is the minimal polynomial of `a` with roots scaled by `π^N`, so the coefficients of
the minimal polynomial of `a` over `B` have total degree at most `N n`.  Only finitely many monic
polynomials of degree at most `n` have such coefficients, and each has finitely many roots.
-/

namespace GroupApproximation
namespace BoundedIntegralFinite

open WithZero TotalDegreeValuation

/-- A value below `1` is at most `exp (-1)`. -/
theorem le_exp_neg_one_of_lt_one {y : ℤᵐ⁰} (hy : y < 1) : y ≤ exp (-1 : ℤ) := by
  by_cases hy0 : y = 0
  · rw [hy0]
    exact WithZero.zero_le _
  have hlog : log y < 0 := (log_lt_iff_lt_exp hy0).mpr (by rw [exp_zero]; exact hy)
  exact le_exp_of_log_le (by omega)

variable {k : Type*} [Field k] [Finite k] {d : ℕ}

/-- **Bounded integral elements are finitely many.** -/
theorem finite_bounded_integral (hd : 0 < d) (K : Type*) [Field K]
    [Algebra (MvPolynomial (Fin d) k) K] [Algebra (FractionRing (MvPolynomial (Fin d) k)) K]
    [IsScalarTower (MvPolynomial (Fin d) k) (FractionRing (MvPolynomial (Fin d) k)) K]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin d) k)) K]
    [Algebra.IsSeparable (FractionRing (MvPolynomial (Fin d) k)) K] :
    ∃ (r : ℕ) (u : Fin r → Valuation K ℤᵐ⁰),
      (∀ j, ∃ ϖ : K, u j ϖ = exp (-1 : ℤ)) ∧
      ∀ N : ℕ, {a : K | IsIntegral (MvPolynomial (Fin d) k) a ∧ ∀ j, u j a ≤ exp (N : ℤ)}.Finite := by
  classical
  let B := MvPolynomial (Fin d) k
  let L := FractionRing (MvPolynomial (Fin d) k)
  let w := degValuation k d
  let π : L := (algebraMap B L (MvPolynomial.X ⟨0, hd⟩))⁻¹
  have hπ : w π = exp (-1 : ℤ) := by
    show degValuation k d (algebraMap B L (MvPolynomial.X ⟨0, hd⟩))⁻¹ = _
    rw [map_inv₀, degValuation_algebraMap, degFun_of_ne_zero (MvPolynomial.X_ne_zero _),
      MvPolynomial.totalDegree_X, Nat.cast_one, exp_neg]
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hπ
    exact exp_ne_zero hπ.symm
  obtain ⟨r, u, hunif, hlt, hcoeff⟩ := ValuationExtension.exists_places_over w K hπ
  refine ⟨r, u, hunif, fun N ↦ ?_⟩
  let n := Module.finrank L K
  let T : Set B := {b | b.totalDegree ≤ N * n}
  have hT : T.Finite := finite_setOf_totalDegree_le k d (N * n)
  let P : Set (Polynomial B) := {q | q.Monic ∧ q.natDegree ≤ n ∧ ∀ i, q.coeff i ∈ T}
  have hP : P.Finite := by
    haveI : Finite T := hT.to_subtype
    refine Set.finite_coe_iff.mp (Finite.of_injective
      (fun q : P ↦ fun i : Fin (n + 1) ↦ (⟨q.1.coeff i, q.2.2.2 i⟩ : T)) ?_)
    intro q q' h
    apply Subtype.ext
    refine Polynomial.ext fun i ↦ ?_
    by_cases hi : i ≤ n
    · exact congrArg (fun f : Fin (n + 1) → T ↦ ((f ⟨i, Nat.lt_succ_of_le hi⟩ : T) : B)) h
    · have h1 := q.2.2.1
      have h2 := q'.2.2.1
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.1.natDegree < i),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q'.1.natDegree < i)]
  have hsub : {a : K | IsIntegral B a ∧ ∀ j, u j a ≤ exp (N : ℤ)} ⊆
      ⋃ q ∈ P, {x : K | (q.map (algebraMap B K)).IsRoot x} := by
    rintro a ⟨ha, hbound⟩
    have hmapL : minpoly L a = (minpoly B a).map (algebraMap B L) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' (R := B) (K := L) ha
    have hdegB : (minpoly B a).natDegree = (minpoly L a).natDegree := by
      rw [hmapL, (minpoly.monic ha).natDegree_map]
    have hdegL : (minpoly L a).natDegree ≤ n := minpoly.natDegree_le a
    refine Set.mem_biUnion (x := minpoly B a) ⟨minpoly.monic ha, by rw [hdegB]; exact hdegL, fun i ↦ ?_⟩ ?_
    · show ((minpoly B a).coeff i).totalDegree ≤ N * n
      let b := (minpoly B a).coeff i
      by_cases hb : b = 0
      · show b.totalDegree ≤ N * n
        rw [hb, MvPolynomial.totalDegree_zero]
        exact Nat.zero_le _
      -- the scaled element `π^N a`
      have hc0 : π ^ N ≠ 0 := pow_ne_zero N hπ0
      have hx : ∀ j, u j (algebraMap L K (π ^ N) * a) ≤ 1 := by
        intro j
        have hπj : u j (algebraMap L K π) ^ N ≤ exp (-(N : ℤ)) := by
          have := pow_le_pow_left' (le_exp_neg_one_of_lt_one (hlt j)) N
          rwa [← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one] at this
        calc u j (algebraMap L K (π ^ N) * a) = u j (algebraMap L K π) ^ N * u j a := by
              rw [Valuation.map_mul, map_pow, Valuation.map_pow]
          _ ≤ exp (-(N : ℤ)) * exp (N : ℤ) := mul_le_mul' hπj (hbound j)
          _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
      have hint : IsIntegral L a := Algebra.IsIntegral.isIntegral a
      have hscale : minpoly L (algebraMap L K (π ^ N) * a) = (minpoly L a).scaleRoots (π ^ N) := by
        rw [← Algebra.smul_def]
        exact IsIntegrallyClosed.minpoly_smul hc0 hint
      have h := hcoeff _ hx i
      rw [hscale, Polynomial.coeff_scaleRoots, hmapL, Polynomial.coeff_map, Valuation.map_mul,
        Valuation.map_pow, Valuation.map_pow] at h
      have hwb : w (algebraMap B L b) = exp (b.totalDegree : ℤ) := by
        rw [degValuation_algebraMap, degFun_of_ne_zero hb]
      rw [(minpoly.monic ha).natDegree_map] at h
      change w (algebraMap B L b) * (w π ^ N) ^ ((minpoly B a).natDegree - i) ≤ 1 at h
      rw [hwb, hπ, ← pow_mul, ← exp_nsmul, ← exp_add, ← exp_zero (M := ℤ), exp_le_exp, nsmul_eq_mul,
        mul_neg, mul_one] at h
      have hle : (b.totalDegree : ℤ) ≤ ((N * ((minpoly B a).natDegree - i) : ℕ) : ℤ) := by
        linarith
      have hle' : b.totalDegree ≤ N * ((minpoly B a).natDegree - i) := by exact_mod_cast hle
      exact hle'.trans (Nat.mul_le_mul_left N ((Nat.sub_le _ _).trans (by rw [hdegB]; exact hdegL)))
    · show Polynomial.eval a ((minpoly B a).map (algebraMap B K)) = 0
      rw [Polynomial.eval_map, ← Polynomial.aeval_def]
      exact minpoly.aeval B a
  refine (hP.biUnion fun q hq ↦ ?_).subset hsub
  exact Polynomial.finite_setOf_isRoot (hq.1.map (algebraMap B K)).ne_zero

end BoundedIntegralFinite
end GroupApproximation

#audit_axioms GroupApproximation.BoundedIntegralFinite.finite_bounded_integral
