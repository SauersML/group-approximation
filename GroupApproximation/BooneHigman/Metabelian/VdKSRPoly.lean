import GroupApproximation.BooneHigman.Metabelian.VdKSRStep
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.SetTheory.Cardinal.Order
import GroupApproximation.Meta.AxiomGuard

/-!
# `sr(K[x₁, …, x_k]) ≤ k + 1` for every field `K`

Lane `bh-met-90m`, part 3.

* `vdkSR_exists_collapse_eq_aeval`: for a nonzero `P ∈ K[X₀, …, X_{n-1}]` and any `y ∈ Aⁿ`
  (`A` a `K`-algebra), some collapse of `y`, times a nonzero scalar, equals `P(y)`.  Induction on
  `n` via `finSuccEquiv`: write `P = X₀^N (X₀ Q + P₀)` with `P₀ ≠ 0` (`N` the trailing degree in
  `X₀`), apply the induction hypothesis to `P₀` and the tail of `y`.
* `vdkSR_kdimLE_mvPolynomial`: `n ≥ k + 1` elements of `K[x₁, …, x_k]` are algebraically
  dependent (transcendence degree `k`), so every `n`-tuple has a collapse equal to `0`.
* `vdkSR_stableRangeLE_mvPolynomial`: with `vdkSR_stableRangeLE_of_kdimLE`, `sr ≤ k + 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open MvPolynomial

/-- Evaluation at `y` through `finSuccEquiv`: the first variable goes to `y 0`, the others to the
tail of `y`. -/
theorem vdkSR_aeval_eq_eval₂ {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {n : ℕ}
    (y : Fin (n + 1) → A) (P : MvPolynomial (Fin (n + 1)) K) :
    aeval y P = Polynomial.eval₂ (aeval (Fin.tail y)).toRingHom (y 0) (finSuccEquiv K n P) := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [finSuccEquiv_apply, eval₂Hom_C, RingHom.comp_apply, Polynomial.eval₂_C]
    exact (aeval_C y r).trans (aeval_C (Fin.tail y) r).symm
  | add p q hp hq =>
    rw [map_add, map_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p i h =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, ← h]
    congr 1
    cases i using Fin.cases with
    | zero => rw [aeval_X, finSuccEquiv_X_zero, Polynomial.eval₂_X]
    | succ j =>
      rw [aeval_X, finSuccEquiv_X_succ, Polynomial.eval₂_C]
      exact (aeval_X (Fin.tail y) j).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_aeval_eq_eval₂

/-- A nonzero polynomial relation yields a collapse: `c · collapse(y; a, m) = P(y)`, `c ≠ 0`. -/
theorem vdkSR_exists_collapse_eq_aeval {K A : Type*} [Field K] [CommRing A] [Algebra K A] :
    ∀ (n : ℕ) (P : MvPolynomial (Fin n) K), P ≠ 0 → ∀ y : Fin n → A,
      ∃ (a : Fin n → A) (m : Fin n → ℕ) (c : K), c ≠ 0 ∧
        algebraMap K A c * vdkSR_collapse n y a m = aeval y P
  | 0, P, hP, _ => by
    obtain ⟨c, rfl⟩ : ∃ c : K, P = C c := ⟨_, P.eq_C_of_isEmpty⟩
    refine ⟨fun _ => 0, fun _ => 0, c, fun h => hP (by rw [h, map_zero]), ?_⟩
    rw [vdkSR_collapse_zero, mul_one, aeval_C]
  | n + 1, P, hP, y => by
    obtain ⟨F, hFdef⟩ : ∃ F, F = finSuccEquiv K n P := ⟨_, rfl⟩
    have hF0 : F ≠ 0 := by
      intro h
      apply hP
      apply (finSuccEquiv K n).injective
      rw [← hFdef, h, map_zero]
    obtain ⟨N, hN⟩ : ∃ N, N = F.natTrailingDegree := ⟨_, rfl⟩
    obtain ⟨F', hF'⟩ : Polynomial.X ^ N ∣ F := Polynomial.X_pow_dvd_iff.mpr fun d hd =>
      Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (lt_of_lt_of_eq hd hN)
    have hq : F'.coeff 0 ≠ 0 := by
      have h1 : F.coeff (0 + N) = F'.coeff 0 := by
        rw [hF']
        exact Polynomial.coeff_X_pow_mul F' N 0
      rw [← h1, zero_add, hN]
      exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hF0
    have hF'' : F = Polynomial.X ^ N *
        (Polynomial.X * Polynomial.divX F' + Polynomial.C (F'.coeff 0)) := by
      rw [Polynomial.X_mul_divX_add]
      exact hF'
    have hev : aeval y P = y 0 ^ N *
        (y 0 * Polynomial.eval₂ (aeval (Fin.tail y)).toRingHom (y 0) (Polynomial.divX F') +
          (aeval (Fin.tail y)).toRingHom (F'.coeff 0)) := by
      rw [vdkSR_aeval_eq_eval₂, ← hFdef, hF'', Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
    obtain ⟨a', m', c, hc, hcoll⟩ :=
      vdkSR_exists_collapse_eq_aeval n (F'.coeff 0) hq (Fin.tail y)
    have hcoll' : algebraMap K A c * vdkSR_collapse n (Fin.tail y) a' m' =
        (aeval (Fin.tail y)).toRingHom (F'.coeff 0) := hcoll
    have hcinv : algebraMap K A c * algebraMap K A (c⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    refine ⟨(Fin.cons (algebraMap K A (c⁻¹) *
        Polynomial.eval₂ (aeval (Fin.tail y)).toRingHom (y 0) (Polynomial.divX F')) a' :
          Fin (n + 1) → A), (Fin.cons N m' : Fin (n + 1) → ℕ), c, hc, ?_⟩
    simp only [vdkSR_collapse_succ, Fin.tail_cons, Fin.cons_zero]
    rw [hev]
    linear_combination y 0 ^ N * hcoll' +
      (y 0 ^ N * Polynomial.eval₂ (aeval (Fin.tail y)).toRingHom (y 0) (Polynomial.divX F') *
        y 0) * hcinv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_exists_collapse_eq_aeval

/-- `Kdim K[x₁, …, x_k] < n` (elementary) for every `n ≥ k + 1`. -/
theorem vdkSR_kdimLE_mvPolynomial (K : Type) [Field K] (k n : ℕ) (hn : k + 1 ≤ n) :
    vdkSR_KdimLE (⊥ : Ideal (MvPolynomial (Fin k) K)) n := by
  intro x
  have hdep : ¬ AlgebraicIndependent K x := by
    intro hx
    have h := hx.cardinalMk_le_trdeg
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin, Cardinal.mk_fin] at h
    have h' : n ≤ k := Nat.cast_le.1 h
    omega
  rw [algebraicIndependent_iff] at hdep
  obtain ⟨P, hP⟩ : ∃ P : MvPolynomial (Fin n) K, aeval x P = 0 ∧ P ≠ 0 := by
    by_contra hcon
    exact hdep fun p hp => by
      by_contra hp0
      exact hcon ⟨p, hp, hp0⟩
  obtain ⟨a, m, c, hc, h⟩ := vdkSR_exists_collapse_eq_aeval n P hP.2 x
  rw [hP.1] at h
  have hcinv : algebraMap K (MvPolynomial (Fin k) K) (c⁻¹) *
      algebraMap K (MvPolynomial (Fin k) K) c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  refine ⟨a, m, Ideal.mem_bot.mpr ?_⟩
  linear_combination algebraMap K (MvPolynomial (Fin k) K) (c⁻¹) * h -
    vdkSR_collapse n x a m * hcinv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_kdimLE_mvPolynomial

/-- **`sr(K[x₁, …, x_k]) ≤ k + 1`** for every field `K` and every `k`. -/
theorem vdkSR_stableRangeLE_mvPolynomial (K : Type) [Field K] (k : ℕ) :
    vdkStab_StableRangeLE (MvPolynomial (Fin k) K) (k + 1) :=
  vdkSR_stableRangeLE_of_kdimLE (k + 1) fun n hn => vdkSR_kdimLE_mvPolynomial K k n hn

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_stableRangeLE_mvPolynomial

end GroupApproximation.BooneHigman.Metabelian.ElemFP
