import GroupApproximation.Algebra.IntegerGaussValuations
import GroupApproximation.Algebra.BoundedIntegralFinite
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The non-archimedean places over `ℚ(t_1, …, t_d)`

A step toward "every countable subgroup of `GL_2` over a field has the Haagerup property"
(`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`, tex lines 1146--1147),
in characteristic zero.

* `exists_places_minpoly_coeff_le`: for a valuation `w` of a field `L` with a uniformizer and a
  finite separable extension `K / L`, the places `u_1, …, u_r` of `K` over `w`
  (`ValuationExtension.exists_places_over`) satisfy: if `u_j a ≤ exp N` for all `j` and the minimal
  polynomial of `a` over `L` has degree `m`, then its coefficient `c_i` has `w c_i ≤ exp (N (m - i))`.
  The element `π^N a` has `u_j ≤ 1`, and its minimal polynomial is the one of `a` with roots scaled
  by `π^N`.
* `exists_places_minpoly_coeff_le_family`: the same for finitely many valuations at once.
* `exists_places_minpoly_coeff`: let `B = ℤ[t_1, …, t_d]`, `L` its fraction field, `K / L`
  finite and `M > 0`.  The places of `K` over the total-degree place of `L` (when `d > 0`) and over
  the `p`-adic places of `L` for the primes `p ∣ M` are finitely many valuations with
  uniformizers such that, if `M^e a` is integral over `B` and `u_j a ≤ exp N` for all `j`, then
  every coefficient of the minimal polynomial of `M^N a` over `L` is an integer polynomial of total
  degree at most `N n`, where `n = [K : L]`.
-/

namespace GroupApproximation
namespace GHW

open WithZero IntegerGaussValuations

section Places

variable {L : Type*} [Field L]
variable (K : Type*) [Field K] [Algebra L K] [FiniteDimensional L K] [Algebra.IsSeparable L K]

/-- **Coefficient bound at the places over one place.** -/
theorem exists_places_minpoly_coeff_le (w : Valuation L ℤᵐ⁰) {π : L} (hπ : w π = exp (-1 : ℤ)) :
    ∃ (r : ℕ) (u : Fin r → Valuation K ℤᵐ⁰),
      (∀ j, ∃ ϖ : K, u j ϖ = exp (-1 : ℤ)) ∧
      ∀ (N : ℕ) (a : K), (∀ j, u j a ≤ exp (N : ℤ)) →
        ∀ i, w ((minpoly L a).coeff i) ≤ exp ((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ) := by
  obtain ⟨r, u, hunif, hlt, hcoeff⟩ := ValuationExtension.exists_places_over w K hπ
  refine ⟨r, u, hunif, fun N a hbound i ↦ ?_⟩
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hx : ∀ j, u j (algebraMap L K (π ^ N) * a) ≤ 1 := by
    intro j
    have hπj : u j (algebraMap L K π) ^ N ≤ exp (-(N : ℤ)) := by
      have := pow_le_pow_left' (BoundedIntegralFinite.le_exp_neg_one_of_lt_one (hlt j)) N
      rwa [← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one] at this
    calc u j (algebraMap L K (π ^ N) * a) = u j (algebraMap L K π) ^ N * u j a := by
          rw [Valuation.map_mul, map_pow, Valuation.map_pow]
      _ ≤ exp (-(N : ℤ)) * exp (N : ℤ) := mul_le_mul' hπj (hbound j)
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have hscale : minpoly L (algebraMap L K (π ^ N) * a) = (minpoly L a).scaleRoots (π ^ N) := by
    rw [← Algebra.smul_def]
    exact IsIntegrallyClosed.minpoly_smul (pow_ne_zero N hπ0) (Algebra.IsIntegral.isIntegral a)
  have h := hcoeff _ hx i
  rw [hscale, Polynomial.coeff_scaleRoots, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow,
    hπ, ← pow_mul, ← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one] at h
  calc w ((minpoly L a).coeff i)
      = w ((minpoly L a).coeff i) * exp (-((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ)) *
          exp ((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ) := by
        rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    _ ≤ 1 * exp ((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ) := mul_le_mul' h le_rfl
    _ = exp ((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ) := one_mul _

/-- **Coefficient bound at the places over finitely many places.** -/
theorem exists_places_minpoly_coeff_le_family {T : Type*} [Fintype T] (w : T → Valuation L ℤᵐ⁰)
    {π : T → L} (hπ : ∀ t, w t (π t) = exp (-1 : ℤ)) :
    ∃ (r : ℕ) (u : Fin r → Valuation K ℤᵐ⁰),
      (∀ j, ∃ ϖ : K, u j ϖ = exp (-1 : ℤ)) ∧
      ∀ (N : ℕ) (a : K), (∀ j, u j a ≤ exp (N : ℤ)) →
        ∀ t i, w t ((minpoly L a).coeff i) ≤ exp ((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ) := by
  classical
  choose r u hunif hbound using fun t ↦ exists_places_minpoly_coeff_le K (w t) (hπ t)
  let e := Fintype.equivFin (Σ t, Fin (r t))
  refine ⟨Fintype.card (Σ t, Fin (r t)), fun j ↦ u (e.symm j).1 (e.symm j).2,
    fun j ↦ hunif (e.symm j).1 (e.symm j).2, fun N a ha t i ↦ hbound t N a (fun j ↦ ?_) i⟩
  have hj : u (e.symm (e ⟨t, j⟩)).1 (e.symm (e ⟨t, j⟩)).2 a ≤ exp (N : ℤ) := ha (e ⟨t, j⟩)
  rwa [Equiv.symm_apply_apply] at hj

end Places

/-- **The non-archimedean places over `ℚ(t_1, …, t_d)`.**  For `M > 0` and a finite extension
`K` of `L = Frac ℤ[t_1, …, t_d]` there are finitely many valuations of `K` with uniformizers such
that, whenever `M^e a` is integral over `ℤ[t_1, …, t_d]` and `a` has valuation at most `exp N` at
each of them, every coefficient of the minimal polynomial of `M^N a` over `L` is an integer
polynomial of total degree at most `N n`, where `n = [K : L]`. -/
theorem exists_places_minpoly_coeff (d M : ℕ) (hM : 0 < M) (K : Type*) [Field K]
    [Algebra (MvPolynomial (Fin d) ℤ) K] [Algebra (FractionRing (MvPolynomial (Fin d) ℤ)) K]
    [IsScalarTower (MvPolynomial (Fin d) ℤ) (FractionRing (MvPolynomial (Fin d) ℤ)) K]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin d) ℤ)) K] :
    ∃ (r : ℕ) (u : Fin r → Valuation K ℤᵐ⁰),
      (∀ j, ∃ ϖ : K, u j ϖ = exp (-1 : ℤ)) ∧
      ∀ (N e : ℕ) (a : K), IsIntegral (MvPolynomial (Fin d) ℤ) ((M : K) ^ e * a) →
        (∀ j, u j a ≤ exp (N : ℤ)) → ∀ i, ∃ G : MvPolynomial (Fin d) ℤ,
          G.totalDegree ≤ N * Module.finrank (FractionRing (MvPolynomial (Fin d) ℤ)) K ∧
          algebraMap (MvPolynomial (Fin d) ℤ) (FractionRing (MvPolynomial (Fin d) ℤ)) G =
            (minpoly (FractionRing (MvPolynomial (Fin d) ℤ)) ((M : K) ^ N * a)).coeff i := by
  classical
  let B := MvPolynomial (Fin d) ℤ
  let L := FractionRing (MvPolynomial (Fin d) ℤ)
  haveI : Algebra.IsSeparable L K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let w : {p // p ∈ M.primeFactors} ⊕ Fin (min d 1) → Valuation L ℤᵐ⁰ :=
    Sum.elim (fun p ↦ padicValuation d (Nat.prime_of_mem_primeFactors p.2)) (fun _ ↦ degValuation d)
  let π : {p // p ∈ M.primeFactors} ⊕ Fin (min d 1) → L := Sum.elim (fun p ↦ (p.1 : L))
    (fun t ↦ (algebraMap B L (MvPolynomial.X ⟨t.1, lt_of_lt_of_le t.2 (min_le_left d 1)⟩))⁻¹)
  have hπ : ∀ t, w t (π t) = exp (-1 : ℤ) := by
    rintro (p | t)
    · exact padicValuation_natCast_self d (Nat.prime_of_mem_primeFactors p.2)
    · exact degValuation_inv_X d ⟨t.1, lt_of_lt_of_le t.2 (min_le_left d 1)⟩
  obtain ⟨r, u, hunif, hbound⟩ := exists_places_minpoly_coeff_le_family K w hπ
  refine ⟨r, u, hunif, fun N e a ha hua i ↦ ?_⟩
  have hc := hbound N a hua
  have hM0 : ∀ m : ℕ, (M : L) ^ m ≠ 0 := fun m ↦ pow_ne_zero m (Nat.cast_ne_zero.mpr hM.ne')
  have hsmul : ∀ (m : ℕ) (x : K), (M : K) ^ m * x = (M : L) ^ m • x := fun m x ↦ by
    rw [Algebra.smul_def, map_pow, map_natCast]
  have hcoeff : (minpoly L ((M : K) ^ N * a)).coeff i =
      (M : L) ^ (N * ((minpoly L a).natDegree - i)) * (minpoly L a).coeff i := by
    rw [hsmul, IsIntegrallyClosed.minpoly_smul (hM0 N) (Algebra.IsIntegral.isIntegral a),
      Polynomial.coeff_scaleRoots, pow_mul]
    exact mul_comm _ _
  have hxint : IsIntegral B ((M : K) ^ e * ((M : K) ^ N * a)) := by
    have hMN : (M : K) ^ N = algebraMap B K ((M : B) ^ N) := by rw [map_pow, map_natCast]
    rw [mul_left_comm, hMN]
    exact IsIntegral.mul isIntegral_algebraMap ha
  have hmapL : minpoly L ((M : K) ^ e * ((M : K) ^ N * a)) =
      (minpoly B ((M : K) ^ e * ((M : K) ^ N * a))).map (algebraMap B L) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (R := B) (K := L) hxint
  have hb0 : algebraMap B L ((minpoly B ((M : K) ^ e * ((M : K) ^ N * a))).coeff i) =
      (M : L) ^ (e * ((minpoly L ((M : K) ^ N * a)).natDegree - i)) *
        (minpoly L ((M : K) ^ N * a)).coeff i := by
    rw [← Polynomial.coeff_map, ← hmapL, hsmul e, IsIntegrallyClosed.minpoly_smul (hM0 e)
      (Algebra.IsIntegral.isIntegral ((M : K) ^ N * a)), Polynomial.coeff_scaleRoots, pow_mul]
    exact mul_comm _ _
  have hH : ∀ (p : ℕ) (hp : p.Prime), p ∣ M →
      padicValuation d hp ((minpoly L ((M : K) ^ N * a)).coeff i) ≤ 1 := by
    intro p hp hpM
    have hcp : padicValuation d hp ((minpoly L a).coeff i) ≤
        exp ((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ) :=
      hc (Sum.inl ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpM, hM.ne'⟩⟩) i
    have hMp : padicValuation d hp (M : L) ≤ exp (-1 : ℤ) := by
      obtain ⟨m, hm⟩ := hpM
      rw [hm, Nat.cast_mul, Valuation.map_mul, padicValuation_natCast_self d hp]
      calc exp (-1 : ℤ) * padicValuation d hp (m : L) ≤ exp (-1 : ℤ) * 1 :=
            mul_le_mul' le_rfl (valuation_natCast_le_one _ m)
        _ = exp (-1 : ℤ) := mul_one _
    rw [hcoeff, Valuation.map_mul, Valuation.map_pow]
    calc padicValuation d hp (M : L) ^ (N * ((minpoly L a).natDegree - i)) *
          padicValuation d hp ((minpoly L a).coeff i)
        ≤ exp (-1 : ℤ) ^ (N * ((minpoly L a).natDegree - i)) *
            exp ((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ) :=
          mul_le_mul' (pow_le_pow_left' hMp _) hcp
      _ = 1 := by
        rw [← exp_nsmul, ← exp_add, nsmul_eq_mul, mul_neg, mul_one, neg_add_cancel, exp_zero]
  obtain ⟨G, hG⟩ := exists_algebraMap_eq d hM (e * ((minpoly L ((M : K) ^ N * a)).natDegree - i))
    ((minpoly L ((M : K) ^ N * a)).coeff i)
    ((minpoly B ((M : K) ^ e * ((M : K) ^ N * a))).coeff i) hb0 hH
  refine ⟨G, ?_, hG⟩
  by_cases hG0 : G = 0
  · rw [hG0, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos d with hd | hd
  · haveI : IsEmpty (Fin d) := ⟨fun t ↦ by have := t.2; omega⟩
    rw [MvPolynomial.eq_C_of_isEmpty G, MvPolynomial.totalDegree_C]
    exact Nat.zero_le _
  · refine (degValuation_algebraMap_le_iff d hG0 _).mp ?_
    rw [hG, hcoeff, Valuation.map_mul, Valuation.map_pow]
    have hcd : degValuation d ((minpoly L a).coeff i) ≤
        exp ((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ) :=
      hc (Sum.inr ⟨0, lt_min hd Nat.one_pos⟩) i
    calc degValuation d (M : L) ^ (N * ((minpoly L a).natDegree - i)) *
          degValuation d ((minpoly L a).coeff i)
        ≤ 1 ^ (N * ((minpoly L a).natDegree - i)) *
            exp ((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ) :=
          mul_le_mul' (pow_le_pow_left' (valuation_natCast_le_one _ M) _) hcd
      _ = exp ((N * ((minpoly L a).natDegree - i) : ℕ) : ℤ) := by rw [one_pow, one_mul]
      _ ≤ exp ((N * Module.finrank L K : ℕ) : ℤ) :=
          exp_le_exp.mpr (Nat.cast_le.mpr (Nat.mul_le_mul_left N
            ((Nat.sub_le _ _).trans (minpoly.natDegree_le a))))

end GHW
end GroupApproximation

#audit_axioms GroupApproximation.GHW.exists_places_minpoly_coeff_le
#audit_axioms GroupApproximation.GHW.exists_places_minpoly_coeff_le_family
#audit_axioms GroupApproximation.GHW.exists_places_minpoly_coeff
