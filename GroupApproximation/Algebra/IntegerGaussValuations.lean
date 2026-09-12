import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Prime.Int
import GroupApproximation.Meta.AxiomGuard

/-!
# Valuations of `ℚ(t_1, …, t_d)` from integer polynomials

A step toward "every countable subgroup of `GL_2` over a field has the Haagerup property"
(`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`, tex lines 1146--1147),
in characteristic zero.  Let `B = ℤ[t_1, …, t_d]` and let `L` be its fraction field.

* `padicValuation d hp : Valuation L ℤᵐ⁰` extends `G ↦ exp (-m)`, where `m` is the multiplicity of
  the prime `p` in `G`; `p` is a uniformizer (`padicValuation_natCast_self`).
* `degValuation d : Valuation L ℤᵐ⁰` extends `G ↦ exp (totalDegree G)`, with uniformizer
  `(t_i)⁻¹` (`degValuation_inv_X`).
* **Clearing denominators** (`exists_algebraMap_eq`): if `n ^ k H` is a polynomial and `H` has
  valuation at most `1` at every prime dividing `n`, then `H` is a polynomial.
-/

namespace GroupApproximation
namespace IntegerGaussValuations

open WithZero

/-- A valuation into `ℤᵐ⁰` is at most `1` on natural numbers. -/
theorem valuation_natCast_le_one {R : Type*} [Ring R] (v : Valuation R ℤᵐ⁰) (m : ℕ) :
    v (m : R) ≤ 1 := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, Valuation.map_zero]
    exact zero_le
  | succ m ih =>
    rw [Nat.cast_succ]
    exact (v.map_add _ _).trans (max_le ih v.map_one.le)

variable (d : ℕ)

/-! ### The `p`-adic valuation -/

open Classical in
/-- `G ↦ exp (-m)` with `m` the multiplicity of `p` in `G`, and value `0` at `0`. -/
noncomputable def padicFun (p : ℕ) (G : MvPolynomial (Fin d) ℤ) : ℤᵐ⁰ :=
  if G = 0 then 0 else exp (-(multiplicity (p : MvPolynomial (Fin d) ℤ) G : ℤ))

variable {d}

theorem padicFun_zero (p : ℕ) : padicFun d p 0 = 0 := by
  rw [padicFun, if_pos rfl]

theorem padicFun_of_ne_zero (p : ℕ) {G : MvPolynomial (Fin d) ℤ} (hG : G ≠ 0) :
    padicFun d p G = exp (-(multiplicity (p : MvPolynomial (Fin d) ℤ) G : ℤ)) := by
  rw [padicFun, if_neg hG]

/-- A rational prime stays prime in `ℤ[t_1, …, t_d]`. -/
theorem prime_natCast {p : ℕ} (hp : p.Prime) : Prime (p : MvPolynomial (Fin d) ℤ) := by
  rw [← map_natCast (MvPolynomial.C : ℤ →+* MvPolynomial (Fin d) ℤ) p]
  exact (MvPolynomial.prime_C_iff (Fin d)).mpr (Nat.prime_iff_prime_int.mp hp)

theorem padicFun_one {p : ℕ} (hp : p.Prime) : padicFun d p 1 = 1 := by
  rw [padicFun_of_ne_zero p one_ne_zero,
    multiplicity_eq_zero.mpr fun h ↦ (prime_natCast (d := d) hp).not_unit (isUnit_of_dvd_one h),
    Nat.cast_zero, neg_zero, exp_zero]

theorem padicFun_mul {p : ℕ} (hp : p.Prime) (G H : MvPolynomial (Fin d) ℤ) :
    padicFun d p (G * H) = padicFun d p G * padicFun d p H := by
  by_cases hG : G = 0
  · rw [hG, zero_mul, padicFun_zero, zero_mul]
  by_cases hH : H = 0
  · rw [hH, mul_zero, padicFun_zero, mul_zero]
  rw [padicFun_of_ne_zero p (mul_ne_zero hG hH), padicFun_of_ne_zero p hG, padicFun_of_ne_zero p hH,
    multiplicity_mul (prime_natCast (d := d) hp)
      (FiniteMultiplicity.of_prime_left (prime_natCast (d := d) hp) (mul_ne_zero hG hH)),
    Nat.cast_add, neg_add, exp_add]

theorem padicFun_add {p : ℕ} (hp : p.Prime) (G H : MvPolynomial (Fin d) ℤ) :
    padicFun d p (G + H) ≤ max (padicFun d p G) (padicFun d p H) := by
  by_cases hGH : G + H = 0
  · rw [hGH, padicFun_zero]
    exact zero_le
  by_cases hG : G = 0
  · rw [hG, zero_add]
    exact le_max_right _ _
  by_cases hH : H = 0
  · rw [hH, add_zero]
    exact le_max_left _ _
  rw [padicFun_of_ne_zero p hGH, padicFun_of_ne_zero p hG, padicFun_of_ne_zero p hH]
  have hfin := FiniteMultiplicity.of_prime_left (prime_natCast (d := d) hp) hGH
  have key : ∀ m : ℕ, (p : MvPolynomial (Fin d) ℤ) ^ m ∣ G → (p : MvPolynomial (Fin d) ℤ) ^ m ∣ H →
      exp (-(multiplicity (p : MvPolynomial (Fin d) ℤ) (G + H) : ℤ)) ≤ exp (-(m : ℤ)) := by
    intro m hmG hmH
    rw [exp_le_exp, neg_le_neg_iff, Nat.cast_le]
    exact hfin.le_multiplicity_of_pow_dvd (dvd_add hmG hmH)
  rcases le_total (multiplicity (p : MvPolynomial (Fin d) ℤ) G)
      (multiplicity (p : MvPolynomial (Fin d) ℤ) H) with h | h
  · exact le_max_iff.mpr (Or.inl (key _ (pow_multiplicity_dvd _ _)
      ((pow_dvd_pow _ h).trans (pow_multiplicity_dvd _ _))))
  · exact le_max_iff.mpr (Or.inr (key _ ((pow_dvd_pow _ h).trans (pow_multiplicity_dvd _ _))
      (pow_multiplicity_dvd _ _)))

variable (d)

/-- The `p`-adic valuation on integer polynomials. -/
noncomputable def padicValuationPoly {p : ℕ} (hp : p.Prime) :
    Valuation (MvPolynomial (Fin d) ℤ) ℤᵐ⁰ where
  toFun := padicFun d p
  map_zero' := padicFun_zero p
  map_one' := padicFun_one hp
  map_mul' := padicFun_mul hp
  map_add_le_max' := padicFun_add hp

theorem padicValuationPoly_apply {p : ℕ} (hp : p.Prime) (G : MvPolynomial (Fin d) ℤ) :
    padicValuationPoly d hp G = padicFun d p G :=
  rfl

theorem nonZeroDivisors_le_primeCompl_padic {p : ℕ} (hp : p.Prime) :
    nonZeroDivisors (MvPolynomial (Fin d) ℤ) ≤ (padicValuationPoly d hp).supp.primeCompl := by
  intro G hG
  rw [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff, padicValuationPoly_apply,
    padicFun_of_ne_zero p (nonZeroDivisors.ne_zero hG)]
  exact exp_ne_zero

/-- **The `p`-adic valuation** on `ℚ(t_1, …, t_d)`. -/
noncomputable def padicValuation {p : ℕ} (hp : p.Prime) :
    Valuation (FractionRing (MvPolynomial (Fin d) ℤ)) ℤᵐ⁰ :=
  (padicValuationPoly d hp).extendToLocalization (nonZeroDivisors_le_primeCompl_padic d hp)
    (FractionRing (MvPolynomial (Fin d) ℤ))

theorem padicValuation_algebraMap {p : ℕ} (hp : p.Prime) (G : MvPolynomial (Fin d) ℤ) :
    padicValuation d hp (algebraMap _ (FractionRing (MvPolynomial (Fin d) ℤ)) G) =
      padicFun d p G :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ G

theorem natCast_prime_ne_zero {p : ℕ} (hp : p.Prime) : (p : FractionRing (MvPolynomial (Fin d) ℤ)) ≠ 0 := by
  rw [← map_natCast (algebraMap (MvPolynomial (Fin d) ℤ) (FractionRing (MvPolynomial (Fin d) ℤ))) p]
  exact fun h ↦ (prime_natCast (d := d) hp).ne_zero (IsFractionRing.to_map_eq_zero_iff.mp h)

/-- **Uniformizer.**  `p` has `p`-adic valuation `exp (-1)`. -/
theorem padicValuation_natCast_self {p : ℕ} (hp : p.Prime) :
    padicValuation d hp (p : FractionRing (MvPolynomial (Fin d) ℤ)) = exp (-1 : ℤ) := by
  rw [← map_natCast (algebraMap (MvPolynomial (Fin d) ℤ) (FractionRing (MvPolynomial (Fin d) ℤ))) p,
    padicValuation_algebraMap, padicFun_of_ne_zero p (prime_natCast (d := d) hp).ne_zero, multiplicity_self,
    Nat.cast_one]

/-! ### The total-degree valuation -/

open Classical in
/-- `G ↦ exp (totalDegree G)`, with value `0` at `0`. -/
noncomputable def degFun (G : MvPolynomial (Fin d) ℤ) : ℤᵐ⁰ :=
  if G = 0 then 0 else exp (G.totalDegree : ℤ)

variable {d}

theorem degFun_zero : degFun d 0 = 0 := by
  rw [degFun, if_pos rfl]

theorem degFun_of_ne_zero {G : MvPolynomial (Fin d) ℤ} (hG : G ≠ 0) :
    degFun d G = exp (G.totalDegree : ℤ) := by
  rw [degFun, if_neg hG]

theorem degFun_one : degFun d 1 = 1 := by
  rw [degFun_of_ne_zero one_ne_zero, MvPolynomial.totalDegree_one, Nat.cast_zero, exp_zero]

theorem degFun_mul (G H : MvPolynomial (Fin d) ℤ) :
    degFun d (G * H) = degFun d G * degFun d H := by
  by_cases hG : G = 0
  · rw [hG, zero_mul, degFun_zero, zero_mul]
  by_cases hH : H = 0
  · rw [hH, mul_zero, degFun_zero, mul_zero]
  rw [degFun_of_ne_zero (mul_ne_zero hG hH), degFun_of_ne_zero hG, degFun_of_ne_zero hH,
    MvPolynomial.totalDegree_mul_of_isDomain hG hH, Nat.cast_add, exp_add]

theorem degFun_add (G H : MvPolynomial (Fin d) ℤ) :
    degFun d (G + H) ≤ max (degFun d G) (degFun d H) := by
  by_cases hGH : G + H = 0
  · rw [hGH, degFun_zero]
    exact zero_le
  by_cases hG : G = 0
  · rw [hG, zero_add]
    exact le_max_right _ _
  by_cases hH : H = 0
  · rw [hH, add_zero]
    exact le_max_left _ _
  rw [degFun_of_ne_zero hGH, degFun_of_ne_zero hG, degFun_of_ne_zero hH]
  rcases le_max_iff.mp (MvPolynomial.totalDegree_add G H) with h | h
  · exact le_max_iff.mpr (Or.inl (exp_le_exp.mpr (by exact_mod_cast h)))
  · exact le_max_iff.mpr (Or.inr (exp_le_exp.mpr (by exact_mod_cast h)))

variable (d)

/-- The total-degree valuation on integer polynomials. -/
noncomputable def degValuationPoly : Valuation (MvPolynomial (Fin d) ℤ) ℤᵐ⁰ where
  toFun := degFun d
  map_zero' := degFun_zero
  map_one' := degFun_one
  map_mul' := degFun_mul
  map_add_le_max' := degFun_add

theorem degValuationPoly_apply (G : MvPolynomial (Fin d) ℤ) :
    degValuationPoly d G = degFun d G :=
  rfl

theorem nonZeroDivisors_le_primeCompl_deg :
    nonZeroDivisors (MvPolynomial (Fin d) ℤ) ≤ (degValuationPoly d).supp.primeCompl := by
  intro G hG
  rw [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff, degValuationPoly_apply,
    degFun_of_ne_zero (nonZeroDivisors.ne_zero hG)]
  exact exp_ne_zero

/-- **The total-degree valuation** on `ℚ(t_1, …, t_d)`. -/
noncomputable def degValuation : Valuation (FractionRing (MvPolynomial (Fin d) ℤ)) ℤᵐ⁰ :=
  (degValuationPoly d).extendToLocalization (nonZeroDivisors_le_primeCompl_deg d)
    (FractionRing (MvPolynomial (Fin d) ℤ))

theorem degValuation_algebraMap (G : MvPolynomial (Fin d) ℤ) :
    degValuation d (algebraMap _ (FractionRing (MvPolynomial (Fin d) ℤ)) G) = degFun d G :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ G

/-- **Uniformizer.**  `(t_i)⁻¹` has total-degree valuation `exp (-1)`. -/
theorem degValuation_inv_X (i : Fin d) :
    degValuation d (algebraMap (MvPolynomial (Fin d) ℤ) (FractionRing (MvPolynomial (Fin d) ℤ))
      (MvPolynomial.X i))⁻¹ = exp (-1 : ℤ) := by
  rw [map_inv₀, degValuation_algebraMap, degFun_of_ne_zero (MvPolynomial.X_ne_zero i),
    MvPolynomial.totalDegree_X, Nat.cast_one, exp_neg]

/-- **Bounded total-degree valuation is bounded total degree.** -/
theorem degValuation_algebraMap_le_iff {G : MvPolynomial (Fin d) ℤ} (hG : G ≠ 0) (N : ℕ) :
    degValuation d (algebraMap _ (FractionRing (MvPolynomial (Fin d) ℤ)) G) ≤ exp (N : ℤ) ↔
      G.totalDegree ≤ N := by
  rw [degValuation_algebraMap, degFun_of_ne_zero hG, exp_le_exp, Nat.cast_le]

/-! ### Clearing denominators -/

/-- **Clearing denominators.**  If `n ^ k H` is an integer polynomial and `H` has valuation at most
`1` at every prime dividing `n`, then `H` is an integer polynomial. -/
theorem exists_algebraMap_eq {n : ℕ} (hn : 0 < n) (k : ℕ)
    (H : FractionRing (MvPolynomial (Fin d) ℤ)) (G : MvPolynomial (Fin d) ℤ)
    (hG : algebraMap (MvPolynomial (Fin d) ℤ) (FractionRing (MvPolynomial (Fin d) ℤ)) G =
      (n : FractionRing (MvPolynomial (Fin d) ℤ)) ^ k * H)
    (hH : ∀ (p : ℕ) (hp : p.Prime), p ∣ n → padicValuation d hp H ≤ 1) :
    ∃ G' : MvPolynomial (Fin d) ℤ,
      algebraMap (MvPolynomial (Fin d) ℤ) (FractionRing (MvPolynomial (Fin d) ℤ)) G' = H := by
  classical
  let L := FractionRing (MvPolynomial (Fin d) ℤ)
  refine Nat.recOnMul (motive := fun n ↦ 0 < n → ∀ (k : ℕ) (H : L) (G : MvPolynomial (Fin d) ℤ),
      algebraMap (MvPolynomial (Fin d) ℤ) L G = (n : L) ^ k * H →
      (∀ (p : ℕ) (hp : p.Prime), p ∣ n → padicValuation d hp H ≤ 1) →
      ∃ G' : MvPolynomial (Fin d) ℤ, algebraMap (MvPolynomial (Fin d) ℤ) L G' = H)
    ?_ ?_ ?_ ?_ n hn k H G hG hH
  · intro h
    exact absurd h (lt_irrefl 0)
  · intro _ k H G hG _
    exact ⟨G, by rw [hG, Nat.cast_one, one_pow, one_mul]⟩
  · intro p hp _ k H G hG hH
    have hpH := hH p hp dvd_rfl
    have hp0 : (p : L) ^ k ≠ 0 := pow_ne_zero k (natCast_prime_ne_zero d hp)
    by_cases hG0 : G = 0
    · refine ⟨0, ?_⟩
      rw [hG0, map_zero] at hG
      rw [map_zero]
      exact ((mul_eq_zero.mp hG.symm).resolve_left hp0).symm
    have hle : padicFun d p G ≤ exp (-(k : ℤ)) := by
      rw [← padicValuation_algebraMap d hp, hG, Valuation.map_mul, Valuation.map_pow,
        padicValuation_natCast_self d hp]
      calc exp (-1 : ℤ) ^ k * padicValuation d hp H ≤ exp (-1 : ℤ) ^ k * 1 := mul_le_mul' le_rfl hpH
        _ = exp (-(k : ℤ)) := by rw [mul_one, ← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
    rw [padicFun_of_ne_zero p hG0, exp_le_exp, neg_le_neg_iff, Nat.cast_le] at hle
    obtain ⟨G', hG'⟩ := (pow_dvd_pow (p : MvPolynomial (Fin d) ℤ) hle).trans
      (pow_multiplicity_dvd _ G)
    refine ⟨G', ?_⟩
    apply mul_left_cancel₀ hp0
    rw [← hG, hG', map_mul, map_pow, map_natCast]
  · intro a b iha ihb hab k H G hG hH
    have ha : 0 < a := Nat.pos_of_ne_zero fun h ↦ by
      rw [h, zero_mul] at hab
      exact lt_irrefl 0 hab
    have hb : 0 < b := Nat.pos_of_ne_zero fun h ↦ by
      rw [h, mul_zero] at hab
      exact lt_irrefl 0 hab
    obtain ⟨G₁, hG₁⟩ := iha ha k ((b : L) ^ k * H) G
      (by rw [hG, Nat.cast_mul, mul_pow, mul_assoc])
      (fun p hp hpa ↦ by
        rw [Valuation.map_mul, Valuation.map_pow]
        calc padicValuation d hp (b : L) ^ k * padicValuation d hp H ≤ 1 ^ k * 1 :=
              mul_le_mul' (pow_le_pow_left' (valuation_natCast_le_one (padicValuation d hp) b) k)
                (hH p hp (dvd_mul_of_dvd_left hpa b))
          _ = 1 := by rw [one_pow, one_mul])
    exact ihb hb k H G₁ hG₁ (fun p hp hpb ↦ hH p hp (dvd_mul_of_dvd_right hpb a))

end IntegerGaussValuations
end GroupApproximation

#audit_axioms GroupApproximation.IntegerGaussValuations.padicValuation_natCast_self
#audit_axioms GroupApproximation.IntegerGaussValuations.degValuation_inv_X
#audit_axioms GroupApproximation.IntegerGaussValuations.degValuation_algebraMap_le_iff
#audit_axioms GroupApproximation.IntegerGaussValuations.exists_algebraMap_eq
