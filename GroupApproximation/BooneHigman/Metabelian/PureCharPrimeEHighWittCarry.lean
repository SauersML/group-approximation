import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# The Witt carry polynomial of length two (bh-met-87c, part 1)

For a prime `p` and any commutative ring `R`,
`eHighWitt_carry p a b = ∑_{i ≤ p} ⌊C(p,i) / p⌋ · a^i · b^(p-i)`.
The two end terms carry the coefficient `⌊1 / p⌋ = 0`, so this is
`((a + b)^p - a^p - b^p) / p`, written with integer coefficients.  It is the carry of the
second Witt coordinate: `W₂` addition is `(x₀, x₁) + (y₀, y₁) = (x₀ + y₀, x₁ + y₁ - carry)`.

The cocycle identities are needed for the group laws.  We prove them without any Witt-vector
library, as follows:

* `eHighWitt_mul_carry`: in every commutative ring, `p · carry = (a + b)^p - a^p - b^p`;
* the identities hold in `ℤ[X₀, X₁, X₂]`, which is torsion-free of characteristic zero.  There we
  cancel the factor `p` using `mul_left_cancel₀`;
* they are pushed to an arbitrary `R` along `eval₂Hom (Int.castRingHom R)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- The second-coordinate carry `((a + b)^p - a^p - b^p) / p`, with integer coefficients. -/
def eHighWitt_carry {R : Type*} [CommRing R] (p : ℕ) (a b : R) : R :=
  ∑ i ∈ Finset.range (p + 1), ((p.choose i / p : ℕ) : R) * a ^ i * b ^ (p - i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_carry

/-- The carry commutes with ring homomorphisms. -/
theorem eHighWitt_carry_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : ℕ)
    (a b : R) : φ (eHighWitt_carry p a b) = eHighWitt_carry p (φ a) (φ b) := by
  simp only [eHighWitt_carry, map_sum, map_mul, map_pow, map_natCast]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_carry_map

/-- `p · carry = (a + b)^p - a^p - b^p` in every commutative ring. -/
theorem eHighWitt_mul_carry {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (a b : R) :
    (p : R) * eHighWitt_carry p a b = (a + b) ^ p - a ^ p - b ^ p := by
  have hterm : ∀ i ∈ Finset.range (p + 1),
      a ^ i * b ^ (p - i) * (p.choose i : R) =
        (p : R) * (((p.choose i / p : ℕ) : R) * a ^ i * b ^ (p - i)) +
          ((p.choose i % p : ℕ) : R) * a ^ i * b ^ (p - i) := by
    intro i _
    have h : (p.choose i : R) =
        (p : R) * ((p.choose i / p : ℕ) : R) + ((p.choose i % p : ℕ) : R) := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Nat.div_add_mod]
    rw [h]
    ring
  have hsum : ∑ i ∈ Finset.range (p + 1), ((p.choose i % p : ℕ) : R) * a ^ i * b ^ (p - i) =
      b ^ p + a ^ p := by
    rw [Finset.sum_eq_add_of_mem 0 p (Finset.mem_range.mpr (Nat.add_one_pos p))
      (Finset.mem_range.mpr (Nat.lt_add_one p)) hp.ne_zero.symm]
    · simp only [Nat.choose_zero_right, Nat.choose_self, Nat.mod_eq_of_lt hp.one_lt,
        Nat.sub_zero, Nat.sub_self, pow_zero, Nat.cast_one, one_mul, mul_one]
    · intro c hc hc'
      have hcp : c < p := by
        have h1 := Finset.mem_range.mp hc
        have h2 := hc'.2
        omega
      simp only [Nat.mod_eq_zero_of_dvd (hp.dvd_choose_self hc'.1 hcp), Nat.cast_zero, zero_mul]
  have key : (a + b) ^ p = (p : R) * eHighWitt_carry p a b + (a ^ p + b ^ p) := by
    rw [eHighWitt_carry, add_pow, Finset.mul_sum, add_comm (a ^ p), ← hsum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  linear_combination (-1 : R) * key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_mul_carry

/-- Universal commutativity of the carry, in `ℤ[X₀, X₁, X₂]`. -/
theorem eHighWitt_carry_comm_univ {p : ℕ} (hp : p.Prime) :
    eHighWitt_carry p (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 1) =
      eHighWitt_carry p (MvPolynomial.X 1) (MvPolynomial.X 0) := by
  have hp0 : ((p : ℕ) : MvPolynomial (Fin 3) ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine mul_left_cancel₀ hp0 ?_
  rw [eHighWitt_mul_carry hp, eHighWitt_mul_carry hp,
    add_comm (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 0)]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_carry_comm_univ

/-- Universal vanishing `carry X₀ 0 = 0`. -/
theorem eHighWitt_carry_zero_right_univ {p : ℕ} (hp : p.Prime) :
    eHighWitt_carry p (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) 0 = 0 := by
  have hp0 : ((p : ℕ) : MvPolynomial (Fin 3) ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine mul_left_cancel₀ hp0 ?_
  rw [eHighWitt_mul_carry hp, add_zero, zero_pow hp.ne_zero]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_carry_zero_right_univ

/-- Universal vanishing `carry 0 X₀ = 0`. -/
theorem eHighWitt_carry_zero_left_univ {p : ℕ} (hp : p.Prime) :
    eHighWitt_carry p (0 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 0) = 0 := by
  have hp0 : ((p : ℕ) : MvPolynomial (Fin 3) ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine mul_left_cancel₀ hp0 ?_
  rw [eHighWitt_mul_carry hp, zero_add, zero_pow hp.ne_zero]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_carry_zero_left_univ

/-- The universal cocycle identity in `ℤ[X₀, X₁, X₂]`. -/
theorem eHighWitt_carry_assoc_univ {p : ℕ} (hp : p.Prime) :
    eHighWitt_carry p (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 1) +
        eHighWitt_carry p (MvPolynomial.X 0 + MvPolynomial.X 1) (MvPolynomial.X 2) =
      eHighWitt_carry p (MvPolynomial.X 1) (MvPolynomial.X 2) +
        eHighWitt_carry p (MvPolynomial.X 0) (MvPolynomial.X 1 + MvPolynomial.X 2) := by
  have hp0 : ((p : ℕ) : MvPolynomial (Fin 3) ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine mul_left_cancel₀ hp0 ?_
  rw [mul_add, mul_add, eHighWitt_mul_carry hp, eHighWitt_mul_carry hp, eHighWitt_mul_carry hp,
    eHighWitt_mul_carry hp, ← add_assoc (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ)
      (MvPolynomial.X 1) (MvPolynomial.X 2)]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_carry_assoc_univ

end GroupApproximation.BooneHigman.Metabelian.Coprimary
