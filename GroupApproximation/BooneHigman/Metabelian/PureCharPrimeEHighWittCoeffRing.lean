import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittLinPoly
import Mathlib.Algebra.CharP.Lemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# The explicit model `W₂(L)` is a commutative ring (bh-met-87e, part 1)

Let `L` be a field of characteristic `p`. We equip the explicit additive model
`eHighWitt_W2 L p` (`PureCharPrimeEHighWittGroup`) with the length-two Witt product
`eHighWittLin_mul a x = (a₀ x₀, a₀^p x₁ + a₁ x₀^p)` (`PureCharPrimeEHighWittLinPoly`) and the
unit `(1, 0)`. This gives a commutative ring `eHighWittCoeff_commRing`.

The laws are checked coordinatewise. Associativity, commutativity and the unit laws are pure
ring identities. Distributivity uses two facts:
* the carry is homogeneous of degree `p` (`eHighWittCoeff_carry_smul`);
* the Frobenius `(b₀ + c₀)^p = b₀^p + c₀^p` holds in characteristic `p`.

We also record that `x₀ : W₂(L) →+* L` is a ring homomorphism (`eHighWittCoeff_x0Hom`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- The carry is homogeneous of degree `p`: `carry (c a) (c b) = c^p · carry a b`. -/
theorem eHighWittCoeff_carry_smul {R : Type*} [CommRing R] (p : ℕ) (c a b : R) :
    eHighWitt_carry p (c * a) (c * b) = c ^ p * eHighWitt_carry p a b := by
  unfold eHighWitt_carry
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hip : i ≤ p := Nat.le_of_lt_add_one (Finset.mem_range.mp hi)
  have hc : c ^ p = c ^ i * c ^ (p - i) := by rw [← pow_add, Nat.add_sub_cancel' hip]
  rw [hc, mul_pow, mul_pow]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_carry_smul

noncomputable section

variable {L : Type} [Field L] {p : ℕ}

/-- The Witt product on the explicit model. -/
instance eHighWittCoeff_instMul : Mul (eHighWitt_W2 L p) := ⟨eHighWittLin_mul⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_instMul

/-- The Witt unit `(1, 0)`. -/
instance eHighWittCoeff_instOne : One (eHighWitt_W2 L p) := ⟨eHighWitt_W2.mk 1 0⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_instOne

theorem eHighWittCoeff_mul_comm (a b : eHighWitt_W2 L p) : a * b = b * a := by
  refine eHighWitt_W2.ext ?_ ?_
  · show a.x0 * b.x0 = b.x0 * a.x0
    ring
  · show a.x0 ^ p * b.x1 + a.x1 * b.x0 ^ p = b.x0 ^ p * a.x1 + b.x1 * a.x0 ^ p
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_mul_comm

theorem eHighWittCoeff_mul_assoc (a b c : eHighWitt_W2 L p) : a * b * c = a * (b * c) := by
  refine eHighWitt_W2.ext ?_ ?_
  · show a.x0 * b.x0 * c.x0 = a.x0 * (b.x0 * c.x0)
    ring
  · show (a.x0 * b.x0) ^ p * c.x1 + (a.x0 ^ p * b.x1 + a.x1 * b.x0 ^ p) * c.x0 ^ p =
      a.x0 ^ p * (b.x0 ^ p * c.x1 + b.x1 * c.x0 ^ p) + a.x1 * (b.x0 * c.x0) ^ p
    rw [mul_pow, mul_pow]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_mul_assoc

theorem eHighWittCoeff_one_mul (a : eHighWitt_W2 L p) : 1 * a = a := by
  refine eHighWitt_W2.ext ?_ ?_
  · show 1 * a.x0 = a.x0
    ring
  · show 1 ^ p * a.x1 + 0 * a.x0 ^ p = a.x1
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_one_mul

theorem eHighWittCoeff_mul_one (a : eHighWitt_W2 L p) : a * 1 = a :=
  (eHighWittCoeff_mul_comm a 1).trans (eHighWittCoeff_one_mul a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_mul_one

theorem eHighWittCoeff_zero_mul (hp : p.Prime) (a : eHighWitt_W2 L p) : 0 * a = 0 := by
  refine eHighWitt_W2.ext ?_ ?_
  · show 0 * a.x0 = 0
    ring
  · show 0 ^ p * a.x1 + 0 * a.x0 ^ p = 0
    rw [zero_pow hp.ne_zero]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_zero_mul

theorem eHighWittCoeff_mul_zero (hp : p.Prime) (a : eHighWitt_W2 L p) : a * 0 = 0 :=
  (eHighWittCoeff_mul_comm a 0).trans (eHighWittCoeff_zero_mul hp a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_mul_zero

theorem eHighWittCoeff_mul_add [Fact p.Prime] [CharP L p] (a b c : eHighWitt_W2 L p) :
    a * (b + c) = a * b + a * c := by
  refine eHighWitt_W2.ext ?_ ?_
  · show a.x0 * (b.x0 + c.x0) = a.x0 * b.x0 + a.x0 * c.x0
    ring
  · show a.x0 ^ p * (b.x1 + c.x1 - eHighWitt_carry p b.x0 c.x0) + a.x1 * (b.x0 + c.x0) ^ p =
      a.x0 ^ p * b.x1 + a.x1 * b.x0 ^ p + (a.x0 ^ p * c.x1 + a.x1 * c.x0 ^ p) -
        eHighWitt_carry p (a.x0 * b.x0) (a.x0 * c.x0)
    rw [eHighWittCoeff_carry_smul, add_pow_char b.x0 c.x0 p]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_mul_add

theorem eHighWittCoeff_add_mul [Fact p.Prime] [CharP L p] (a b c : eHighWitt_W2 L p) :
    (a + b) * c = a * c + b * c := by
  rw [eHighWittCoeff_mul_comm (a + b) c, eHighWittCoeff_mul_add, eHighWittCoeff_mul_comm c a,
    eHighWittCoeff_mul_comm c b]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_add_mul

/-- **The commutative ring `W₂(L)`**, for a field `L` of characteristic `p`. -/
instance eHighWittCoeff_commRing [Fact p.Prime] [CharP L p] : CommRing (eHighWitt_W2 L p) where
  __ := (eHighWitt_W2.instAddCommGroup : AddCommGroup (eHighWitt_W2 L p))
  mul := (· * ·)
  one := 1
  left_distrib := eHighWittCoeff_mul_add
  right_distrib := eHighWittCoeff_add_mul
  zero_mul := eHighWittCoeff_zero_mul Fact.out
  mul_zero := eHighWittCoeff_mul_zero Fact.out
  mul_assoc := eHighWittCoeff_mul_assoc
  one_mul := eHighWittCoeff_one_mul
  mul_one := eHighWittCoeff_mul_one
  mul_comm := eHighWittCoeff_mul_comm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_commRing

/-- The zeroth Witt coordinate `x₀ : W₂(L) →+* L`. -/
def eHighWittCoeff_x0Hom [Fact p.Prime] [CharP L p] : eHighWitt_W2 L p →+* L where
  toFun x := x.x0
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_x0Hom

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
