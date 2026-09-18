import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoeffRing
import GroupApproximation.Meta.AxiomGuard

/-!
# `W₂(L)` has characteristic `p²` and `p = (0, 1)` (bh-met-87e, part 2)

In the commutative ring `eHighWitt_W2 L p` (`PureCharPrimeEHighWittCoeffRing`) we compute the
image of `n : ℕ`:
* the zeroth coordinate is `n` (`eHighWittCoeff_natCast_x0`);
* the first coordinate is `-∑_{m<n} carry m 1` (`eHighWittCoeff_natCast_x1`).

In `ℤ` we have `p · ∑_{m<n} carry m 1 = n^p - n` (`eHighWittCoeff_sum_carry_int`). For `n = p`
this gives `∑_{m<p} carry m 1 = p^(p-1) - 1`, which is `-1` in `L`. Hence `(p : W₂(L)) = (0, 1)`
and `p · w = (0, w₀^p)` (`eHighWittCoeff_p_mul`). Two consequences follow:
* `W₂(L)` has characteristic `p²` (`eHighWittCoeff_charP_W`);
* every `w` with `w₀ ≠ 0` is a unit (`eHighWittCoeff_isUnit`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- `p · ∑_{m<n} carry m 1 = n^p - n` in `ℤ`. -/
theorem eHighWittCoeff_sum_carry_int {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (p : ℤ) * ∑ m ∈ Finset.range n, eHighWitt_carry p (m : ℤ) 1 = (n : ℤ) ^ p - n := by
  induction n with
  | zero => rw [Finset.sum_range_zero, mul_zero, Nat.cast_zero, zero_pow hp.ne_zero, sub_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, eHighWitt_mul_carry hp, one_pow, Nat.cast_add_one]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_sum_carry_int

/-- `∑_{m<p} carry m 1 = p^(p-1) - 1` in `ℤ`. -/
theorem eHighWittCoeff_sum_carry_int_eq {p : ℕ} (hp : p.Prime) :
    ∑ m ∈ Finset.range p, eHighWitt_carry p (m : ℤ) 1 = (p : ℤ) ^ (p - 1) - 1 := by
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine mul_left_cancel₀ hp0 ?_
  rw [eHighWittCoeff_sum_carry_int hp p, mul_sub, mul_one, ← pow_succ',
    Nat.sub_add_cancel hp.one_le]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_sum_carry_int_eq

noncomputable section

variable {L : Type} [Field L] {p : ℕ}

/-- `∑_{m<p} carry m 1 = -1` in a field of characteristic `p`. -/
theorem eHighWittCoeff_sum_carry_L [Fact p.Prime] [CharP L p] :
    ∑ m ∈ Finset.range p, eHighWitt_carry p (m : L) 1 = -1 := by
  have hp : p.Prime := Fact.out
  have h := congrArg (Int.castRingHom L) (eHighWittCoeff_sum_carry_int_eq hp)
  simp only [map_sum, eHighWitt_carry_map, map_natCast, map_one, map_sub, map_pow] at h
  rw [h, CharP.cast_eq_zero L p, zero_pow (Nat.sub_ne_zero_of_lt hp.one_lt), zero_sub]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_sum_carry_L

theorem eHighWittCoeff_natCast_x0 [Fact p.Prime] [CharP L p] (n : ℕ) :
    ((n : eHighWitt_W2 L p)).x0 = n :=
  map_natCast (eHighWittCoeff_x0Hom (L := L) (p := p)) n

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_natCast_x0

theorem eHighWittCoeff_natCast_x1 [Fact p.Prime] [CharP L p] (n : ℕ) :
    ((n : eHighWitt_W2 L p)).x1 = -∑ m ∈ Finset.range n, eHighWitt_carry p (m : L) 1 := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero, neg_zero]
    exact congrArg eHighWitt_W2.x1 (Nat.cast_zero (R := eHighWitt_W2 L p))
  | succ n ih =>
    rw [Nat.cast_add_one]
    show ((n : eHighWitt_W2 L p)).x1 + 0 - eHighWitt_carry p ((n : eHighWitt_W2 L p)).x0 1 = _
    rw [ih, eHighWittCoeff_natCast_x0, Finset.sum_range_succ]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_natCast_x1

/-- `(p : W₂(L)) = (0, 1)`. -/
theorem eHighWittCoeff_natCast_p [Fact p.Prime] [CharP L p] :
    ((p : ℕ) : eHighWitt_W2 L p) = eHighWitt_W2.mk 0 1 := by
  refine eHighWitt_W2.ext ?_ ?_
  · exact (eHighWittCoeff_natCast_x0 p).trans (CharP.cast_eq_zero L p)
  · show _ = (1 : L)
    rw [eHighWittCoeff_natCast_x1, eHighWittCoeff_sum_carry_L, neg_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_natCast_p

/-- `p · w = (0, w₀^p)`. -/
theorem eHighWittCoeff_p_mul [Fact p.Prime] [CharP L p] (w : eHighWitt_W2 L p) :
    (p : eHighWitt_W2 L p) * w = eHighWitt_W2.mk 0 (w.x0 ^ p) := by
  have hp : p.Prime := Fact.out
  rw [eHighWittCoeff_natCast_p]
  refine eHighWitt_W2.ext ?_ ?_
  · show 0 * w.x0 = 0
    ring
  · show 0 ^ p * w.x1 + 1 * w.x0 ^ p = w.x0 ^ p
    rw [zero_pow hp.ne_zero]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_p_mul

/-- `(p² : W₂(L)) = 0`. -/
theorem eHighWittCoeff_natCast_p_sq [Fact p.Prime] [CharP L p] :
    ((p ^ 2 : ℕ) : eHighWitt_W2 L p) = 0 := by
  have hp : p.Prime := Fact.out
  rw [Nat.cast_pow, sq, eHighWittCoeff_p_mul]
  refine eHighWitt_W2.ext rfl ?_
  show ((p : eHighWitt_W2 L p)).x0 ^ p = 0
  rw [eHighWittCoeff_natCast_x0, CharP.cast_eq_zero L p, zero_pow hp.ne_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_natCast_p_sq

/-- **`W₂(L)` has characteristic `p²`.** -/
instance eHighWittCoeff_charP_W [Fact p.Prime] [CharP L p] :
    CharP (eHighWitt_W2 L p) (p ^ 2) := by
  have hp : p.Prime := Fact.out
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have h0 : (x : L) = 0 :=
      (eHighWittCoeff_natCast_x0 x).symm.trans (congrArg eHighWitt_W2.x0 hx)
    obtain ⟨y, rfl⟩ := (CharP.cast_eq_zero_iff L p x).mp h0
    have h1 := congrArg eHighWitt_W2.x1 hx
    rw [Nat.cast_mul, eHighWittCoeff_p_mul] at h1
    have h2 : ((y : eHighWitt_W2 L p)).x0 ^ p = 0 := h1
    rw [eHighWittCoeff_natCast_x0, pow_eq_zero_iff hp.ne_zero, CharP.cast_eq_zero_iff L p] at h2
    rw [sq]
    exact mul_dvd_mul_left p h2
  · obtain ⟨c, rfl⟩ := hx
    rw [Nat.cast_mul, eHighWittCoeff_natCast_p_sq, zero_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_charP_W

/-- **Units.** Every `w` with `w₀ ≠ 0` is a unit of `W₂(L)`. -/
theorem eHighWittCoeff_isUnit [Fact p.Prime] [CharP L p] {w : eHighWitt_W2 L p}
    (hw : w.x0 ≠ 0) : IsUnit w := by
  refine IsUnit.of_mul_eq_one (eHighWitt_W2.mk w.x0⁻¹ (-(w.x1 * w.x0⁻¹ ^ p * w.x0⁻¹ ^ p))) ?_
  have h : w.x0 * w.x0⁻¹ = 1 := mul_inv_cancel₀ hw
  have hq : w.x0 ^ p * w.x0⁻¹ ^ p = 1 := by rw [← mul_pow, h, one_pow]
  refine eHighWitt_W2.ext h ?_
  show w.x0 ^ p * (-(w.x1 * w.x0⁻¹ ^ p * w.x0⁻¹ ^ p)) + w.x1 * w.x0⁻¹ ^ p = 0
  linear_combination (-(w.x1 * w.x0⁻¹ ^ p)) * hq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_isUnit

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
