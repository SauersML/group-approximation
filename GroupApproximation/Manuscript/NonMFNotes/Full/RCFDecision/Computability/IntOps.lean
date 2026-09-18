import GroupApproximation.Higman.IntPrimrec
import Mathlib.Computability.Primrec.List

/-!
# Primitive recursive integer arithmetic for the decision procedure

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  The symbolic procedure of
`RCFDecision/Algo.lean` (Basu--Pollack--Roy, *Algorithms in Real Algebraic Geometry*,
Ch. 2 and Ch. 10) only uses integer addition, negation, multiplication, comparison and
powers of `-1`.  Addition, negation and `≤` are in `Higman.IntPrimrec`; this file adds
the magnitude, the product, the strict order and `(-1)^n`.
-/

namespace GroupApproximation.Full.NN11b.PR

/-- Integer magnitudes are primitive recursive (read off the code of an integer). -/
theorem primrec_natAbs : Primrec Int.natAbs := by
  refine Primrec.ofNat_iff.2 ((Primrec.cond
    ((Primrec.eq (α := ℕ)).decide.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0))
    (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
    (Primrec.succ.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))).of_eq fun m => ?_)
  show (bif decide (m % 2 = 0) then m / 2 else Nat.succ (m / 2)) = Int.natAbs (Denumerable.ofNat ℤ m)
  rw [Higman.ofNat_int_eq]
  by_cases h : m % 2 = 0
  · rw [if_pos h, decide_eq_true h, cond_true]
    omega
  · rw [if_neg h, decide_eq_false h, cond_false]
    omega

/-- The product of two integers from the signs and the magnitudes. -/
theorem int_mul_eq (a b : ℤ) :
    a * b = if decide (0 ≤ a) = decide (0 ≤ b) then ((a.natAbs * b.natAbs : ℕ) : ℤ)
      else -((a.natAbs * b.natAbs : ℕ) : ℤ) := by
  rcases Int.lt_or_le a 0 with ha | ha <;> rcases Int.lt_or_le b 0 with hb | hb
  · rw [decide_eq_false (Int.not_le.mpr ha), decide_eq_false (Int.not_le.mpr hb),
      if_pos (rfl : false = false),
      Int.natCast_mul, Int.ofNat_natAbs_of_nonpos (Int.le_of_lt ha),
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hb), Int.neg_mul_neg]
  · rw [decide_eq_false (Int.not_le.mpr ha), decide_eq_true hb,
      if_neg (by decide : ¬(false = true)), Int.natCast_mul,
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt ha), Int.natAbs_of_nonneg hb, Int.neg_mul,
      Int.neg_neg]
  · rw [decide_eq_true ha, decide_eq_false (Int.not_le.mpr hb),
      if_neg (by decide : ¬(true = false)), Int.natCast_mul, Int.natAbs_of_nonneg ha,
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hb), Int.mul_neg, Int.neg_neg]
  · rw [decide_eq_true ha, decide_eq_true hb, if_pos (rfl : true = true), Int.natCast_mul,
      Int.natAbs_of_nonneg ha, Int.natAbs_of_nonneg hb]

/-- Integer multiplication is primitive recursive. -/
theorem primrec_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  have hd1 : Primrec fun p : ℤ × ℤ => decide (0 ≤ p.1) :=
    Higman.primrec2_int_decide_le.comp (Primrec.const 0) Primrec.fst
  have hd2 : Primrec fun p : ℤ × ℤ => decide (0 ≤ p.2) :=
    Higman.primrec2_int_decide_le.comp (Primrec.const 0) Primrec.snd
  have hm : Primrec fun p : ℤ × ℤ => ((p.1.natAbs * p.2.natAbs : ℕ) : ℤ) :=
    Higman.primrec_int_natCast.comp
      (Primrec.nat_mul.comp (primrec_natAbs.comp Primrec.fst) (primrec_natAbs.comp Primrec.snd))
  have hc : PrimrecPred fun p : ℤ × ℤ => decide (0 ≤ p.1) = decide (0 ≤ p.2) :=
    Primrec.eq.comp hd1 hd2
  show Primrec fun p : ℤ × ℤ => p.1 * p.2
  exact (Primrec.ite hc hm (Higman.primrec_int_neg.comp hm)).of_eq fun p =>
    (int_mul_eq p.1 p.2).symm

/-- Composition form of `primrec_int_mul`. -/
theorem primrec_int_mul_comp {α : Type*} [Primcodable α] {f g : α → ℤ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun a => f a * g a :=
  primrec_int_mul.comp hf hg

/-- The strict order on `ℤ` is primitive recursive. -/
theorem primrecRel_int_lt : PrimrecRel ((· < ·) : ℤ → ℤ → Prop) :=
  (Higman.primrec2_int_le.comp Primrec.snd Primrec.fst).not.of_eq fun _ => Int.not_le

/-- The strict order on `ℤ`, as a Boolean function. -/
theorem primrec2_int_decide_lt : Primrec₂ fun x y : ℤ => decide (x < y) :=
  primrecRel_int_lt.decide

/-- Powers of `-1` by iterated negation. -/
theorem neg_one_pow_eq (n : ℕ) : (-1 : ℤ) ^ n = (fun z : ℤ => -z)^[n] 1 := by
  induction n with
  | zero => exact Int.pow_zero _
  | succ n ih =>
    exact (Int.pow_succ (-1 : ℤ) n).trans ((Int.mul_neg_one _).trans
      ((congrArg (fun z : ℤ => -z) ih).trans
        (Function.iterate_succ_apply' (fun z : ℤ => -z) n 1).symm))

/-- `n ↦ (-1)^n` is primitive recursive. -/
theorem primrec_neg_one_pow : Primrec fun n : ℕ => (-1 : ℤ) ^ n :=
  (Primrec.nat_iterate (f := fun n : ℕ => n) (g := fun _ : ℕ => (1 : ℤ))
    (h := fun (_ : ℕ) (z : ℤ) => -z) Primrec.id (Primrec.const 1)
    (Higman.primrec_int_neg.comp (Primrec.snd (α := ℕ) (β := ℤ))).to₂).of_eq fun n =>
      (neg_one_pow_eq n).symm

end GroupApproximation.Full.NN11b.PR
