import Mathlib.Computability.Primrec.List
import Mathlib.Data.Rat.Lemmas
import GroupApproximation.Analysis.RationalHermitian

/-!
# Executable Gaussian-rational codes

The arithmetical MF checker cannot use `ℚ` as certificate data: at the pinned
Mathlib revision `ℚ` is encodable but not `Primcodable`.  We therefore use an
unnormalized, denominator-positive code made only from natural numbers.

`((p,n),d)` denotes `(p-n)/(d+1)`.  Addition, negation and multiplication are
defined without normalization.  Consequently every operation is primitive
recursive, equality and strict order reduce to natural-number comparisons,
and every rational number is represented.  A Gaussian rational is a pair of
these codes.
-/

namespace GroupApproximation
namespace RationalComplexCode

/-- An unnormalized rational code: `((positive, negative), denominator-1)`. -/
abbrev RatCode := (ℕ × ℕ) × ℕ

/-- A Gaussian-rational code. -/
abbrev ComplexCode := RatCode × RatCode

def ratZero : RatCode := ((0, 0), 0)
def ratOne : RatCode := ((1, 0), 0)

def numeratorPos (q : RatCode) : ℕ := q.1.1
def numeratorNeg (q : RatCode) : ℕ := q.1.2
def denominator (q : RatCode) : ℕ := q.2 + 1

/-- Semantic value of a rational code. -/
def toRat (q : RatCode) : ℚ :=
  ((numeratorPos q : ℚ) - numeratorNeg q) / denominator q

def ratNeg (q : RatCode) : RatCode := ((numeratorNeg q, numeratorPos q), q.2)

def ratAdd (q r : RatCode) : RatCode :=
  (((numeratorPos q * denominator r + numeratorPos r * denominator q),
      (numeratorNeg q * denominator r + numeratorNeg r * denominator q)),
    denominator q * denominator r - 1)

def ratMul (q r : RatCode) : RatCode :=
  (((numeratorPos q * numeratorPos r + numeratorNeg q * numeratorNeg r),
      (numeratorPos q * numeratorNeg r + numeratorNeg q * numeratorPos r)),
    denominator q * denominator r - 1)

/-- Cross-multiplied equality, using naturals only. -/
def RatEq (q r : RatCode) : Prop :=
  numeratorPos q * denominator r + numeratorNeg r * denominator q =
    numeratorNeg q * denominator r + numeratorPos r * denominator q

/-- Cross-multiplied strict order, using naturals only. -/
def RatLt (q r : RatCode) : Prop :=
  numeratorPos q * denominator r + numeratorNeg r * denominator q <
    numeratorNeg q * denominator r + numeratorPos r * denominator q

instance ratEqDecidable : DecidableRel RatEq := fun _ _ => by
  unfold RatEq
  infer_instance

instance ratLtDecidable : DecidableRel RatLt := fun _ _ => by
  unfold RatLt
  infer_instance

@[simp] theorem denominator_pos (q : RatCode) : 0 < denominator q := by
  simp [denominator]

@[simp] theorem denominator_ne_zero (q : RatCode) : denominator q ≠ 0 :=
  Nat.ne_of_gt (denominator_pos q)

theorem denominator_mul_sub_one (q r : RatCode) :
    denominator q * denominator r - 1 + 1 = denominator q * denominator r := by
  exact Nat.sub_add_cancel
    (Nat.succ_le_iff.2 (Nat.mul_pos (denominator_pos q) (denominator_pos r)))

@[simp] theorem toRat_zero : toRat ratZero = 0 := by
  norm_num [toRat, ratZero, numeratorPos, numeratorNeg, denominator]

@[simp] theorem toRat_one : toRat ratOne = 1 := by
  norm_num [toRat, ratOne, numeratorPos, numeratorNeg, denominator]

@[simp] theorem toRat_neg (q : RatCode) : toRat (ratNeg q) = -toRat q := by
  simp only [toRat, ratNeg, numeratorPos, numeratorNeg, denominator]
  ring

@[simp] theorem toRat_add (q r : RatCode) : toRat (ratAdd q r) = toRat q + toRat r := by
  have hq : (denominator q : ℚ) ≠ 0 := by exact_mod_cast denominator_ne_zero q
  have hr : (denominator r : ℚ) ≠ 0 := by exact_mod_cast denominator_ne_zero r
  simp only [toRat, ratAdd, numeratorPos, numeratorNeg, denominator]
  rw [Nat.sub_add_cancel (by
    exact Nat.succ_le_of_lt (Nat.mul_pos (denominator_pos q) (denominator_pos r)))]
  push_cast
  field_simp
  ring

@[simp] theorem toRat_mul (q r : RatCode) : toRat (ratMul q r) = toRat q * toRat r := by
  have hq : (denominator q : ℚ) ≠ 0 := by exact_mod_cast denominator_ne_zero q
  have hr : (denominator r : ℚ) ≠ 0 := by exact_mod_cast denominator_ne_zero r
  simp only [toRat, ratMul, numeratorPos, numeratorNeg, denominator]
  rw [Nat.sub_add_cancel (by
    exact Nat.succ_le_of_lt (Nat.mul_pos (denominator_pos q) (denominator_pos r)))]
  push_cast
  field_simp
  ring

theorem ratEq_iff (q r : RatCode) : RatEq q r ↔ toRat q = toRat r := by
  have hq : (denominator q : ℚ) ≠ 0 := by exact_mod_cast denominator_ne_zero q
  have hr : (denominator r : ℚ) ≠ 0 := by exact_mod_cast denominator_ne_zero r
  simp only [RatEq, toRat]
  constructor
  · intro h
    apply (div_eq_div_iff hq hr).2
    have hc :
        (numeratorPos q : ℚ) * denominator r + numeratorNeg r * denominator q =
          numeratorNeg q * denominator r + numeratorPos r * denominator q := by
      exact_mod_cast h
    linarith
  · intro h
    have h' := (div_eq_div_iff hq hr).1 h
    have hc :
        (numeratorPos q : ℚ) * denominator r + numeratorNeg r * denominator q =
          numeratorNeg q * denominator r + numeratorPos r * denominator q := by
      linarith
    exact_mod_cast hc

theorem ratLt_iff (q r : RatCode) : RatLt q r ↔ toRat q < toRat r := by
  have hq : (0 : ℚ) < denominator q := by exact_mod_cast denominator_pos q
  have hr : (0 : ℚ) < denominator r := by exact_mod_cast denominator_pos r
  simp only [RatLt, toRat]
  rw [div_lt_div_iff₀ hq hr]
  constructor
  · intro h
    have hc :
        (numeratorPos q : ℚ) * denominator r + numeratorNeg r * denominator q <
          numeratorNeg q * denominator r + numeratorPos r * denominator q := by
      exact_mod_cast h
    linarith
  · intro h
    have hc :
        (numeratorPos q : ℚ) * denominator r + numeratorNeg r * denominator q <
          numeratorNeg q * denominator r + numeratorPos r * denominator q := by
      linarith
    exact_mod_cast hc

/-! ## Primitive recursiveness -/

theorem primrec_numeratorPos : Primrec numeratorPos :=
  Primrec.fst.comp Primrec.fst

theorem primrec_numeratorNeg : Primrec numeratorNeg :=
  Primrec.snd.comp Primrec.fst

theorem primrec_denominator : Primrec denominator :=
  Primrec.succ.comp Primrec.snd

theorem primrec_ratNeg : Primrec ratNeg := by
  exact Primrec.pair (Primrec.pair primrec_numeratorNeg primrec_numeratorPos) Primrec.snd

theorem primrec_ratAdd : Primrec₂ ratAdd := by
  apply Primrec₂.mk
  let qpos : Primrec fun z : RatCode × RatCode => numeratorPos z.1 :=
    primrec_numeratorPos.comp Primrec.fst
  let qneg : Primrec fun z : RatCode × RatCode => numeratorNeg z.1 :=
    primrec_numeratorNeg.comp Primrec.fst
  let qden : Primrec fun z : RatCode × RatCode => denominator z.1 :=
    primrec_denominator.comp Primrec.fst
  let rpos : Primrec fun z : RatCode × RatCode => numeratorPos z.2 :=
    primrec_numeratorPos.comp Primrec.snd
  let rneg : Primrec fun z : RatCode × RatCode => numeratorNeg z.2 :=
    primrec_numeratorNeg.comp Primrec.snd
  let rden : Primrec fun z : RatCode × RatCode => denominator z.2 :=
    primrec_denominator.comp Primrec.snd
  exact Primrec.pair
    (Primrec.pair
      (Primrec.nat_add.comp (Primrec.nat_mul.comp qpos rden)
        (Primrec.nat_mul.comp rpos qden))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp qneg rden)
        (Primrec.nat_mul.comp rneg qden)))
    (Primrec.pred.comp (Primrec.nat_mul.comp qden rden))

theorem primrec_ratMul : Primrec₂ ratMul := by
  apply Primrec₂.mk
  let qpos : Primrec fun z : RatCode × RatCode => numeratorPos z.1 :=
    primrec_numeratorPos.comp Primrec.fst
  let qneg : Primrec fun z : RatCode × RatCode => numeratorNeg z.1 :=
    primrec_numeratorNeg.comp Primrec.fst
  let qden : Primrec fun z : RatCode × RatCode => denominator z.1 :=
    primrec_denominator.comp Primrec.fst
  let rpos : Primrec fun z : RatCode × RatCode => numeratorPos z.2 :=
    primrec_numeratorPos.comp Primrec.snd
  let rneg : Primrec fun z : RatCode × RatCode => numeratorNeg z.2 :=
    primrec_numeratorNeg.comp Primrec.snd
  let rden : Primrec fun z : RatCode × RatCode => denominator z.2 :=
    primrec_denominator.comp Primrec.snd
  exact Primrec.pair
    (Primrec.pair
      (Primrec.nat_add.comp (Primrec.nat_mul.comp qpos rpos)
        (Primrec.nat_mul.comp qneg rneg))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp qpos rneg)
        (Primrec.nat_mul.comp qneg rpos)))
    (Primrec.pred.comp (Primrec.nat_mul.comp qden rden))

theorem primrecRel_ratEq : PrimrecRel RatEq := by
  apply PrimrecRel.comp₂ Primrec.eq
  · exact Primrec.nat_add.comp₂
      (Primrec.nat_mul.comp₂ (primrec_numeratorPos.comp₂ Primrec₂.left)
        (primrec_denominator.comp₂ Primrec₂.right))
      (Primrec.nat_mul.comp₂ (primrec_numeratorNeg.comp₂ Primrec₂.right)
        (primrec_denominator.comp₂ Primrec₂.left))
  · exact Primrec.nat_add.comp₂
      (Primrec.nat_mul.comp₂ (primrec_numeratorNeg.comp₂ Primrec₂.left)
        (primrec_denominator.comp₂ Primrec₂.right))
      (Primrec.nat_mul.comp₂ (primrec_numeratorPos.comp₂ Primrec₂.right)
        (primrec_denominator.comp₂ Primrec₂.left))

theorem primrecRel_ratLt : PrimrecRel RatLt := by
  apply PrimrecRel.comp₂ Primrec.nat_lt
  · exact Primrec.nat_add.comp₂
      (Primrec.nat_mul.comp₂ (primrec_numeratorPos.comp₂ Primrec₂.left)
        (primrec_denominator.comp₂ Primrec₂.right))
      (Primrec.nat_mul.comp₂ (primrec_numeratorNeg.comp₂ Primrec₂.right)
        (primrec_denominator.comp₂ Primrec₂.left))
  · exact Primrec.nat_add.comp₂
      (Primrec.nat_mul.comp₂ (primrec_numeratorNeg.comp₂ Primrec₂.left)
        (primrec_denominator.comp₂ Primrec₂.right))
      (Primrec.nat_mul.comp₂ (primrec_numeratorPos.comp₂ Primrec₂.right)
        (primrec_denominator.comp₂ Primrec₂.left))

/-! ## Gaussian rational operations -/

def complexZero : ComplexCode := (ratZero, ratZero)
def complexOne : ComplexCode := (ratOne, ratZero)
def complexI : ComplexCode := (ratZero, ratOne)

def complexAdd (z w : ComplexCode) : ComplexCode :=
  (ratAdd z.1 w.1, ratAdd z.2 w.2)

def complexNeg (z : ComplexCode) : ComplexCode := (ratNeg z.1, ratNeg z.2)

def complexMul (z w : ComplexCode) : ComplexCode :=
  (ratAdd (ratMul z.1 w.1) (ratNeg (ratMul z.2 w.2)),
    ratAdd (ratMul z.1 w.2) (ratMul z.2 w.1))

def complexConj (z : ComplexCode) : ComplexCode := (z.1, ratNeg z.2)

def toComplex (z : ComplexCode) : ℂ :=
  (toRat z.1 : ℂ) + (toRat z.2 : ℂ) * Complex.I

@[simp] theorem toComplex_zero : toComplex complexZero = 0 := by
  simp [toComplex, complexZero]

@[simp] theorem toComplex_one : toComplex complexOne = 1 := by
  simp [toComplex, complexOne]

@[simp] theorem toComplex_add (z w : ComplexCode) :
    toComplex (complexAdd z w) = toComplex z + toComplex w := by
  simp [toComplex, complexAdd]
  ring

@[simp] theorem toComplex_neg (z : ComplexCode) :
    toComplex (complexNeg z) = -toComplex z := by
  simp [toComplex, complexNeg]
  ring

@[simp] theorem toComplex_mul (z w : ComplexCode) :
    toComplex (complexMul z w) = toComplex z * toComplex w := by
  apply Complex.ext
  · simp [toComplex, complexMul]
    ring
  · simp [toComplex, complexMul]

@[simp] theorem toComplex_conj (z : ComplexCode) :
    toComplex (complexConj z) = star (toComplex z) := by
  apply Complex.ext <;> simp [toComplex, complexConj]

def ComplexEq (z w : ComplexCode) : Prop := RatEq z.1 w.1 ∧ RatEq z.2 w.2

instance complexEqDecidable : DecidableRel ComplexEq := fun _ _ => by
  unfold ComplexEq
  infer_instance

theorem complexEq_iff (z w : ComplexCode) : ComplexEq z w ↔ toComplex z = toComplex w := by
  rw [ComplexEq, ratEq_iff, ratEq_iff]
  constructor
  · rintro ⟨hre, him⟩
    apply Complex.ext <;> simp [toComplex, hre, him]
  · intro h
    constructor
    · have := congrArg Complex.re h
      simpa [toComplex] using this
    · have := congrArg Complex.im h
      simpa [toComplex] using this

theorem primrec_complexAdd : Primrec₂ complexAdd := by
  apply Primrec₂.mk
  exact Primrec.pair
    (primrec_ratAdd.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (primrec_ratAdd.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

theorem primrec_complexNeg : Primrec complexNeg :=
  Primrec.pair (primrec_ratNeg.comp Primrec.fst) (primrec_ratNeg.comp Primrec.snd)

theorem primrec_complexMul : Primrec₂ complexMul := by
  apply Primrec₂.mk
  let zr : Primrec fun p : ComplexCode × ComplexCode => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  let zi : Primrec fun p : ComplexCode × ComplexCode => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  let wr : Primrec fun p : ComplexCode × ComplexCode => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  let wi : Primrec fun p : ComplexCode × ComplexCode => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.pair
    (primrec_ratAdd.comp (primrec_ratMul.comp zr wr)
      (primrec_ratNeg.comp (primrec_ratMul.comp zi wi)))
    (primrec_ratAdd.comp (primrec_ratMul.comp zr wi) (primrec_ratMul.comp zi wr))

theorem primrec_complexConj : Primrec complexConj :=
  Primrec.pair Primrec.fst (primrec_ratNeg.comp Primrec.snd)

theorem primrecRel_complexEq : PrimrecRel ComplexEq :=
  (primrecRel_ratEq.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
      (Primrec.fst.comp₂ Primrec₂.right)).and
    (primrecRel_ratEq.comp₂ (Primrec.snd.comp₂ Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.right))

end RationalComplexCode
end GroupApproximation
