import GroupApproximation.Computability.BinaryDigitPrimrec
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Mathlib's `trNat`, as a halving recurrence

`Turing.PartrecToTM2.trNat` encodes a natural number as a list of `Γ'` symbols
through `Num` and `PosNum`, which is convenient for the inductions Mathlib does
with it and inconvenient for computability: nothing in Mathlib presents it as a
recurrence in the number itself, so there is no handle for `Primrec`.

This module supplies the missing shape,

    trNat m = (if m % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat (m / 2)   (m > 0)

and the consequence that matters for `D4'`: for any reading `g : Γ' → ℕ` of the
alphabet, `(trNat m).map g` is `binDigits (g Γ'.bit0) (g Γ'.bit1) m`, hence
computable.  That is what turns the index map of
`exists_modularMachine_halting_not_computablePred` into an arithmetic function
of its input, with the choice-based symbol encoding entering only as the two
fixed naturals `g Γ'.bit0` and `g Γ'.bit1`.

No induction is needed for the recurrence.  `trPosNum` already recurses on the
bit structure of a `PosNum`, and `PosNum.cast_bit0`/`cast_bit1` say that
structure *is* division by two, so a case analysis on the constructor suffices;
the round trip `Num.of_to_nat` is what lets a positive natural be named by its
`PosNum`.
-/

namespace GroupApproximation
namespace Computability

open Turing.PartrecToTM2

/-- A positive number is encoded by its own `PosNum`. -/
theorem trNat_posNum (p : PosNum) : trNat (p : ℕ) = trPosNum p := by
  have h : (((p : ℕ) : Num)) = Num.pos p := by simp
  rw [trNat, h]
  rfl

/-- **The halving recurrence, on `PosNum`.**  The three constructors are the
three cases of "is the number one, even, or odd", and `cast_bit0`/`cast_bit1`
identify the bit structure with division by two. -/
theorem trPosNum_eq (p : PosNum) :
    trPosNum p
      = (if (p : ℕ) % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat ((p : ℕ) / 2) := by
  cases p with
  | one => simp [trPosNum, trNat_zero]
  | bit1 q =>
      have h2 : ((q : ℕ) + (q : ℕ) + 1) % 2 = 1 := by omega
      have h3 : ((q : ℕ) + (q : ℕ) + 1) / 2 = (q : ℕ) := by omega
      show Γ'.bit1 :: trPosNum q = _
      rw [PosNum.cast_bit1, h2, h3, trNat_posNum]
      simp
  | bit0 q =>
      have h2 : ((q : ℕ) + (q : ℕ)) % 2 = 0 := by omega
      have h3 : ((q : ℕ) + (q : ℕ)) / 2 = (q : ℕ) := by omega
      show Γ'.bit0 :: trPosNum q = _
      rw [PosNum.cast_bit0, h2, h3, trNat_posNum]
      simp

/-- **The halving recurrence.**  Mathlib has `trNat_zero`; this is the step. -/
theorem trNat_eq_cons (m : ℕ) (hm : 0 < m) :
    trNat m = (if m % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat (m / 2) := by
  cases h : (m : Num) with
  | zero =>
      exfalso
      have : m = 0 := by
        have := Num.to_of_nat m
        rw [h] at this
        simpa using this.symm
      omega
  | pos p =>
      have hp : (p : ℕ) = m := by
        have := Num.to_of_nat m
        rw [h] at this
        simpa using this
      rw [← hp, trNat_posNum, trPosNum_eq]

/-- **The reading of `trNat` is the binary digit list.**  This is the bridge to
`binDigits`, and with it to `Primrec`. -/
theorem map_trNat_eq_binDigits (g : Γ' → ℕ) :
    ∀ m : ℕ, (trNat m).map g = binDigits (g Γ'.bit0) (g Γ'.bit1) m
  | 0 => by simp [trNat_zero]
  | (n + 1) => by
      rw [trNat_eq_cons (n + 1) (Nat.succ_pos n), List.map_cons, binDigits_succ,
        map_trNat_eq_binDigits g ((n + 1) / 2), apply_ite g]
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) Nat.one_lt_two

/-- **The reading of `trNat` is computable.**  The alphabet is read by an
arbitrary `g`, so in particular by a choice-based encoding: only the two values
`g Γ'.bit0` and `g Γ'.bit1` enter, and they are fixed naturals. -/
theorem computable_map_trNat (g : Γ' → ℕ) :
    Computable (fun m : ℕ => (trNat m).map g) := by
  have h := computable_binDigits (g Γ'.bit0) (g Γ'.bit1)
  exact h.of_eq fun m => (map_trNat_eq_binDigits g m).symm

end Computability
end GroupApproximation
