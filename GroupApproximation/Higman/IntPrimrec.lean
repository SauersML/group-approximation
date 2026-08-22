import Mathlib.Computability.Primrec.Basic

/-!
# Primitive recursive arithmetic on `ℤ`

Pinned Mathlib has **no** declaration mentioning both `Int` and `Primrec`: the
computability library is built over `Primcodable` types and `ℤ` is one of them,
but not a single arithmetic operation on it has been recorded as primitive
recursive.  `Higman.HigmanCodingDictionary` therefore carries
`Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)` as a standing hypothesis, written `hadd`
there, and eight of its theorems are stated conditionally on it.  This module
discharges that hypothesis, and three of its neighbours, once and for all.

## The encoding

`Primcodable ℤ` is `Primcodable.ofDenumerable` over `Denumerable.int`, which is
`Denumerable.mk' Equiv.intEquivNat`, and `Equiv.intEquivNat` factors as
`Equiv.intEquivNatSumNat` followed by `Equiv.natSumNatEquivNat`.  Reading that
chain off at a constructor gives

    Encodable.encode (Int.ofNat k)   = 2 * k ,
    Encodable.encode (Int.negSucc k) = 2 * k + 1 ,

both by `rfl` --- `Equiv.natSumNatEquivNat_apply` is proved the same way
upstream, so `Nat.bit false k` really does reduce to `2 * k`.  So the sign of an
integer is the parity of its code, and its magnitude is the code halved.
`ofNat_int_eq` is that statement in the direction the proofs want: it computes
`Denumerable.ofNat ℤ m` from `m % 2` and `m / 2`.

## Why the proofs look the way they do

Every one of the four results is proved by the same three-step move.

1. `Primrec.ofNat_iff` / `Primrec₂.ofNat_iff` replace the `ℤ`-indexed question
   by its `ℕ`-indexed form.  These are unconditional and already in Mathlib;
   nothing about `ℤ` is used beyond `Denumerable ℤ`.
2. `Primrec.encode_iff` / `Primrec₂.encode_iff` replace the `ℤ`-valued answer by
   its code, leaving a question about an explicit function `ℕ → ℕ` --- `encAdd`
   for addition, `encNeg` for negation, `leEnc` for the order.  Each is a
   handful of parity tests and `ℕ` arithmetic, hence `Primrec` by
   `Primrec.nat_add`, `Primrec.nat_sub`, `Primrec.nat_mod`, `Primrec.nat_le`,
   `Primrec.nat_lt`, `Primrec.eq` and `Primrec.ite` alone.
3. The two are matched by a pointwise identity --- `encAdd_spec`, `encNeg_spec`,
   `leEnc_spec` --- stated on the `ofNat` side rather than the `encode` side, so
   that after `ofNat_int_eq` the goal is pure linear arithmetic over `ℕ` and `ℤ`
   with division and truncated subtraction by the literal `2`, which is exactly
   what `omega` decides.  `Denumerable.encode_ofNat` then closes the transfer.

The four branches of `encAdd` are the four sign combinations: two like signs
add, and the two mixed pairs are a comparison followed by a truncated
subtraction, the comparison being on the codes rather than on the integers
because `2 * a` beats `2 * b + 1` exactly when `b < a`.

## What this unlocks

`Higman.Seq.primrec_evalCode`, `Higman.Seq.primrec_windowCheck`,
`Higman.Seq.primrec_decodeCoords`, `Higman.Seq.REset_of_rePred_coords`,
`Higman.Seq.REset_window_iff`, `Higman.Seq.rePred_coordsOf_iff`,
`Higman.Seq.boundedWindowRE_iff_coord` and `Higman.Seq.primrec_natCast_int` all
take `hadd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)` as their only hypothesis, and
`primrec2_int_add` below is that hypothesis.  Supplying it to each turns all
eight unconditional; no other change to that module is needed.  The last of
them is reproved here directly as `primrec_int_natCast`, since it costs one
line once the code of `Int.ofNat` is known.

`primrec2_int_sub`, `primrec_int_neg` and `primrec2_int_le` are not used by the
coding dictionary but are the same one-time gap, and the window arguments
downstream need the order.
-/

namespace GroupApproximation
namespace Higman

/-! ## 1.  The code of an integer

Two `rfl`s and their consequences.  These are the only places where the
concrete shape of `Primcodable ℤ` is touched; everything below is stated in
terms of `Denumerable.ofNat`. -/

/-- A non-negative integer has an even code. -/
theorem encode_int_ofNat (a : ℕ) : (Encodable.encode (Int.ofNat a) : ℕ) = 2 * a := rfl

/-- A negative integer has an odd code. -/
theorem encode_int_negSucc (a : ℕ) : (Encodable.encode (Int.negSucc a) : ℕ) = 2 * a + 1 := rfl

/-- The even codes decode to the non-negative integers. -/
theorem ofNat_two_mul (a : ℕ) : Denumerable.ofNat ℤ (2 * a) = (a : ℤ) := by
  have h : Denumerable.ofNat ℤ (Encodable.encode (Int.ofNat a)) = Int.ofNat a :=
    Denumerable.ofNat_encode _
  rw [encode_int_ofNat] at h
  exact h

/-- The odd codes decode to the negative integers. -/
theorem ofNat_two_mul_add_one (a : ℕ) : Denumerable.ofNat ℤ (2 * a + 1) = -(a : ℤ) - 1 := by
  have h : Denumerable.ofNat ℤ (Encodable.encode (Int.negSucc a)) = Int.negSucc a :=
    Denumerable.ofNat_encode _
  rw [encode_int_negSucc] at h
  rw [h]
  omega

/-- **Decoding, in closed form.**  The parity of the code is the sign and half
the code is the magnitude.  This is the only fact about the encoding that the
arithmetic below consumes, and it is stated so that `omega` can use it. -/
theorem ofNat_int_eq (m : ℕ) :
    Denumerable.ofNat ℤ m
      = if m % 2 = 0 then ((m / 2 : ℕ) : ℤ) else -((m / 2 : ℕ) : ℤ) - 1 := by
  by_cases h : m % 2 = 0
  · rw [if_pos h]
    obtain ⟨a, rfl⟩ : ∃ a, m = 2 * a := ⟨m / 2, by omega⟩
    rw [ofNat_two_mul]
    omega
  · rw [if_neg h]
    obtain ⟨a, rfl⟩ : ∃ a, m = 2 * a + 1 := ⟨m / 2, by omega⟩
    rw [ofNat_two_mul_add_one]
    omega

/-! ## 2.  Addition

`encAdd` is addition read in codes.  Like signs add; mixed signs compare and
subtract. -/

/-- Addition of integers, transported to their codes. -/
def encAdd (m k : ℕ) : ℕ :=
  if m % 2 = 0 then
    if k % 2 = 0 then m + k
    else if k < m then m - k - 1 else k - m
  else
    if k % 2 = 0 then (if m < k then k - m - 1 else m - k)
    else m + k + 1

theorem encAdd_def (m k : ℕ) :
    encAdd m k =
      if m % 2 = 0 then
        if k % 2 = 0 then m + k
        else if k < m then m - k - 1 else k - m
      else
        if k % 2 = 0 then (if m < k then k - m - 1 else m - k)
        else m + k + 1 := rfl

/-- `encAdd` is built from `Primrec.nat_add`, `Primrec.nat_sub`,
`Primrec.nat_mod`, `Primrec.nat_lt`, `Primrec.eq` and `Primrec.ite`. -/
theorem primrec2_encAdd : Primrec₂ encAdd := by
  have hf : Primrec (Prod.fst : ℕ × ℕ → ℕ) := Primrec.fst
  have hs : Primrec (Prod.snd : ℕ × ℕ → ℕ) := Primrec.snd
  have hmev : PrimrecPred fun p : ℕ × ℕ => p.1 % 2 = 0 :=
    Primrec.eq.comp (Primrec.nat_mod.comp hf (Primrec.const 2)) (Primrec.const 0)
  have hkev : PrimrecPred fun p : ℕ × ℕ => p.2 % 2 = 0 :=
    Primrec.eq.comp (Primrec.nat_mod.comp hs (Primrec.const 2)) (Primrec.const 0)
  have hkm : PrimrecPred fun p : ℕ × ℕ => p.2 < p.1 := Primrec.nat_lt.comp hs hf
  have hmk : PrimrecPred fun p : ℕ × ℕ => p.1 < p.2 := Primrec.nat_lt.comp hf hs
  have hsum : Primrec fun p : ℕ × ℕ => p.1 + p.2 := Primrec.nat_add.comp hf hs
  have hsum1 : Primrec fun p : ℕ × ℕ => p.1 + p.2 + 1 :=
    Primrec.nat_add.comp hsum (Primrec.const 1)
  have hd : Primrec fun p : ℕ × ℕ => p.1 - p.2 := Primrec.nat_sub.comp hf hs
  have hd' : Primrec fun p : ℕ × ℕ => p.2 - p.1 := Primrec.nat_sub.comp hs hf
  have hd1 : Primrec fun p : ℕ × ℕ => p.1 - p.2 - 1 :=
    Primrec.nat_sub.comp hd (Primrec.const 1)
  have hd1' : Primrec fun p : ℕ × ℕ => p.2 - p.1 - 1 :=
    Primrec.nat_sub.comp hd' (Primrec.const 1)
  exact Primrec.ite hmev (Primrec.ite hkev hsum (Primrec.ite hkm hd1 hd'))
    (Primrec.ite hkev (Primrec.ite hmk hd1' hd) hsum1)

/-- **`encAdd` really is addition.**  Stated on the decoding side, where the
four sign cases are linear arithmetic in `m / 2`, `k / 2` and the parities. -/
theorem encAdd_spec (m k : ℕ) :
    Denumerable.ofNat ℤ (encAdd m k)
      = Denumerable.ofNat ℤ m + Denumerable.ofNat ℤ k := by
  simp only [encAdd_def, ofNat_int_eq]
  split_ifs <;> omega

/-- **Addition of integers is primitive recursive.**  This is the `hadd`
hypothesis of `Higman.HigmanCodingDictionary`; supplying it discharges the eight
theorems there that are stated conditionally on it. -/
theorem primrec2_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  refine Primrec₂.ofNat_iff.mpr ?_
  refine Primrec₂.encode_iff.mp ?_
  refine primrec2_encAdd.of_eq fun m k => ?_
  rw [← encAdd_spec m k, Denumerable.encode_ofNat]

/-! ## 3.  Negation and subtraction

Negation flips the parity of the code, and the truncated `m - 1` handles zero
for free: the code of `0` is `0`, and `0 - 1 = 0` in `ℕ`. -/

/-- Negation of integers, transported to their codes. -/
def encNeg (m : ℕ) : ℕ := if m % 2 = 0 then m - 1 else m + 1

theorem encNeg_def (m : ℕ) : encNeg m = if m % 2 = 0 then m - 1 else m + 1 := rfl

theorem primrec_encNeg : Primrec encNeg := by
  have hmev : PrimrecPred fun m : ℕ => m % 2 = 0 :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  exact Primrec.ite hmev (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
    (Primrec.nat_add.comp Primrec.id (Primrec.const 1))

theorem encNeg_spec (m : ℕ) :
    Denumerable.ofNat ℤ (encNeg m) = -Denumerable.ofNat ℤ m := by
  simp only [encNeg_def, ofNat_int_eq]
  split_ifs <;> omega

/-- **Negation of integers is primitive recursive.** -/
theorem primrec_int_neg : Primrec (fun z : ℤ => -z) := by
  refine Primrec.ofNat_iff.mpr ?_
  refine Primrec.encode_iff.mp ?_
  refine primrec_encNeg.of_eq fun m => ?_
  rw [← encNeg_spec m, Denumerable.encode_ofNat]

/-- **Subtraction of integers is primitive recursive.**  No new arithmetic: it
is addition after negation. -/
theorem primrec2_int_sub : Primrec₂ ((· - ·) : ℤ → ℤ → ℤ) :=
  (primrec2_int_add.comp₂ Primrec₂.left (primrec_int_neg.comp₂ Primrec₂.right)).of_eq
    fun a b => (sub_eq_add_neg a b).symm

/-! ## 4.  The order

A negative integer is below every non-negative one, so the comparison is a
parity test and then one `ℕ` comparison --- forward on the non-negative side
and reversed on the negative side, since larger magnitude means smaller
integer. -/

/-- The order on integers, transported to their codes. -/
def leEnc (m k : ℕ) : Prop :=
  (m % 2 = 0 ∧ k % 2 = 0 ∧ m ≤ k) ∨ (m % 2 = 1 ∧ k % 2 = 0) ∨
    (m % 2 = 1 ∧ k % 2 = 1 ∧ k ≤ m)

theorem leEnc_def (m k : ℕ) :
    leEnc m k ↔
      (m % 2 = 0 ∧ k % 2 = 0 ∧ m ≤ k) ∨ (m % 2 = 1 ∧ k % 2 = 0) ∨
        (m % 2 = 1 ∧ k % 2 = 1 ∧ k ≤ m) := Iff.rfl

theorem primrecRel_leEnc : PrimrecRel leEnc := by
  have hf : Primrec (Prod.fst : ℕ × ℕ → ℕ) := Primrec.fst
  have hs : Primrec (Prod.snd : ℕ × ℕ → ℕ) := Primrec.snd
  have hm : ∀ r : ℕ, PrimrecPred fun p : ℕ × ℕ => p.1 % 2 = r := fun r =>
    Primrec.eq.comp (Primrec.nat_mod.comp hf (Primrec.const 2)) (Primrec.const r)
  have hk : ∀ r : ℕ, PrimrecPred fun p : ℕ × ℕ => p.2 % 2 = r := fun r =>
    Primrec.eq.comp (Primrec.nat_mod.comp hs (Primrec.const 2)) (Primrec.const r)
  have hle : PrimrecPred fun p : ℕ × ℕ => p.1 ≤ p.2 := Primrec.nat_le.comp hf hs
  have hge : PrimrecPred fun p : ℕ × ℕ => p.2 ≤ p.1 := Primrec.nat_le.comp hs hf
  exact ((hm 0).and ((hk 0).and hle)).or (((hm 1).and (hk 0)).or ((hm 1).and ((hk 1).and hge)))

theorem leEnc_spec (m k : ℕ) :
    leEnc m k ↔ Denumerable.ofNat ℤ m ≤ Denumerable.ofNat ℤ k := by
  simp only [leEnc_def, ofNat_int_eq]
  split_ifs <;> omega

/-- **The order on integers is a primitive recursive relation.** -/
theorem primrec2_int_le : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) :=
  (primrecRel_leEnc.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
      (Primrec.encode.comp₂ Primrec₂.right)).of_eq fun _ _ => by
    simp only [leEnc_spec, Denumerable.ofNat_encode]

/-- The `Bool`-valued form of `primrec2_int_le`, for the callers that want a
`Primrec₂` rather than a `PrimrecRel`. -/
theorem primrec2_int_decide_le : Primrec₂ (fun x y : ℤ => decide (x ≤ y)) :=
  primrec2_int_le.decide

/-! ## 5.  The cast

`Higman.Seq.primrec_natCast_int` derives this from `hadd` by a primitive
recursion; with the code of `Int.ofNat` in hand it is immediate, since the cast
is doubling on codes. -/

/-- **The cast `ℕ → ℤ` is primitive recursive.** -/
theorem primrec_int_natCast : Primrec (fun m : ℕ => (m : ℤ)) := by
  refine Primrec.encode_iff.mp ?_
  refine (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq fun m => ?_
  exact (encode_int_ofNat m).symm

end Higman
end GroupApproximation
