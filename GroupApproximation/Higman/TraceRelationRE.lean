import GroupApproximation.Higman.EnumeratedRangeTraceCorrectness
import GroupApproximation.Higman.HigmanCodingDictionary

/-!
# The transition relation of a trace is recursively enumerable

`Higman.EnumeratedRangeTraceCorrectness` leaves two obligations behind
`Seq.higmanGenerated_range_of_projection`.  This module discharges the first:

    REset (blockPairSet (traceRel c))   for every computable `c`.

`Seq.traceRel` is a four-case condition on eight integers, and the only thing in
it that is not decidable arithmetic is the enumeration: `Seq.loIdx`,
`Seq.hiIdx` and `Seq.gseq`, all read at the index `Seq.parIdx` recovers from a
parameter.  Those three are computable in the block data, so the whole condition
is a *computable* predicate on codes, hence recursively enumerable.

## The coding layer of `ℤ`, discharged

`Higman.HigmanCodingDictionary` records that pinned Mathlib has no declaration
mentioning both `Int` and `Primrec`, and carries its arithmetic as the single
hypothesis `hadd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)`.  That hypothesis is proved
here, and with it the order, the truncation `Int.toNat` and `min`/`max`.

The whole layer rests on one fact, and it is a fact about the *encoding*:
`Primcodable ℤ` is `Primcodable.ofDenumerable` through `Equiv.intEquivNat`,
which factors as `ℤ ≃ ℕ ⊕ ℕ ≃ ℕ` with the second step `2n` and `2n+1` --- the
same sum encoding `Primcodable.sum` uses.  So

    Encodable.encode (i : ℤ) = Encodable.encode (Seq.intSplit i)

holds *definitionally*, and `Primrec.encode_iff` turns it into
`Seq.primrec_intSplit` and `Seq.primrec_intJoin`.  Everything else is
`Primrec.sumCasesOn` over the two summands together with `ℕ` arithmetic:
`Seq.zpos` and `Seq.zneg` split an integer into a difference of naturals
(`Seq.zpos_sub_zneg`), `Seq.natDiffZ` puts one back together, and addition,
order and truncation are read off the split.  No branch of the argument needs
`Int.negSucc` inside `omega`; `Int.negSucc_eq` is applied first each time.

## The shape of the reduction

The enumeration enters only through six integers --- the two ends of the window
of each of the two parameters, and the value of each member at the counter of
its block --- so `Seq.traceRel` is `Seq.traceRelOn` at those six
(`Seq.traceRel_iff`), and `Seq.traceRelOn` mentions nothing but integers.
`Seq.traceOK` is therefore a *primitive-recursive* predicate on the pair (code,
window data), `Seq.traceData` is the computable map producing the window data
from the code, and `Seq.computablePred_comp_primrecPred` composes the two.  The
window-support half is `Seq.windowCheck 8`, already built and already proved
correct in the coding dictionary.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  The sign splitting of `ℤ`, primitively

`Primcodable ℤ` encodes `Int.ofNat n` as `2n` and `Int.negSucc n` as `2n+1`, and
`Primcodable (ℕ ⊕ ℕ)` encodes `Sum.inl n` and `Sum.inr n` the same way.  The two
encodings are therefore the same function, which is what the two `rfl`s below
say.  This is the only place in the file where the encoding is inspected. -/

/-- An integer as a signed natural number. -/
def intSplit : ℤ → ℕ ⊕ ℕ
  | Int.ofNat n => Sum.inl n
  | Int.negSucc n => Sum.inr n

/-- A signed natural number as an integer. -/
def intJoin : ℕ ⊕ ℕ → ℤ
  | Sum.inl n => Int.ofNat n
  | Sum.inr n => Int.negSucc n

/-- **The sign splitting is primitive recursive.**  It is the identity on
encodings. -/
theorem primrec_intSplit : Primrec intSplit := by
  refine Primrec.encode_iff.1 (Primrec.encode.of_eq ?_)
  intro i
  cases i <;> rfl

/-- **And so is its inverse.** -/
theorem primrec_intJoin : Primrec intJoin := by
  refine Primrec.encode_iff.1 (Primrec.encode.of_eq ?_)
  intro s
  cases s <;> rfl

/-! ## 2.  An integer as a difference of two naturals -/

/-- The nonnegative part of an integer. -/
def zpos : ℤ → ℕ
  | Int.ofNat n => n
  | Int.negSucc _ => 0

/-- The magnitude of the negative part of an integer. -/
def zneg : ℤ → ℕ
  | Int.ofNat _ => 0
  | Int.negSucc n => n + 1

theorem zpos_sub_zneg (i : ℤ) : (zpos i : ℤ) - (zneg i : ℤ) = i := by
  cases i with
  | ofNat n =>
      show (n : ℤ) - ((0 : ℕ) : ℤ) = (n : ℤ)
      omega
  | negSucc n =>
      show ((0 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) = Int.negSucc n
      rw [Int.negSucc_eq]
      omega

theorem primrec_zpos : Primrec zpos := by
  have hg : Primrec₂ fun (_ : ℤ) (n : ℕ) => n := Primrec₂.right
  exact (Primrec.sumCasesOn primrec_intSplit hg (Primrec₂.const 0)).of_eq fun i => by
    cases i <;> rfl

theorem primrec_zneg : Primrec zneg := by
  have hh : Primrec₂ fun (_ : ℤ) (n : ℕ) => Nat.succ n := Primrec.succ.comp Primrec.snd
  exact (Primrec.sumCasesOn primrec_intSplit (Primrec₂.const 0) hh).of_eq fun i => by
    cases i <;> rfl

/-- The integer difference of two naturals, assembled from the two injections
and `ℕ` subtraction alone. -/
def natDiffZ (m n : ℕ) : ℤ :=
  if n ≤ m then intJoin (Sum.inl (m - n)) else intJoin (Sum.inr (n - m - 1))

theorem natDiffZ_eq (m n : ℕ) : natDiffZ m n = (m : ℤ) - (n : ℤ) := by
  unfold natDiffZ
  split_ifs with h
  · show ((m - n : ℕ) : ℤ) = (m : ℤ) - (n : ℤ)
    omega
  · show Int.negSucc (n - m - 1) = (m : ℤ) - (n : ℤ)
    rw [Int.negSucc_eq]
    omega

theorem primrec_natDiffZ : Primrec₂ natDiffZ := by
  have h : Primrec fun p : ℕ × ℕ =>
      if p.2 ≤ p.1 then intJoin (Sum.inl (p.1 - p.2)) else intJoin (Sum.inr (p.2 - p.1 - 1)) :=
    Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
      (primrec_intJoin.comp (Primrec.sumInl.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd)))
      (primrec_intJoin.comp (Primrec.sumInr.comp
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
          (Primrec.const 1))))
  exact h.of_eq fun _ => rfl

/-! ## 3.  The arithmetic of `ℤ`

`Seq.primrec_intAdd` is the hypothesis `hadd` of `Higman.HigmanCodingDictionary`,
and it is used there under that name; discharging it here discharges it for the
whole fan-out. -/

/-- **Addition on `ℤ` is primitive recursive.**  This is `hadd`. -/
theorem primrec_intAdd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  have h : Primrec fun p : ℤ × ℤ =>
      natDiffZ (zpos p.1 + zpos p.2) (zneg p.1 + zneg p.2) :=
    primrec_natDiffZ.comp
      (Primrec.nat_add.comp (primrec_zpos.comp Primrec.fst) (primrec_zpos.comp Primrec.snd))
      (Primrec.nat_add.comp (primrec_zneg.comp Primrec.fst) (primrec_zneg.comp Primrec.snd))
  refine h.of_eq fun p => ?_
  have h1 := zpos_sub_zneg p.1
  have h2 := zpos_sub_zneg p.2
  rw [natDiffZ_eq]
  push_cast
  omega

/-- **The order on `ℤ` is primitive recursive.** -/
theorem primrec_intLe : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) := by
  have h : PrimrecRel fun a b : ℤ => zpos a + zneg b ≤ zpos b + zneg a :=
    Primrec.nat_le.comp₂
      (Primrec.nat_add.comp₂ (primrec_zpos.comp₂ Primrec₂.left)
        (primrec_zneg.comp₂ Primrec₂.right))
      (Primrec.nat_add.comp₂ (primrec_zpos.comp₂ Primrec₂.right)
        (primrec_zneg.comp₂ Primrec₂.left))
  refine h.of_eq fun a b => ?_
  have h1 := zpos_sub_zneg a
  have h2 := zpos_sub_zneg b
  omega

theorem primrec_intLt : PrimrecRel ((· < ·) : ℤ → ℤ → Prop) := by
  have h : PrimrecRel fun a b : ℤ => zpos a + zneg b < zpos b + zneg a :=
    Primrec.nat_lt.comp₂
      (Primrec.nat_add.comp₂ (primrec_zpos.comp₂ Primrec₂.left)
        (primrec_zneg.comp₂ Primrec₂.right))
      (Primrec.nat_add.comp₂ (primrec_zpos.comp₂ Primrec₂.right)
        (primrec_zneg.comp₂ Primrec₂.left))
  refine h.of_eq fun a b => ?_
  have h1 := zpos_sub_zneg a
  have h2 := zpos_sub_zneg b
  omega

theorem primrec_intToNat : Primrec Int.toNat :=
  primrec_zpos.of_eq fun i => by cases i <;> rfl

theorem primrec_intMin : Primrec₂ (min : ℤ → ℤ → ℤ) := by
  have h : Primrec fun p : ℤ × ℤ => if p.1 ≤ p.2 then p.1 else p.2 :=
    Primrec.ite (primrec_intLe.comp Primrec.fst Primrec.snd) Primrec.fst Primrec.snd
  refine h.of_eq fun p => ?_
  by_cases hh : p.1 ≤ p.2
  · rw [if_pos hh, min_eq_left hh]
  · rw [if_neg hh, min_eq_right (not_le.mp hh).le]

theorem primrec_intMax : Primrec₂ (max : ℤ → ℤ → ℤ) := by
  have h : Primrec fun p : ℤ × ℤ => if p.1 ≤ p.2 then p.2 else p.1 :=
    Primrec.ite (primrec_intLe.comp Primrec.fst Primrec.snd) Primrec.snd Primrec.fst
  refine h.of_eq fun p => ?_
  by_cases hh : p.1 ≤ p.2
  · rw [if_pos hh, max_eq_right hh]
  · rw [if_neg hh, max_eq_left (not_le.mp hh).le]

/-! ## 4.  The window of a code, and the index a parameter carries -/

/-- The left end of the normalized window of a code.  `Seq.loIdx` is this at the
`r`-th member. -/
def loOf (l : List (ℤ × ℤ)) : ℤ := (l.map Prod.fst).foldr min 0

/-- The right end. -/
def hiOf (l : List (ℤ × ℤ)) : ℤ := (l.map Prod.fst).foldr max 0

theorem loIdx_eq (c : ℕ → List (ℤ × ℤ)) (r : ℕ) : loIdx c r = loOf (c r) := rfl

theorem hiIdx_eq (c : ℕ → List (ℤ × ℤ)) (r : ℕ) : hiIdx c r = hiOf (c r) := rfl

theorem primrec_firsts : Primrec fun l : List (ℤ × ℤ) => l.map Prod.fst := by
  refine (Primrec.list_map Primrec.id ?_).of_eq fun _ => rfl
  exact (Primrec.fst.comp Primrec.snd).to₂

theorem primrec_loOf : Primrec loOf := by
  have hstep : Primrec₂ fun (_ : List (ℤ × ℤ)) (bs : ℤ × ℤ) => min bs.1 bs.2 :=
    primrec_intMin.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr primrec_firsts (Primrec.const (0 : ℤ)) hstep).of_eq fun _ => rfl

theorem primrec_hiOf : Primrec hiOf := by
  have hstep : Primrec₂ fun (_ : List (ℤ × ℤ)) (bs : ℤ × ℤ) => max bs.1 bs.2 :=
    primrec_intMax.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr primrec_firsts (Primrec.const (0 : ℤ)) hstep).of_eq fun _ => rfl

/-- The index a parameter carries, in `ℕ` arithmetic: an active block carries
`r + 1`, and an inactive one carries `0`, which truncates to `0` either way. -/
theorem parIdx_eq (p : ℤ) : parIdx p = p.toNat - 1 := by
  unfold parIdx
  omega

theorem primrec_parIdx : Primrec parIdx :=
  (Primrec.nat_sub.comp primrec_intToNat (Primrec.const 1)).of_eq fun p => (parIdx_eq p).symm

/-! ## 5.  The relation, with the enumeration factored out

Everything `Seq.traceRel` asks of the enumeration is six integers: the two ends
of the window of each parameter, and the value of the corresponding member at
the counter of its block.  `Seq.traceRelOn` is the relation with those six
supplied, and it mentions nothing but integers. -/

/-- **`Seq.traceRel`, with the window data supplied explicitly.** -/
def traceRelOn (lo hi w lo' hi' w' v j p m v' j' p' m' : ℤ) : Prop :=
  0 ≤ p ∧ 0 ≤ p' ∧
  m = (if 1 ≤ p ∧ j = 0 then 1 else 0) ∧
  m' = (if 1 ≤ p' ∧ j' = 0 then 1 else 0) ∧
  (p = 0 → v = 0 ∧ j = 0) ∧
  (p' = 0 → v' = 0 ∧ j' = 0) ∧
  (1 ≤ p → lo ≤ j ∧ j ≤ hi ∧ v = w) ∧
  (1 ≤ p' → lo' ≤ j' ∧ j' ≤ hi' ∧ v' = w') ∧
  (1 ≤ p → 1 ≤ p' → p' = p ∧ j' = j + 1) ∧
  (1 ≤ p → p' = 0 → j = hi) ∧
  (p = 0 → 1 ≤ p' → j' = lo')

/-- **The factorization.**  The only step is `Seq.seqOfList_apply`: the value of
a member is the value its code computes. -/
theorem traceRel_iff (c : ℕ → List (ℤ × ℤ)) (v j p m v' j' p' m' : ℤ) :
    traceRel c v j p m v' j' p' m' ↔
      traceRelOn (loIdx c (parIdx p)) (hiIdx c (parIdx p)) (evalCode (c (parIdx p)) j)
        (loIdx c (parIdx p')) (hiIdx c (parIdx p')) (evalCode (c (parIdx p')) j')
        v j p m v' j' p' m' := by
  have h1 : gseq c (parIdx p) j = evalCode (c (parIdx p)) j :=
    seqOfList_apply (c (parIdx p)) j
  have h2 : gseq c (parIdx p') j' = evalCode (c (parIdx p')) j' :=
    seqOfList_apply (c (parIdx p')) j'
  unfold traceRel traceRelOn
  rw [h1, h2]

/-! ## 6.  The check, and the data it reads -/

/-- The datum the block-pair check reads: the code of the window, and the window
data of the two parameters. -/
abbrev TraceInput : Type := List (ℤ × ℤ) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))

/-- The window data the transition relation reads off the enumeration, as a
function of the code of the window. -/
def traceData (c : ℕ → List (ℤ × ℤ)) (l : List (ℤ × ℤ)) : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) :=
  ((loIdx c (parIdx (evalCode l 2)), hiIdx c (parIdx (evalCode l 2)),
      evalCode (c (parIdx (evalCode l 2))) (evalCode l 1)),
    (loIdx c (parIdx (evalCode l 6)), hiIdx c (parIdx (evalCode l 6)),
      evalCode (c (parIdx (evalCode l 6))) (evalCode l 5)))

/-- **The block-pair check.**  Nothing in it mentions the enumeration: the
window data is an argument. -/
def traceOK (x : TraceInput) : Prop :=
  windowCheck 8 x.1 = true ∧
    traceRelOn x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2
      (evalCode x.1 0) (evalCode x.1 1) (evalCode x.1 2) (evalCode x.1 3)
      (evalCode x.1 4) (evalCode x.1 5) (evalCode x.1 6) (evalCode x.1 7)

/-- **The check is the membership.** -/
theorem traceOK_iff (c : ℕ → List (ℤ × ℤ)) (l : List (ℤ × ℤ)) :
    traceOK (l, traceData c l) ↔ seqOfList l ∈ blockPairSet (traceRel c) := by
  have hv : ∀ k : ℤ, seqOfList l k = evalCode l k := fun k => seqOfList_apply l k
  rw [mem_blockPairSet_iff]
  constructor
  · rintro ⟨hw, hr⟩
    refine ⟨(windowCheck_eq_true_iff 8 l).mp hw, ?_⟩
    refine (traceRel_iff c (seqOfList l 0) (seqOfList l 1) (seqOfList l 2) (seqOfList l 3)
      (seqOfList l 4) (seqOfList l 5) (seqOfList l 6) (seqOfList l 7)).mpr ?_
    simp only [hv]
    exact hr
  · rintro ⟨hw, hr⟩
    refine ⟨(windowCheck_eq_true_iff 8 l).mpr hw, ?_⟩
    have hr' := (traceRel_iff c (seqOfList l 0) (seqOfList l 1) (seqOfList l 2) (seqOfList l 3)
      (seqOfList l 4) (seqOfList l 5) (seqOfList l 6) (seqOfList l 7)).mp hr
    simp only [hv] at hr'
    exact hr'

/-! ## 7.  The check is primitive recursive, the data is computable -/

/-- **The check is primitive recursive.**  Eleven clauses, each of them an
equality or an order comparison on integers; the implications are turned into
disjunctions, which is what `PrimrecPred` is closed under. -/
theorem primrecPred_traceOK : PrimrecPred traceOK := by
  have hl : Primrec fun x : TraceInput => x.1 := Primrec.fst
  have hs : ∀ k : ℤ, Primrec fun x : TraceInput => evalCode x.1 k := fun k =>
    (primrec_evalCode primrec_intAdd).comp hl (Primrec.const k)
  have hd : Primrec fun x : TraceInput => x.2 := Primrec.snd
  have hd1 : Primrec fun x : TraceInput => x.2.1 := Primrec.fst.comp hd
  have hd2 : Primrec fun x : TraceInput => x.2.2 := Primrec.snd.comp hd
  have hlo : Primrec fun x : TraceInput => x.2.1.1 := Primrec.fst.comp hd1
  have hd1b : Primrec fun x : TraceInput => x.2.1.2 := Primrec.snd.comp hd1
  have hhi : Primrec fun x : TraceInput => x.2.1.2.1 := Primrec.fst.comp hd1b
  have hw : Primrec fun x : TraceInput => x.2.1.2.2 := Primrec.snd.comp hd1b
  have hlo' : Primrec fun x : TraceInput => x.2.2.1 := Primrec.fst.comp hd2
  have hd2b : Primrec fun x : TraceInput => x.2.2.2 := Primrec.snd.comp hd2
  have hhi' : Primrec fun x : TraceInput => x.2.2.2.1 := Primrec.fst.comp hd2b
  have hw' : Primrec fun x : TraceInput => x.2.2.2.2 := Primrec.snd.comp hd2b
  have hwin : PrimrecPred fun x : TraceInput => windowCheck 8 x.1 = true :=
    Primrec.eq.comp ((primrec_windowCheck primrec_intAdd 8).comp hl) (Primrec.const true)
  have c1 : PrimrecPred fun x : TraceInput => (0 : ℤ) ≤ evalCode x.1 2 :=
    primrec_intLe.comp (Primrec.const 0) (hs 2)
  have c2 : PrimrecPred fun x : TraceInput => (0 : ℤ) ≤ evalCode x.1 6 :=
    primrec_intLe.comp (Primrec.const 0) (hs 6)
  have c3 : PrimrecPred fun x : TraceInput =>
      evalCode x.1 3 = (if 1 ≤ evalCode x.1 2 ∧ evalCode x.1 1 = 0 then (1 : ℤ) else 0) :=
    Primrec.eq.comp (hs 3)
      (Primrec.ite
        (PrimrecPred.and (primrec_intLe.comp (Primrec.const 1) (hs 2))
          (Primrec.eq.comp (hs 1) (Primrec.const 0)))
        (Primrec.const 1) (Primrec.const 0))
  have c4 : PrimrecPred fun x : TraceInput =>
      evalCode x.1 7 = (if 1 ≤ evalCode x.1 6 ∧ evalCode x.1 5 = 0 then (1 : ℤ) else 0) :=
    Primrec.eq.comp (hs 7)
      (Primrec.ite
        (PrimrecPred.and (primrec_intLe.comp (Primrec.const 1) (hs 6))
          (Primrec.eq.comp (hs 5) (Primrec.const 0)))
        (Primrec.const 1) (Primrec.const 0))
  have c5 : PrimrecPred fun x : TraceInput =>
      evalCode x.1 2 = 0 → evalCode x.1 0 = 0 ∧ evalCode x.1 1 = 0 :=
    (PrimrecPred.or (PrimrecPred.not (Primrec.eq.comp (hs 2) (Primrec.const 0)))
      (PrimrecPred.and (Primrec.eq.comp (hs 0) (Primrec.const 0))
        (Primrec.eq.comp (hs 1) (Primrec.const 0)))).of_eq fun _ => by tauto
  have c6 : PrimrecPred fun x : TraceInput =>
      evalCode x.1 6 = 0 → evalCode x.1 4 = 0 ∧ evalCode x.1 5 = 0 :=
    (PrimrecPred.or (PrimrecPred.not (Primrec.eq.comp (hs 6) (Primrec.const 0)))
      (PrimrecPred.and (Primrec.eq.comp (hs 4) (Primrec.const 0))
        (Primrec.eq.comp (hs 5) (Primrec.const 0)))).of_eq fun _ => by tauto
  have c7 : PrimrecPred fun x : TraceInput =>
      1 ≤ evalCode x.1 2 →
        x.2.1.1 ≤ evalCode x.1 1 ∧ evalCode x.1 1 ≤ x.2.1.2.1 ∧ evalCode x.1 0 = x.2.1.2.2 :=
    (PrimrecPred.or (PrimrecPred.not (primrec_intLe.comp (Primrec.const 1) (hs 2)))
      (PrimrecPred.and (primrec_intLe.comp hlo (hs 1))
        (PrimrecPred.and (primrec_intLe.comp (hs 1) hhi)
          (Primrec.eq.comp (hs 0) hw)))).of_eq fun _ => by tauto
  have c8 : PrimrecPred fun x : TraceInput =>
      1 ≤ evalCode x.1 6 →
        x.2.2.1 ≤ evalCode x.1 5 ∧ evalCode x.1 5 ≤ x.2.2.2.1 ∧ evalCode x.1 4 = x.2.2.2.2 :=
    (PrimrecPred.or (PrimrecPred.not (primrec_intLe.comp (Primrec.const 1) (hs 6)))
      (PrimrecPred.and (primrec_intLe.comp hlo' (hs 5))
        (PrimrecPred.and (primrec_intLe.comp (hs 5) hhi')
          (Primrec.eq.comp (hs 4) hw')))).of_eq fun _ => by tauto
  have c9 : PrimrecPred fun x : TraceInput =>
      1 ≤ evalCode x.1 2 → 1 ≤ evalCode x.1 6 →
        evalCode x.1 6 = evalCode x.1 2 ∧ evalCode x.1 5 = evalCode x.1 1 + 1 :=
    (PrimrecPred.or (PrimrecPred.not (primrec_intLe.comp (Primrec.const 1) (hs 2)))
      (PrimrecPred.or (PrimrecPred.not (primrec_intLe.comp (Primrec.const 1) (hs 6)))
        (PrimrecPred.and (Primrec.eq.comp (hs 6) (hs 2))
          (Primrec.eq.comp (hs 5)
            (primrec_intAdd.comp (hs 1) (Primrec.const 1)))))).of_eq fun _ => by tauto
  have c10 : PrimrecPred fun x : TraceInput =>
      1 ≤ evalCode x.1 2 → evalCode x.1 6 = 0 → evalCode x.1 1 = x.2.1.2.1 :=
    (PrimrecPred.or (PrimrecPred.not (primrec_intLe.comp (Primrec.const 1) (hs 2)))
      (PrimrecPred.or (PrimrecPred.not (Primrec.eq.comp (hs 6) (Primrec.const 0)))
        (Primrec.eq.comp (hs 1) hhi))).of_eq fun _ => by tauto
  have c11 : PrimrecPred fun x : TraceInput =>
      evalCode x.1 2 = 0 → 1 ≤ evalCode x.1 6 → evalCode x.1 5 = x.2.2.1 :=
    (PrimrecPred.or (PrimrecPred.not (Primrec.eq.comp (hs 2) (Primrec.const 0)))
      (PrimrecPred.or (PrimrecPred.not (primrec_intLe.comp (Primrec.const 1) (hs 6)))
        (Primrec.eq.comp (hs 5) hlo'))).of_eq fun _ => by tauto
  have hrel : PrimrecPred fun x : TraceInput =>
      traceRelOn x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2
        (evalCode x.1 0) (evalCode x.1 1) (evalCode x.1 2) (evalCode x.1 3)
        (evalCode x.1 4) (evalCode x.1 5) (evalCode x.1 6) (evalCode x.1 7) :=
    PrimrecPred.and c1 (PrimrecPred.and c2 (PrimrecPred.and c3 (PrimrecPred.and c4
      (PrimrecPred.and c5 (PrimrecPred.and c6 (PrimrecPred.and c7 (PrimrecPred.and c8
        (PrimrecPred.and c9 (PrimrecPred.and c10 c11)))))))))
  exact PrimrecPred.and hwin hrel

/-- **The window data is computable in the code.**  This is the only place the
enumeration enters, and the only place `Computable` rather than `Primrec` is
needed. -/
theorem computable_traceData (c : ℕ → List (ℤ × ℤ)) (hc : Computable c) :
    Computable (traceData c) := by
  have hev : Primrec₂ evalCode := primrec_evalCode primrec_intAdd
  have hsv : ∀ k : ℤ, Computable fun l : List (ℤ × ℤ) => evalCode l k := fun k =>
    (hev.comp Primrec.id (Primrec.const k)).to_comp
  have hcode : ∀ k : ℤ, Computable fun l : List (ℤ × ℤ) => c (parIdx (evalCode l k)) :=
    fun k => hc.comp ((primrec_parIdx.comp (hev.comp Primrec.id (Primrec.const k))).to_comp)
  have h : Computable fun l : List (ℤ × ℤ) =>
      ((loOf (c (parIdx (evalCode l 2))), hiOf (c (parIdx (evalCode l 2))),
          evalCode (c (parIdx (evalCode l 2))) (evalCode l 1)),
        (loOf (c (parIdx (evalCode l 6))), hiOf (c (parIdx (evalCode l 6))),
          evalCode (c (parIdx (evalCode l 6))) (evalCode l 5))) :=
    Computable.pair
      (Computable.pair (primrec_loOf.to_comp.comp (hcode 2))
        (Computable.pair (primrec_hiOf.to_comp.comp (hcode 2))
          (hev.to_comp.comp (hcode 2) (hsv 1))))
      (Computable.pair (primrec_loOf.to_comp.comp (hcode 6))
        (Computable.pair (primrec_hiOf.to_comp.comp (hcode 6))
          (hev.to_comp.comp (hcode 6) (hsv 5))))
  exact h.of_eq fun _ => rfl

/-- A primitive-recursive predicate composed with a computable map is a
computable predicate.  Pinned Mathlib has `PrimrecPred.comp` for a primitive
recursive map and no `ComputablePred.comp` at all. -/
theorem computablePred_comp_primrecPred {α β : Type} [Primcodable α] [Primcodable β]
    {p : β → Prop} {h : α → β} (hp : PrimrecPred p) (hh : Computable h) :
    ComputablePred fun a => p (h a) := by
  classical
  refine ComputablePred.computable_iff.mpr ⟨fun a => decide (p (h a)), ?_, ?_⟩
  · exact hp.decide.to_comp.comp hh
  · funext a
    simp

/-! ## 8.  The theorem -/

/-- **The transition relation of a trace is recursively enumerable.**  This is
the first of the two obligations left open at the end of
`Higman.EnumeratedRangeTraceCorrectness`.

It is in fact *decidable*: the condition on a code is a finite conjunction of
comparisons between integers computed from the code and from the enumeration,
and recursive enumerability is only what the consumer asks for. -/
theorem reset_blockPairSet_traceRel (c : ℕ → List (ℤ × ℤ)) (hc : Computable c) :
    REset (blockPairSet (traceRel c)) := by
  have hcp : ComputablePred fun l : List (ℤ × ℤ) => traceOK (l, traceData c l) :=
    computablePred_comp_primrecPred primrecPred_traceOK
      (Computable.pair Computable.id (computable_traceData c hc))
  show REPred fun l : List (ℤ × ℤ) => seqOfList l ∈ blockPairSet (traceRel c)
  exact hcp.to_re.of_eq fun l => traceOK_iff c l

/-- **What the trace construction still owes, with the computability half
discharged.**  Only the projection identity is left. -/
theorem higmanGenerated_range_of_projection_of_computable (h : BoundedWindowRE)
    (c : ℕ → List (ℤ × ℤ)) (hc : Computable c)
    (hproj : ∀ f : E,
      (∃ g ∈ traceSet c, ∀ i : ℤ, f i = g (4 * i)) ↔
        f ∈ {g : E | ∃ r : ℕ, seqOfList (c r) = g}) :
    HigmanGenerated {g : E | ∃ r : ℕ, seqOfList (c r) = g} :=
  higmanGenerated_range_of_projection h c (reset_blockPairSet_traceRel c hc) hproj

end Seq
end Higman
end GroupApproximation
