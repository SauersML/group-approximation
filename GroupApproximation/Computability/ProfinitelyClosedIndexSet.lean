import GroupApproximation.Computability.ArithmeticalHierarchy
import GroupApproximation.Computability.SecondLevelIndexSets
import GroupApproximation.Computability.WordProblemRE

/-!
# Profinitely closed r.e. subsets of the integers form a `Π⁰₃`-complete index set

Write `cl(J)` for the closure of `J ⊆ ℤ` in the profinite topology of `ℤ`, so
that `i ∈ cl(J)` exactly when every congruence class `i + nℤ` with `n ≥ 1` meets
`J`.  This file proves that

```text
CLOSED := { c : cl(W_c) = W_c }
```

is `Π⁰₃`-complete under computable many-one reductions, where `W_c ⊆ ℕ ⊆ ℤ` is
the domain of the partial-recursive program with code `c`.

The upper bound is the observation that `cl(W_c) = W_c` says: for every integer
`i`, either `i ∈ W_c` (a `Σ⁰₁` condition) or some modulus `n ≥ 1` separates `i`
from every enumerated element (a `Σ⁰₂` condition).  A universal quantifier over
a `Σ⁰₂` matrix is `Π⁰₃`.

Hardness is the dyadic construction of the research node.  With `D_x` the odd
multiples of `2 ^ x`, the reduction emits

```text
J_e = {0} ∪ ⋃ x, { 2 ^ x * (2 * j + 1) : row x of the instance reaches past j }.
```

The classes `D_x` are pairwise disjoint and clopen in `ℤ̂`, and their only
accumulation point is `0`, which is placed into `J_e` once and for all.  So an
infinite row `x` puts `-2 ^ x` into `cl(J_e) \ J_e`, while all rows finite makes
every `D_x`-trace of `J_e` a finite, hence closed, set.  Composing with the
uniform `Σ⁰₂`-completeness of `FiniteDomain` (`SecondLevelIndexSets`) turns an
arbitrary `Π⁰₃` predicate `∀ x, ∃ y, ∀ z, R` into an instance of `CLOSED`.

Everything below is arithmetic and computability; the group-theoretic
consequence --- that residual finiteness of two-generator recursive
presentations is `Π⁰₃`-complete --- is **not** formalized here.

Research nodes: `index-set-profinitely-closed-is-pi3-complete` (claim),
`index-set-profinitely-closed-pi3-proof` (route),
`residual-finiteness-two-generator-recursive-is-pi3-complete` (the
group-theoretic consequence, not formalized).
-/

namespace GroupApproximation
namespace ProfinitelyClosedIndexSet

open ArithmeticalHierarchy
open SecondLevelIndexSets
open Nat.Partrec

/-! ## The third arithmetical level

`ArithmeticalHierarchy` stops at the second level.  The definitions here mirror
its normal form exactly one level up: a predicate is `Π⁰₃` when it is a
universal family of `Σ⁰₂` predicates. -/

section Level

variable {A : Type*} [Primcodable A]

/-- A predicate is `Π⁰₃` if it is uniformly a universal family of `Σ⁰₂`
predicates. -/
def Pi03 (p : A → Prop) : Prop :=
  ∃ q : A × ℕ → Prop, Sigma02 q ∧ ∀ a, p a ↔ ∀ n, q (a, n)

/-- The third existential level, defined by complementing `Pi03`. -/
def Sigma03 (p : A → Prop) : Prop := Pi03 fun a => ¬ p a

theorem pi03_of_sigma02_family {p : A → Prop} {q : A × ℕ → Prop}
    (hq : Sigma02 q) (h : ∀ a, p a ↔ ∀ n, q (a, n)) : Pi03 p :=
  ⟨q, hq, h⟩

theorem pi03_congr {p r : A → Prop} (h : ∀ a, p a ↔ r a) : Pi03 p ↔ Pi03 r := by
  constructor
  · rintro ⟨q, hq, hp⟩
    exact ⟨q, hq, fun a => (h a).symm.trans (hp a)⟩
  · rintro ⟨q, hq, hr⟩
    exact ⟨q, hq, fun a => (h a).trans (hr a)⟩

end Level

/-- A predicate is `Π⁰₃`-hard on an effective source carrier if every `Π⁰₃`
predicate on that carrier computably many-one reduces to it. -/
def Pi03HardOn (Source : Type*) [Primcodable Source]
    {Target : Type*} [Primcodable Target] (q : Target → Prop) : Prop :=
  ∀ p : Source → Prop, Pi03 p → p ≤₀ q

/-- Standard `Π⁰₃` many-one hardness, with numerical source indices. -/
def Pi03Hard {Target : Type*} [Primcodable Target] (q : Target → Prop) : Prop :=
  Pi03HardOn ℕ q

/-- Membership in `Π⁰₃` together with computable many-one hardness. -/
def Pi03Complete {Target : Type*} [Primcodable Target] (q : Target → Prop) : Prop :=
  Pi03 q ∧ Pi03Hard q

/-! ## Profinite closedness of a set of integers

The profinite topology of `ℤ` has the subgroups `nℤ` as a neighbourhood basis of
`0`, so `i` lies in the closure of `S` exactly when every class `i + nℤ`,
`n ≥ 1`, meets `S`.  Closedness is the converse implication. -/

/-- `i` lies in the profinite closure of `S ⊆ ℤ`. -/
def ProfiniteClosurePoint (S : Set ℤ) (i : ℤ) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ j ∈ S, (n : ℤ) ∣ (i - j)

/-- `S ⊆ ℤ` is closed in the profinite topology. -/
def ProfinitelyClosed (S : Set ℤ) : Prop :=
  ∀ i : ℤ, ProfiniteClosurePoint S i → i ∈ S

/-- The domain of a partial-recursive program code, as a set of naturals. -/
def WSet (c : Code) : Set ℕ := {n | (Code.eval c n).Dom}

theorem wSet_eq_codeDomain (c : Code) : WSet c = codeDomain c := rfl

/-- A set of naturals, read inside the integers. -/
def intImage (S : Set ℕ) : Set ℤ := ((↑) : ℕ → ℤ) '' S

theorem mem_intImage {S : Set ℕ} {i : ℤ} :
    i ∈ intImage S ↔ ∃ k, k ∈ S ∧ (k : ℤ) = i :=
  Iff.rfl

/-- **The index set.**  The r.e. set `W_c`, read inside `ℤ`, is profinitely
closed. -/
def ClosedIndex (c : Code) : Prop := ProfinitelyClosed (intImage (WSet c))

/-! ## Two arithmetic facts about powers of two -/

/-- Every positive natural number is an odd multiple of a power of two. -/
theorem exists_two_pow_mul_odd :
    ∀ a : ℕ, 0 < a → ∃ x k : ℕ, a = 2 ^ x * (2 * k + 1) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha
    rcases Nat.even_or_odd a with he | ho
    · obtain ⟨b, hb⟩ := he
      have hb0 : 0 < b := by omega
      obtain ⟨x, k, hk⟩ := ih b (by omega) hb0
      exact ⟨x + 1, k, by rw [hb, hk]; ring⟩
    · obtain ⟨k, hk⟩ := ho
      exact ⟨0, k, by rw [hk]; ring⟩

/-- Every nonzero integer is an odd multiple of a power of two. -/
theorem exists_two_pow_mul_not_two_dvd {i : ℤ} (hi : i ≠ 0) :
    ∃ (x : ℕ) (v : ℤ), i = 2 ^ x * v ∧ ¬ (2 : ℤ) ∣ v := by
  have ha : 0 < i.natAbs := Int.natAbs_pos.mpr hi
  obtain ⟨x, k, hk⟩ := exists_two_pow_mul_odd i.natAbs ha
  rcases Int.natAbs_eq i with h | h
  · refine ⟨x, 2 * (k : ℤ) + 1, ?_, ?_⟩
    · rw [h, hk]; push_cast; ring
    · rintro ⟨c, hc⟩; omega
  · refine ⟨x, -(2 * (k : ℤ) + 1), ?_, ?_⟩
    · rw [h, hk]; push_cast; ring
    · rintro ⟨c, hc⟩; omega

/-- If two odd multiples of powers of two agree modulo `2 ^ (x + 1)`, where `x`
is the exponent of the first, then the exponents agree.  This is the arithmetic
form of "the dyadic classes `D_x` are disjoint and clopen". -/
theorem two_pow_exponent_eq {x y : ℕ} {v w : ℤ}
    (hv : ¬ (2 : ℤ) ∣ v) (hw : ¬ (2 : ℤ) ∣ w)
    (h : (2 : ℤ) ^ (x + 1) ∣ ((2 : ℤ) ^ x * v - (2 : ℤ) ^ y * w)) : x = y := by
  by_contra hne
  rcases Nat.lt_or_ge x y with hxy | hxy
  · obtain ⟨d, hd⟩ : ∃ d, y = x + 1 + d := ⟨y - (x + 1), by omega⟩
    have hfac : (2 : ℤ) ^ x * v - (2 : ℤ) ^ y * w
        = (2 : ℤ) ^ x * (v - 2 * (2 : ℤ) ^ d * w) := by
      rw [hd]; ring
    have hpow : (2 : ℤ) ^ (x + 1) = (2 : ℤ) ^ x * 2 := by ring
    rw [hfac, hpow] at h
    have hne0 : ((2 : ℤ) ^ x) ≠ 0 := by positivity
    obtain ⟨cc, hcc⟩ := (mul_dvd_mul_iff_left hne0).mp h
    exact hv ⟨cc + (2 : ℤ) ^ d * w, by linear_combination hcc⟩
  · have hyx : y < x := lt_of_le_of_ne hxy fun hh => hne hh.symm
    obtain ⟨d, hd⟩ : ∃ d, x = y + 1 + d := ⟨x - (y + 1), by omega⟩
    have hle : (2 : ℤ) ^ (y + 1) ∣ (2 : ℤ) ^ (x + 1) := pow_dvd_pow 2 (by omega)
    have h' : (2 : ℤ) ^ (y + 1) ∣ ((2 : ℤ) ^ x * v - (2 : ℤ) ^ y * w) := hle.trans h
    have hfac : (2 : ℤ) ^ x * v - (2 : ℤ) ^ y * w
        = (2 : ℤ) ^ y * (2 * (2 : ℤ) ^ d * v - w) := by
      rw [hd]; ring
    have hpow : (2 : ℤ) ^ (y + 1) = (2 : ℤ) ^ y * 2 := by ring
    rw [hfac, hpow] at h'
    have hne0 : ((2 : ℤ) ^ y) ≠ 0 := by positivity
    obtain ⟨cc, hcc⟩ := (mul_dvd_mul_iff_left hne0).mp h'
    exact hw ⟨(2 : ℤ) ^ d * v - cc, by linear_combination -hcc⟩

/-- The comparison that turns "the witness is inside the window" into an
equality of integers.  Stated over abstract bounds so that `omega` sees only
linear data. -/
theorem abs_sub_lt_of_bounds {i : ℤ} {k bnd N : ℕ}
    (hk : k ≤ bnd) (hN : i.natAbs + bnd + 1 ≤ N) : |i - (k : ℤ)| < (N : ℤ) := by
  rw [abs_lt]
  omega

/-! ## Compiling an r.e. set of naturals into a program code

`SecondLevelIndexSets` performs this compilation for one specific predicate and
keeps the pieces private.  The general statement is recorded here: a uniformly
r.e. family of subsets of `ℕ` is the family of domains of a computable family of
codes.  The proof is the standard `s-m-n` argument through `Code.curry`. -/

section Compiler

variable {A : Type*} [Primcodable A]

private theorem assert_dom_iff (r : Prop) :
    (Part.assert r fun _ => Part.some ()).Dom ↔ r := by
  change (∃ _ : r, True) ↔ r
  simp

private def domainRun (M : A × ℕ → Prop) (a : A) (m : ℕ) : Part Unit :=
  Part.assert (M (a, m)) fun _ => Part.some ()

private theorem domainRun_partrec₂ {M : A × ℕ → Prop} (hM : REPred M) :
    Partrec₂ (domainRun M) := by
  change Partrec fun z : A × ℕ => domainRun M z.1 z.2
  exact Partrec.of_eq hM fun z => by cases z; rfl

private def encodedDomainRun (M : A × ℕ → Prop) (input : ℕ) : Part ℕ :=
  Part.bind (↑(Encodable.decode₂ (A × ℕ) input) : Part (A × ℕ)) fun z =>
    (domainRun M z.1 z.2).map Encodable.encode

private theorem encodedDomainRun_partrec {M : A × ℕ → Prop} (hM : REPred M) :
    Nat.Partrec (encodedDomainRun M) :=
  (Partrec.bind_decode₂_iff.mp (domainRun_partrec₂ hM)).of_eq fun _ => rfl

private noncomputable def domainRunnerCode (M : A × ℕ → Prop) (hM : REPred M) : Code :=
  (Code.exists_code.mp (encodedDomainRun_partrec hM)).choose

private theorem eval_domainRunnerCode (M : A × ℕ → Prop) (hM : REPred M) :
    Code.eval (domainRunnerCode M hM) = encodedDomainRun M :=
  (Code.exists_code.mp (encodedDomainRun_partrec hM)).choose_spec

/-- The code compiled from a uniformly r.e. family at the instance `a`. -/
noncomputable def domainCode (M : A × ℕ → Prop) (hM : REPred M) (a : A) : Code :=
  Code.curry (domainRunnerCode M hM) (Encodable.encode a)

theorem computable_domainCode (M : A × ℕ → Prop) (hM : REPred M) :
    Computable (domainCode M hM) :=
  (Code.primrec₂_curry.comp (Primrec.const (domainRunnerCode M hM))
    Primrec.encode).to_comp

theorem eval_domainCode_dom_iff (M : A × ℕ → Prop) (hM : REPred M) (a : A) (m : ℕ) :
    (Code.eval (domainCode M hM a) m).Dom ↔ M (a, m) := by
  rw [domainCode, Code.eval_curry, eval_domainRunnerCode]
  change (Part.bind
    (↑(Encodable.decode₂ (A × ℕ) (Nat.pair (Encodable.encode a) m)) : Part (A × ℕ))
    fun z : A × ℕ => Part.map Encodable.encode (domainRun M z.1 z.2)).Dom ↔ _
  have hpair : Nat.pair (Encodable.encode a) m = Encodable.encode (a, m) := by
    rw [Encodable.encode_prod_val, Encodable.encode_nat]
  rw [hpair, Encodable.decode₂_encode, Part.coe_some, Part.bind_some]
  change (domainRun M a m).Dom ↔ _
  exact assert_dom_iff _

/-- **A uniformly r.e. family of sets of naturals is a computable family of
program domains.** -/
theorem exists_code_of_rePred {M : A × ℕ → Prop} (hM : REPred M) :
    ∃ f : A → Code, Computable f ∧ ∀ a m, (Code.eval (f a) m).Dom ↔ M (a, m) :=
  ⟨domainCode M hM, computable_domainCode M hM, eval_domainCode_dom_iff M hM⟩

end Compiler

/-! ## The upper bound

Reading `ℤ` through a computable surjection from `ℕ` turns the universal
quantifier over integers into a universal quantifier over indices, and the
matrix "either the integer is enumerated or some modulus separates it" is
`Σ⁰₂`.  Every congruence test is carried out in `ℕ`: nothing below asks for
`Primrec` facts about integer arithmetic, of which pinned Mathlib has none. -/

/-- A computable surjection `ℕ → ℤ`: even indices name the naturals, odd
indices the strictly negative integers. -/
def intOfIndex (n : ℕ) : ℤ :=
  if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n / 2 : ℕ) : ℤ) + 1)

theorem intOfIndex_even {n : ℕ} (h : n % 2 = 0) : intOfIndex n = ((n / 2 : ℕ) : ℤ) :=
  if_pos h

theorem intOfIndex_odd {n : ℕ} (h : ¬ n % 2 = 0) :
    intOfIndex n = -(((n / 2 : ℕ) : ℤ) + 1) :=
  if_neg h

theorem intOfIndex_neg_of_odd {n : ℕ} (h : ¬ n % 2 = 0) : intOfIndex n < 0 := by
  rw [intOfIndex_odd h]; omega

theorem intOfIndex_surjective (i : ℤ) : ∃ n : ℕ, intOfIndex n = i := by
  by_cases h : 0 ≤ i
  · refine ⟨2 * i.natAbs, ?_⟩
    have h1 : 2 * i.natAbs % 2 = 0 := by omega
    have h2 : 2 * i.natAbs / 2 = i.natAbs := by omega
    rw [intOfIndex_even h1, h2]
    omega
  · refine ⟨2 * (-i - 1).natAbs + 1, ?_⟩
    have h1 : ¬ (2 * (-i - 1).natAbs + 1) % 2 = 0 := by omega
    have h2 : (2 * (-i - 1).natAbs + 1) / 2 = (-i - 1).natAbs := by omega
    rw [intOfIndex_odd h1, h2]
    omega

/-- The congruence test: index `n` names an integer, `m` is the modulus and `k`
a natural member of the set.  Both branches are natural-number arithmetic. -/
def congrTest (n m k : ℕ) : Bool :=
  if n % 2 = 0 then decide (n / 2 % m = k % m) else decide ((n / 2 + 1 + k) % m = 0)

theorem congrTest_iff (n m k : ℕ) :
    congrTest n m k = true ↔ (m : ℤ) ∣ (intOfIndex n - (k : ℤ)) := by
  by_cases h : n % 2 = 0
  · have hdef : congrTest n m k = decide (n / 2 % m = k % m) := if_pos h
    rw [hdef, decide_eq_true_eq, intOfIndex_even h]
    have h1 : (n / 2 % m = k % m) ↔ (m : ℤ) ∣ ((k : ℤ) - ((n / 2 : ℕ) : ℤ)) :=
      Nat.modEq_iff_dvd (n := m) (a := n / 2) (b := k)
    rw [h1]
    exact dvd_sub_comm
  · have hdef : congrTest n m k = decide ((n / 2 + 1 + k) % m = 0) := if_neg h
    rw [hdef, decide_eq_true_eq, intOfIndex_odd h]
    have hneg : -(((n / 2 : ℕ) : ℤ) + 1) - (k : ℤ) = -(((n / 2 + 1 + k : ℕ) : ℤ)) := by
      push_cast; ring
    rw [hneg, dvd_neg, Int.natCast_dvd_natCast]
    exact Nat.dvd_iff_mod_eq_zero.symm

theorem primrec_congrTest : Primrec fun z : ℕ × ℕ × ℕ => congrTest z.1 z.2.1 z.2.2 := by
  have hn : Primrec fun z : ℕ × ℕ × ℕ => z.1 := Primrec.fst
  have hm : Primrec fun z : ℕ × ℕ × ℕ => z.2.1 := Primrec.fst.comp Primrec.snd
  have hk : Primrec fun z : ℕ × ℕ × ℕ => z.2.2 := Primrec.snd.comp Primrec.snd
  have hhalf : Primrec fun z : ℕ × ℕ × ℕ => z.1 / 2 :=
    Primrec.nat_div.comp hn (Primrec.const 2)
  have hcond : PrimrecPred fun z : ℕ × ℕ × ℕ => z.1 % 2 = 0 :=
    Primrec.eq.comp (Primrec.nat_mod.comp hn (Primrec.const 2)) (Primrec.const 0)
  have hthen : Primrec fun z : ℕ × ℕ × ℕ => decide (z.1 / 2 % z.2.1 = z.2.2 % z.2.1) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp hhalf hm)
      (Primrec.nat_mod.comp hk hm)).decide
  have helse : Primrec fun z : ℕ × ℕ × ℕ => decide ((z.1 / 2 + 1 + z.2.2) % z.2.1 = 0) :=
    (Primrec.eq.comp
      (Primrec.nat_mod.comp
        (Primrec.nat_add.comp (Primrec.nat_add.comp hhalf (Primrec.const 1)) hk) hm)
      (Primrec.const 0)).decide
  exact Primrec.of_eq (Primrec.ite hcond hthen helse) fun _ => rfl

/-- The matrix of the upper bound: at index `n`, either the named integer is
enumerated, or some positive modulus separates it from the whole set. -/
def ClosedAtIndex (c : Code) (n : ℕ) : Prop :=
  (n % 2 = 0 ∧ (n / 2) ∈ WSet c) ∨ ∃ m, 0 < m ∧ ∀ k ∈ WSet c, congrTest n m k = false

theorem closedIndex_iff_forall_index (c : Code) :
    ClosedIndex c ↔ ∀ n, ClosedAtIndex c n := by
  classical
  constructor
  · intro hclosed n
    by_cases hcp : ProfiniteClosurePoint (intImage (WSet c)) (intOfIndex n)
    · obtain ⟨k, hk, hkeq⟩ := hclosed _ hcp
      have heven : n % 2 = 0 := by
        by_contra hodd
        have hneg : intOfIndex n < 0 := intOfIndex_neg_of_odd hodd
        rw [← hkeq] at hneg
        omega
      refine Or.inl ⟨heven, ?_⟩
      have hcast : ((n / 2 : ℕ) : ℤ) = (k : ℤ) := by rw [← intOfIndex_even heven, ← hkeq]
      have hnk : n / 2 = k := by exact_mod_cast hcast
      rw [hnk]
      exact hk
    · right
      have hcp' : ¬ ∀ m : ℕ, 0 < m →
          ∃ j ∈ intImage (WSet c), (m : ℤ) ∣ (intOfIndex n - j) := hcp
      push Not at hcp'
      obtain ⟨m, hm, hmall⟩ := hcp'
      refine ⟨m, hm, fun k hk => ?_⟩
      have hnot : ¬ ((m : ℤ) ∣ (intOfIndex n - (k : ℤ))) :=
        hmall (k : ℤ) (mem_intImage.mpr ⟨k, hk, rfl⟩)
      rw [← congrTest_iff n m k] at hnot
      simpa using hnot
  · intro hall i hi
    obtain ⟨n, rfl⟩ := intOfIndex_surjective i
    rcases hall n with ⟨heven, hmem⟩ | ⟨m, hm, hmall⟩
    · exact mem_intImage.mpr ⟨n / 2, hmem, (intOfIndex_even heven).symm⟩
    · exfalso
      obtain ⟨j, hj, hdvd⟩ := hi m hm
      obtain ⟨k, hk, rfl⟩ := mem_intImage.mp hj
      have hfalse := hmall k hk
      rw [← congrTest_iff n m k] at hdvd
      rw [hdvd] at hfalse
      simp at hfalse

/-- The search matrix refuting `ClosedAtIndex` at stage `t`. -/
def refuteCheck (zt : (Code × ℕ) × ℕ) (w : ℕ × ℕ) : Bool :=
  decide ((¬ (zt.1.2 % 2 = 0 ∧ (Code.evaln zt.2 zt.1.1 (zt.1.2 / 2)).isSome = true)) ∧
    (zt.2 = 0 ∨ ((Code.evaln w.2 zt.1.1 w.1).isSome = true ∧
      congrTest zt.1.2 zt.2 w.1 = true)))

theorem refuteCheck_eq_true_iff (z : Code × ℕ) (t : ℕ) (w : ℕ × ℕ) :
    refuteCheck (z, t) w = true ↔
      (¬ (z.2 % 2 = 0 ∧ (Code.evaln t z.1 (z.2 / 2)).isSome = true)) ∧
        (t = 0 ∨ ((Code.evaln w.2 z.1 w.1).isSome = true ∧
          congrTest z.2 t w.1 = true)) := by
  simp only [refuteCheck, decide_eq_true_eq]

theorem primrec₂_refuteCheck : Primrec₂ refuteCheck := by
  have hc : Primrec fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) => z.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ht : Primrec fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hk : Primrec fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hs : Primrec fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) => z.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hev1 : Primrec fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) =>
      (Code.evaln z.1.2 z.1.1.1 (z.1.1.2 / 2)).isSome :=
    Primrec.option_isSome.comp
      (Code.primrec_evaln.comp
        (Primrec.pair (Primrec.pair ht hc)
          (Primrec.nat_div.comp hn (Primrec.const 2))))
  have hev2 : Primrec fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) =>
      (Code.evaln z.2.2 z.1.1.1 z.2.1).isSome :=
    Primrec.option_isSome.comp
      (Code.primrec_evaln.comp (Primrec.pair (Primrec.pair hs hc) hk))
  have hcg : Primrec fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) =>
      congrTest z.1.1.2 z.1.2 z.2.1 :=
    primrec_congrTest.comp (Primrec.pair hn (Primrec.pair ht hk))
  have hP1 : PrimrecPred fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) => z.1.1.2 % 2 = 0 :=
    Primrec.eq.comp (Primrec.nat_mod.comp hn (Primrec.const 2)) (Primrec.const 0)
  have hP2 : PrimrecPred fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) =>
      (Code.evaln z.1.2 z.1.1.1 (z.1.1.2 / 2)).isSome = true :=
    Primrec.eq.comp hev1 (Primrec.const true)
  have hQ1 : PrimrecPred fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) => z.1.2 = 0 :=
    Primrec.eq.comp ht (Primrec.const 0)
  have hQ2 : PrimrecPred fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) =>
      (Code.evaln z.2.2 z.1.1.1 z.2.1).isSome = true :=
    Primrec.eq.comp hev2 (Primrec.const true)
  have hQ3 : PrimrecPred fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) =>
      congrTest z.1.1.2 z.1.2 z.2.1 = true :=
    Primrec.eq.comp hcg (Primrec.const true)
  have hall : PrimrecPred fun z : ((Code × ℕ) × ℕ) × (ℕ × ℕ) =>
      (¬ (z.1.1.2 % 2 = 0 ∧ (Code.evaln z.1.2 z.1.1.1 (z.1.1.2 / 2)).isSome = true)) ∧
        (z.1.2 = 0 ∨ ((Code.evaln z.2.2 z.1.1.1 z.2.1).isSome = true ∧
          congrTest z.1.1.2 z.1.2 z.2.1 = true)) :=
    PrimrecPred.and (PrimrecPred.not (PrimrecPred.and hP1 hP2))
      (PrimrecPred.or hQ1 (PrimrecPred.and hQ2 hQ3))
  exact Primrec.of_eq hall.decide fun _ => rfl

theorem not_closedAtIndex_iff (z : Code × ℕ) :
    ¬ ClosedAtIndex z.1 z.2 ↔ ∀ t : ℕ, ∃ w : ℕ × ℕ, refuteCheck (z, t) w = true := by
  classical
  constructor
  · intro hnot t
    have hleft : ¬ (z.2 % 2 = 0 ∧ (Code.evaln t z.1 (z.2 / 2)).isSome = true) := by
      rintro ⟨heven, hsome⟩
      exact hnot (Or.inl ⟨heven,
        (eval_dom_iff_exists_evaln_isSome z.1 (z.2 / 2)).2 ⟨t, hsome⟩⟩)
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · exact ⟨(0, 0), (refuteCheck_eq_true_iff z t (0, 0)).2 ⟨hleft, Or.inl ht0⟩⟩
    · have hex : ∃ k ∈ WSet z.1, congrTest z.2 t k = true := by
        by_contra hno
        push Not at hno
        exact hnot (Or.inr ⟨t, htpos, fun k hk => by simpa using hno k hk⟩)
      obtain ⟨k, hk, hck⟩ := hex
      obtain ⟨s, hs⟩ := (eval_dom_iff_exists_evaln_isSome z.1 k).1 hk
      exact ⟨(k, s), (refuteCheck_eq_true_iff z t (k, s)).2 ⟨hleft, Or.inr ⟨hs, hck⟩⟩⟩
  · intro hall hclosed
    rcases hclosed with ⟨heven, hmem⟩ | ⟨m, hm, hmall⟩
    · obtain ⟨t, ht⟩ := (eval_dom_iff_exists_evaln_isSome z.1 (z.2 / 2)).1 hmem
      obtain ⟨w, hw⟩ := hall t
      exact ((refuteCheck_eq_true_iff z t w).1 hw).1 ⟨heven, ht⟩
    · obtain ⟨w, hw⟩ := hall m
      rcases ((refuteCheck_eq_true_iff z m w).1 hw).2 with h0 | ⟨hsome, hck⟩
      · omega
      · have hk : w.1 ∈ WSet z.1 :=
          (eval_dom_iff_exists_evaln_isSome z.1 w.1).2 ⟨w.2, hsome⟩
        have := hmall w.1 hk
        rw [hck] at this
        simp at this

/-- **The upper bound.**  Profinite closedness of an r.e. subset of `ℤ` is
`Π⁰₃`. -/
theorem pi03_closedIndex : Pi03 ClosedIndex := by
  refine ⟨fun z : Code × ℕ => ClosedAtIndex z.1 z.2, ?_,
    fun c => closedIndex_iff_forall_index c⟩
  refine ⟨fun zt : (Code × ℕ) × ℕ => ∃ w : ℕ × ℕ, refuteCheck zt w = true,
    WordProblemRE.rePred_exists_eq_true primrec₂_refuteCheck.to_comp, ?_⟩
  intro z
  exact not_closedAtIndex_iff z

/-! ## Hardness

The row predicate below is not "the row has at least `j + 1` elements" but the
equivalent-for-our-purposes "the row reaches past `j`".  That is already the
uniformly r.e. predicate `rePred_hasDomainAbove` of `SecondLevelIndexSets`, it
holds for every `j` when the row is infinite, and it is bounded when the row is
finite --- the only two facts the dyadic argument uses. -/

/-- Row `j` fires when the program's domain reaches past `j`. -/
def Row (c : Code) (j : ℕ) : Prop := ∃ n, j < n ∧ (Code.eval c n).Dom

theorem row_of_infiniteDomain {c : Code} (h : InfiniteDomain c) (j : ℕ) : Row c j := by
  obtain ⟨n, hn, hjn⟩ := (Set.infinite_iff_exists_gt (s := codeDomain c)).1 h j
  exact ⟨n, hjn, hn⟩

theorem exists_bound_of_finiteDomain {c : Code} (h : FiniteDomain c) :
    ∃ B : ℕ, ∀ j, Row c j → j < B := by
  have hni : ¬ (codeDomain c).Infinite := Set.not_infinite.2 h
  rw [Set.infinite_iff_exists_gt] at hni
  push Not at hni
  obtain ⟨B, hB⟩ := hni
  refine ⟨B + 1, fun j hj => ?_⟩
  obtain ⟨n, hjn, hn⟩ := hj
  have hnB : n ≤ B := hB n hn
  omega

/-- The dyadic hardness set: `0`, together with row `x` inside the odd multiples
of `2 ^ x`. -/
def dyadicSet (g : ℕ × ℕ → Code) (e : ℕ) : Set ℕ :=
  {m | m = 0 ∨ ∃ x j : ℕ, m = 2 ^ x * (2 * j + 1) ∧ Row (g (e, x)) j}

theorem mem_dyadicSet_iff (g : ℕ × ℕ → Code) (e m : ℕ) :
    m ∈ dyadicSet g e ↔ m = 0 ∨ ∃ x j : ℕ, m = 2 ^ x * (2 * j + 1) ∧ Row (g (e, x)) j :=
  Iff.rfl

theorem zero_mem_dyadicSet (g : ℕ × ℕ → Code) (e : ℕ) : 0 ∈ dyadicSet g e := Or.inl rfl

/-- The step-indexed halting test, with the code as its own argument.  Keeping
the code separate is what lets the reduction's computable code family enter
through `Computable₂.comp`, whose intermediate types are `Code` and a tuple of
naturals; routing it instead through the mixed intermediate `(ℕ × Code) × ℕ` of
`Code.primrec_evaln` makes the elaborator's `whnf` diverge. -/
def evalnBool (c : Code) (u : ℕ × ℕ) : Bool := (Code.evaln u.2 c u.1).isSome

theorem primrec₂_evalnBool : Primrec₂ evalnBool := by
  have hc : Primrec fun z : Code × (ℕ × ℕ) => z.1 := Primrec.fst
  have hn : Primrec fun z : Code × (ℕ × ℕ) => z.2.1 := Primrec.fst.comp Primrec.snd
  have hs : Primrec fun z : Code × (ℕ × ℕ) => z.2.2 := Primrec.snd.comp Primrec.snd
  exact Primrec.of_eq
    (Primrec.option_isSome.comp
      (Code.primrec_evaln.comp (Primrec.pair (Primrec.pair hs hc) hn))) fun _ => rfl

/-- The search matrix enumerating the dyadic set. -/
def dyadicCheck (g : ℕ × ℕ → Code) (em : ℕ × ℕ) (w : ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (em.2 = 0) ||
    (decide (em.2 = 2 ^ w.1 * (2 * w.2.1 + 1)) && decide (w.2.1 < w.2.2.1) &&
      evalnBool (g (em.1, w.1)) (w.2.2.1, w.2.2.2))

theorem dyadicCheck_eq_true_iff (g : ℕ × ℕ → Code) (em : ℕ × ℕ)
    (w : ℕ × ℕ × ℕ × ℕ) :
    dyadicCheck g em w = true ↔
      em.2 = 0 ∨ ((em.2 = 2 ^ w.1 * (2 * w.2.1 + 1) ∧ w.2.1 < w.2.2.1) ∧
        (Code.evaln w.2.2.2 (g (em.1, w.1)) w.2.2.1).isSome = true) := by
  simp only [dyadicCheck, evalnBool, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem exists_dyadicCheck_iff (g : ℕ × ℕ → Code) (em : ℕ × ℕ) :
    (∃ w : ℕ × ℕ × ℕ × ℕ, dyadicCheck g em w = true) ↔ em.2 ∈ dyadicSet g em.1 := by
  constructor
  · rintro ⟨w, hw⟩
    rcases (dyadicCheck_eq_true_iff g em w).1 hw with h0 | ⟨⟨hval, hjn⟩, hsome⟩
    · exact Or.inl h0
    · exact Or.inr ⟨w.1, w.2.1, hval, w.2.2.1, hjn,
        (eval_dom_iff_exists_evaln_isSome _ w.2.2.1).2 ⟨w.2.2.2, hsome⟩⟩
  · rintro (h0 | ⟨x, j, hval, n, hjn, hdom⟩)
    · exact ⟨(0, 0, 0, 0), (dyadicCheck_eq_true_iff g em (0, 0, 0, 0)).2 (Or.inl h0)⟩
    · obtain ⟨s, hs⟩ := (eval_dom_iff_exists_evaln_isSome _ n).1 hdom
      exact ⟨(x, j, n, s),
        (dyadicCheck_eq_true_iff g em (x, j, n, s)).2 (Or.inr ⟨⟨hval, hjn⟩, hs⟩)⟩

theorem primrec₂_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem computable_dyadicCheck {g : ℕ × ℕ → Code} (hg : Computable g) :
    Computable₂ (dyadicCheck g) := by
  have hm : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hx : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hj : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) => z.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) => z.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hs : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) => z.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have he : Computable fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) => z.1.1 :=
    Computable.fst.comp Computable.fst
  have hzero : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) => decide (z.1.2 = 0) :=
    (Primrec.eq.comp hm (Primrec.const 0)).decide
  have hpow : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) => 2 ^ z.2.1 :=
    primrec₂_natPow.comp (Primrec.const 2) hx
  have hodd : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) => 2 * z.2.2.1 + 1 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hj) (Primrec.const 1)
  have hval : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) =>
      2 ^ z.2.1 * (2 * z.2.2.1 + 1) := Primrec.nat_mul.comp hpow hodd
  have hshape : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) =>
      decide (z.1.2 = 2 ^ z.2.1 * (2 * z.2.2.1 + 1)) :=
    (Primrec.eq.comp hm hval).decide
  have hlt : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) =>
      decide (z.2.2.1 < z.2.2.2.1) :=
    (Primrec.nat_lt.comp hj hn).decide
  have hcond : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) =>
      decide (z.1.2 = 2 ^ z.2.1 * (2 * z.2.2.1 + 1)) && decide (z.2.2.1 < z.2.2.2.1) :=
    Primrec.and.comp hshape hlt
  have hev : Computable fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) =>
      evalnBool (g (z.1.1, z.2.1)) (z.2.2.2.1, z.2.2.2.2) :=
    primrec₂_evalnBool.to_comp.comp (hg.comp (Computable.pair he hx.to_comp))
      (Computable.pair hn.to_comp hs.to_comp)
  have hbody : Computable fun z : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) =>
      decide (z.1.2 = 0) ||
        (decide (z.1.2 = 2 ^ z.2.1 * (2 * z.2.2.1 + 1)) &&
            decide (z.2.2.1 < z.2.2.2.1) &&
          evalnBool (g (z.1.1, z.2.1)) (z.2.2.2.1, z.2.2.2.2)) :=
    Primrec.or.to_comp.comp hzero.to_comp
      (Primrec.and.to_comp.comp hcond.to_comp hev)
  exact hbody.of_eq fun _ => rfl

/-! ### The two halves of the dyadic argument -/

/-- An infinite row puts `-2 ^ x` into the closure but not into the set. -/
theorem not_closedIndex_of_infinite {g : ℕ × ℕ → Code} {e : ℕ} {c : Code}
    (hc : ∀ m, m ∈ WSet c ↔ m ∈ dyadicSet g e) {x : ℕ}
    (hx : ¬ FiniteDomain (g (e, x))) : ¬ ClosedIndex c := by
  intro hclosed
  have hinf : InfiniteDomain (g (e, x)) := hx
  have hcp : ProfiniteClosurePoint (intImage (WSet c)) (-((2 : ℤ) ^ x)) := by
    intro n hn
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
    refine ⟨((2 ^ x * (2 * t + 1) : ℕ) : ℤ), mem_intImage.mpr
      ⟨2 ^ x * (2 * t + 1), (hc _).2 (Or.inr ⟨x, t, rfl,
        row_of_infiniteDomain hinf t⟩), rfl⟩, ?_⟩
    refine ⟨-((2 : ℤ) ^ x * 2), ?_⟩
    push_cast
    ring
  obtain ⟨k, _, hkeq⟩ := hclosed _ hcp
  have hnn : (0 : ℤ) ≤ (k : ℤ) := by positivity
  rw [hkeq] at hnn
  have hpos : (0 : ℤ) < (2 : ℤ) ^ x := by positivity
  linarith

/-- All rows finite makes the dyadic set profinitely closed. -/
theorem closedIndex_of_forall_finite {g : ℕ × ℕ → Code} {e : ℕ} {c : Code}
    (hc : ∀ m, m ∈ WSet c ↔ m ∈ dyadicSet g e)
    (hfin : ∀ x, FiniteDomain (g (e, x))) : ClosedIndex c := by
  intro i hi
  rcases eq_or_ne i 0 with rfl | hi0
  · exact mem_intImage.mpr ⟨0, (hc 0).2 (zero_mem_dyadicSet g e), by norm_num⟩
  obtain ⟨x, v, hiv, hv⟩ := exists_two_pow_mul_not_two_dvd hi0
  obtain ⟨B, hB⟩ := exists_bound_of_finiteDomain (hfin x)
  have hNpos : 0 < 2 ^ (x + 1) * (i.natAbs + 2 ^ x * (2 * B + 1) + 1) := by positivity
  obtain ⟨jj, hjj, hdvd⟩ := hi _ hNpos
  obtain ⟨k, hk, rfl⟩ := mem_intImage.mp hjj
  have hdvd2 : ((2 : ℤ) ^ (x + 1)) ∣ (i - (k : ℤ)) := by
    refine dvd_trans ?_ hdvd
    refine ⟨((i.natAbs + 2 ^ x * (2 * B + 1) + 1 : ℕ) : ℤ), ?_⟩
    push_cast
    ring
  rcases (hc k).1 hk with hk0 | ⟨y, j, hkyj, hrow⟩
  · exfalso
    subst hk0
    rw [Nat.cast_zero, sub_zero, hiv, pow_succ] at hdvd2
    have hne0 : ((2 : ℤ) ^ x) ≠ 0 := by positivity
    exact hv ((mul_dvd_mul_iff_left hne0).mp hdvd2)
  · have hkz : (k : ℤ) = (2 : ℤ) ^ y * (2 * (j : ℤ) + 1) := by
      rw [hkyj]; push_cast; ring
    have hwodd : ¬ (2 : ℤ) ∣ (2 * (j : ℤ) + 1) := by
      rintro ⟨cc, hcc⟩; omega
    have hxy : x = y := by
      have h' : ((2 : ℤ) ^ (x + 1)) ∣ ((2 : ℤ) ^ x * v - (2 : ℤ) ^ y * (2 * (j : ℤ) + 1)) := by
        rw [← hiv, ← hkz]; exact hdvd2
      exact two_pow_exponent_eq hv hwodd h'
    rw [← hxy] at hrow hkyj
    have hjB : j < B := hB j hrow
    have hkle : k ≤ 2 ^ x * (2 * B + 1) := by
      rw [hkyj]
      exact Nat.mul_le_mul (Nat.le_refl _) (by omega)
    have hMle : i.natAbs + 2 ^ x * (2 * B + 1) + 1
        ≤ 2 ^ (x + 1) * (i.natAbs + 2 ^ x * (2 * B + 1) + 1) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    have hzero : i - (k : ℤ) = 0 :=
      Int.eq_zero_of_abs_lt_dvd hdvd (abs_sub_lt_of_bounds hkle hMle)
    exact mem_intImage.mpr ⟨k, hk, by omega⟩

/-- **Hardness.**  Every `Π⁰₃` predicate on `ℕ` computably many-one reduces to
profinite closedness of an r.e. subset of `ℤ`. -/
theorem pi03Hard_closedIndex : Pi03Hard ClosedIndex := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hp
  obtain ⟨g, hgcomp, hgcorrect⟩ :=
    pi02_manyOne_infiniteDomain (p := fun z : ℕ × ℕ => ¬ q z) hq
  have hgfin : ∀ z : ℕ × ℕ, q z ↔ FiniteDomain (g z) := by
    intro z
    classical
    have h := not_congr (hgcorrect z)
    simpa only [not_not, FiniteDomain, InfiniteDomain, Set.Infinite] using h
  have hre : REPred fun z : ℕ × ℕ => z.2 ∈ dyadicSet g z.1 :=
    (WordProblemRE.rePred_exists_eq_true (computable_dyadicCheck hgcomp)).of_eq
      fun z => exists_dyadicCheck_iff g z
  obtain ⟨f, hfcomp, hf⟩ := exists_code_of_rePred hre
  refine ⟨f, hfcomp, fun e => ?_⟩
  have hc : ∀ m, m ∈ WSet (f e) ↔ m ∈ dyadicSet g e := fun m => hf e m
  rw [hpq e]
  constructor
  · intro hall
    exact closedIndex_of_forall_finite hc fun x => (hgfin (e, x)).1 (hall x)
  · intro hclosed x
    by_contra hxq
    exact not_closedIndex_of_infinite hc
      (fun hfin => hxq ((hgfin (e, x)).2 hfin)) hclosed

/-- **The classification.**  The r.e. subsets of `ℤ` that are closed in the
profinite topology form a `Π⁰₃`-complete index set. -/
theorem pi03Complete_closedIndex : Pi03Complete ClosedIndex :=
  ⟨pi03_closedIndex, pi03Hard_closedIndex⟩

end ProfinitelyClosedIndexSet
end GroupApproximation
