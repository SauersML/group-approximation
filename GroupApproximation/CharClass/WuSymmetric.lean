import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The half-antidiagonal identity for elementary symmetric functions

This file proves, over any commutative ring in which `2 = 0`, the single
combinatorial identity that carries the diagonal Wu relation for mod-2 Chern
classes:

```text
∑_{j ≤ i} e_{i-j} · e_{i+1+j}  =  ∑_{|B| = i} ∑_{k ∉ B} (∏_{l ∈ B} y_l²) · y_k .
```

The right-hand side is exactly what the total Steenrod square
`Sq(y) = y + y²` produces from the squarefree monomials of `e_{i+1}` (see
`GroupApproximation/CharClass/WuDiagonal.lean`), so the identity converts the
Cartan/splitting computation of `Sq^{2i} γ_{i+1}` into the product
`∑_{j} γ_{i-j} γ_{i+1+j}`.

## The proof

The design source suggests a generating-function proof: expand
`∏_k (1 + y_k T)² = ∏_k (1 + 2 y_k T + y_k² T²)` over `ℤ`, observe that the
coefficient of `T^{2i+1}` is even, halve it, and reduce mod two.  We do **not**
follow that route.  Halving inside `ℤ[y]` forces a coefficient extraction from a
`Finset` product of three-term factors and a division step, both expensive.

Instead we run an induction on the *index set*.  Writing `E s a` for the `a`-th
elementary symmetric function of `y` over `s` and

```text
P s i = ∑_{q ≤ i} E s q · E s (2i+1-q),      Q s i = ∑_{|B| = i} ∑_{k ∈ s \ B} y_B² y_k,
```

both sides obey the *same* recursion under adjoining a variable `w ∉ s`:

```text
P (insert w s) (c+1) = P s (c+1) + y_w · (E s (c+1))² + y_w² · P s c,
Q (insert w s) (c+1) = Q s (c+1) + y_w · (E s (c+1))² + y_w² · Q s c,
```

they agree at `i = 0` (both are `E s 1`) and at `s = ∅` (both are `0`).  Nothing
but characteristic two, `Finset.powersetCard_succ_insert`, and the Frobenius
identity `(∑ x)² = ∑ x²` is used.

A by-product recorded here is the vanishing of the *full* antidiagonal in odd
total degree, `∑_{q ≤ n} E q · E (n-q) = 0` for odd `n`, which is the pairing
`q ↔ n - q`.  It is used twice downstream: for the vanishing of the odd
components of the slice class in `ParityEvenSlice.lean`, and as the statement
that the half antidiagonal is a genuine half.

## Main results

* `GroupApproximation.CharClass.esymm_halfAntidiagonal_eq` — the identity above.
* `GroupApproximation.CharClass.esymm_antidiagonal_odd_eq_zero` — the full
  antidiagonal vanishes in odd total degree.
* `GroupApproximation.CharClass.esymm_halfAntidiagonal_mvPolynomial` — the same
  identity spelled out in `MvPolynomial (Fin n) (ZMod 2)` with
  `MvPolynomial.esymm`.
-/

namespace GroupApproximation.CharClass

open Finset

/-! ### Characteristic two -/

section CharTwo

variable {A : Type*} [CommRing A]

/-- In characteristic two an element is its own additive inverse. -/
theorem add_self_eq_zero_of_two_eq_zero (h2 : (2 : A) = 0) (a : A) : a + a = 0 := by
  rw [← two_mul, h2, zero_mul]

/-- The Frobenius identity on a binary sum. -/
theorem add_pow_two_of_two_eq_zero (h2 : (2 : A) = 0) (a b : A) :
    (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have h : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring
  rw [h, h2, zero_mul, add_zero]

/-- The Frobenius identity on a finite sum: squaring is additive in
characteristic two. -/
theorem sum_pow_two_of_two_eq_zero {ι : Type*} (h2 : (2 : A) = 0) (s : Finset ι) (f : ι → A) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    rw [Finset.sum_cons, add_pow_two_of_two_eq_zero h2, ih, Finset.sum_cons]

/-- In characteristic two the convolution of a sequence with itself vanishes in every
odd total degree: the pairing `q ↔ n - q` of the antidiagonal has no fixed point. -/
theorem sum_antidiagonal_self_eq_zero (h2 : (2 : A) = 0) (f : ℕ → A) {n : ℕ} (hn : Odd n) :
    ∑ q ∈ range (n + 1), f q * f (n - q) = 0 := by
  obtain ⟨k, hk⟩ := hn
  have key : ∀ q ∈ range (n + 1), q ≤ n := fun q hq =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  refine Finset.sum_involution (fun q _ => n - q) (fun q hq => ?_) (fun q hq _ => ?_)
    (fun q hq => ?_) (fun q hq => ?_)
  · have hqn := key q hq
    show f q * f (n - q) + f (n - q) * f (n - (n - q)) = 0
    rw [Nat.sub_sub_self hqn, mul_comm (f (n - q)) (f q)]
    exact add_self_eq_zero_of_two_eq_zero h2 _
  · have hqn := key q hq
    show n - q ≠ q
    omega
  · have hqn := key q hq
    show n - q ∈ range (n + 1)
    simp only [Finset.mem_range]
    omega
  · have hqn := key q hq
    show n - (n - q) = q
    omega

end CharTwo

/-! ### Elementary symmetric functions over an index set -/

section Esymm

variable {σ A : Type*} [CommRing A]

/-- `esymmOn s y a` is the `a`-th elementary symmetric function of the family `y`,
formed over the index set `s`. -/
def esymmOn (s : Finset σ) (y : σ → A) (a : ℕ) : A :=
  ∑ B ∈ s.powersetCard a, ∏ l ∈ B, y l

@[simp]
theorem esymmOn_zero (s : Finset σ) (y : σ → A) : esymmOn s y 0 = 1 := by
  simp [esymmOn]

theorem esymmOn_one (s : Finset σ) (y : σ → A) : esymmOn s y 1 = ∑ k ∈ s, y k := by
  rw [esymmOn, Finset.powersetCard_one, Finset.sum_map]
  simp

theorem esymmOn_empty_of_pos (y : σ → A) {a : ℕ} (ha : 0 < a) :
    esymmOn (∅ : Finset σ) y a = 0 := by
  rw [esymmOn, Finset.powersetCard_eq_empty.mpr (by simpa using ha), Finset.sum_empty]

/-- `esymmOn` shifted up by one, with the value `0` in degree zero.  This is the
coefficient of a newly adjoined variable in `esymmOn_insert`, and its
definition by cases is what keeps natural-number subtraction out of the
recursions below. -/
def esymmShift (s : Finset σ) (y : σ → A) : ℕ → A
  | 0 => 0
  | (a + 1) => esymmOn s y a

@[simp]
theorem esymmShift_zero (s : Finset σ) (y : σ → A) : esymmShift s y 0 = 0 := rfl

@[simp]
theorem esymmShift_succ (s : Finset σ) (y : σ → A) (a : ℕ) :
    esymmShift s y (a + 1) = esymmOn s y a := rfl

/-- Adjoining a variable to the index set. -/
theorem esymmOn_insert [DecidableEq σ] {w : σ} {s : Finset σ} (hw : w ∉ s) (y : σ → A) (a : ℕ) :
    esymmOn (insert w s) y a = esymmOn s y a + y w * esymmShift s y a := by
  cases a with
  | zero => simp
  | succ a =>
    have hps : (insert w s).powersetCard (a + 1)
        = s.powersetCard (a + 1) ∪ (s.powersetCard a).image (insert w) :=
      Finset.powersetCard_succ_insert hw a
    have hdisj : Disjoint (s.powersetCard (a + 1)) ((s.powersetCard a).image (insert w)) := by
      rw [Finset.disjoint_right]
      intro B hB hB'
      rw [Finset.mem_image] at hB
      obtain ⟨C, _, rfl⟩ := hB
      exact hw ((Finset.mem_powersetCard.mp hB').1 (Finset.mem_insert_self w C))
    have hinj : Set.InjOn (fun C : Finset σ => insert w C) ↑(s.powersetCard a) := by
      intro C hC D hD hCD
      have hC' : C ∈ s.powersetCard a := hC
      have hD' : D ∈ s.powersetCard a := hD
      have hwC : w ∉ C := fun h => hw ((Finset.mem_powersetCard.mp hC').1 h)
      have hwD : w ∉ D := fun h => hw ((Finset.mem_powersetCard.mp hD').1 h)
      have hCD' : insert w C = insert w D := hCD
      rw [← Finset.erase_insert hwC, ← Finset.erase_insert hwD, hCD']
    rw [esymmOn, hps, Finset.sum_union hdisj, Finset.sum_image hinj, esymmShift_succ,
      esymmOn, esymmOn, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun C hC => ?_
    have hwC : w ∉ C := fun h => hw ((Finset.mem_powersetCard.mp hC).1 h)
    rw [Finset.prod_insert hwC]

/-- The half antidiagonal `∑_{q ≤ i} e_q e_{2i+1-q}` of the elementary symmetric
functions.  Reindexed by `q ↦ i - q` this is the sum `∑_{j ≤ i} e_{i-j} e_{i+1+j}`
of the Wu relation; see `esymmHalf_eq_sum_sub`. -/
def esymmHalf (s : Finset σ) (y : σ → A) (i : ℕ) : A :=
  ∑ q ∈ range (i + 1), esymmOn s y q * esymmOn s y (2 * i + 1 - q)

/-- The right-hand side of the Wu identity: over all `i`-element subsets `B` of the
index set and all indices `k` outside `B`, the monomial `y_B² · y_k`. -/
def esymmWuRHS [DecidableEq σ] (s : Finset σ) (y : σ → A) (i : ℕ) : A :=
  ∑ B ∈ s.powersetCard i, ∑ k ∈ s \ B, (∏ l ∈ B, y l ^ 2) * y k

/-- The Frobenius identity for elementary symmetric functions:
`e_a(y²) = e_a(y)²` in characteristic two. -/
theorem sum_prod_pow_two_eq (h2 : (2 : A) = 0) (s : Finset σ) (y : σ → A) (a : ℕ) :
    ∑ B ∈ s.powersetCard a, ∏ l ∈ B, y l ^ 2 = esymmOn s y a ^ 2 := by
  rw [esymmOn, sum_pow_two_of_two_eq_zero h2]
  exact Finset.sum_congr rfl fun B _ => Finset.prod_pow B 2 y

theorem esymmHalf_empty (y : σ → A) (i : ℕ) : esymmHalf (∅ : Finset σ) y i = 0 := by
  refine Finset.sum_eq_zero fun q hq => ?_
  have hq' : q ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  rw [esymmOn_empty_of_pos y (a := 2 * i + 1 - q) (by omega), mul_zero]

theorem esymmWuRHS_empty [DecidableEq σ] (y : σ → A) (i : ℕ) :
    esymmWuRHS (∅ : Finset σ) y i = 0 :=
  Finset.sum_eq_zero fun _ _ => by simp

theorem esymmHalf_zero_index (s : Finset σ) (y : σ → A) :
    esymmHalf s y 0 = esymmOn s y 1 := by
  simp only [esymmHalf, Finset.sum_range_one]
  norm_num

theorem esymmWuRHS_zero_index [DecidableEq σ] (s : Finset σ) (y : σ → A) :
    esymmWuRHS s y 0 = esymmOn s y 1 := by
  rw [esymmOn_one]
  simp only [esymmWuRHS, Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty,
    Finset.sdiff_empty, one_mul]

/-- The recursion for the half antidiagonal under adjoining a variable. -/
theorem esymmHalf_insert (h2 : (2 : A) = 0) [DecidableEq σ] {w : σ} {s : Finset σ} (hw : w ∉ s)
    (y : σ → A) (c : ℕ) :
    esymmHalf (insert w s) y (c + 1)
      = esymmHalf s y (c + 1) + y w * esymmOn s y (c + 1) ^ 2
        + y w ^ 2 * esymmHalf s y c := by
  have hexp : ∀ q : ℕ,
      esymmOn (insert w s) y q * esymmOn (insert w s) y (2 * (c + 1) + 1 - q)
        = esymmOn s y q * esymmOn s y (2 * (c + 1) + 1 - q)
          + y w * (esymmOn s y q * esymmShift s y (2 * (c + 1) + 1 - q)
              + esymmShift s y q * esymmOn s y (2 * (c + 1) + 1 - q))
          + y w ^ 2 * (esymmShift s y q * esymmShift s y (2 * (c + 1) + 1 - q)) := by
    intro q
    rw [esymmOn_insert hw, esymmOn_insert hw]
    ring
  have hmid : ∑ q ∈ range (c + 1 + 1),
        (esymmOn s y q * esymmShift s y (2 * (c + 1) + 1 - q)
          + esymmShift s y q * esymmOn s y (2 * (c + 1) + 1 - q))
      = esymmOn s y (c + 1) ^ 2 := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ q ∈ range (c + 1 + 1), esymmOn s y q * esymmShift s y (2 * (c + 1) + 1 - q)
        = ∑ q ∈ range (c + 1 + 1), esymmOn s y q * esymmOn s y (2 * (c + 1) - q) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hq' : q ≤ c + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
      have e : 2 * (c + 1) + 1 - q = 2 * (c + 1) - q + 1 := by omega
      rw [e, esymmShift_succ]
    have h2' : ∑ q ∈ range (c + 1 + 1), esymmShift s y q * esymmOn s y (2 * (c + 1) + 1 - q)
        = ∑ q ∈ range (c + 1), esymmOn s y q * esymmOn s y (2 * (c + 1) - q) := by
      rw [Finset.sum_range_succ'
        (fun q => esymmShift s y q * esymmOn s y (2 * (c + 1) + 1 - q)) (c + 1)]
      simp only [esymmShift_zero, zero_mul, add_zero, esymmShift_succ]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hq' : q < c + 1 := Finset.mem_range.mp hq
      have e : 2 * (c + 1) + 1 - (q + 1) = 2 * (c + 1) - q := by omega
      rw [e]
    rw [h1, h2', Finset.sum_range_succ, show 2 * (c + 1) - (c + 1) = c + 1 from by omega]
    set S := ∑ q ∈ range (c + 1), esymmOn s y q * esymmOn s y (2 * (c + 1) - q) with hS
    have hSS : S + S = 0 := add_self_eq_zero_of_two_eq_zero h2 S
    have hrw : S + esymmOn s y (c + 1) * esymmOn s y (c + 1) + S
        = esymmOn s y (c + 1) * esymmOn s y (c + 1) + (S + S) := by ring
    rw [hrw, hSS, add_zero, sq]
  have htop : ∑ q ∈ range (c + 1 + 1),
        esymmShift s y q * esymmShift s y (2 * (c + 1) + 1 - q)
      = esymmHalf s y c := by
    rw [Finset.sum_range_succ'
      (fun q => esymmShift s y q * esymmShift s y (2 * (c + 1) + 1 - q)) (c + 1)]
    simp only [esymmShift_zero, zero_mul, add_zero, esymmShift_succ]
    simp only [esymmHalf]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q < c + 1 := Finset.mem_range.mp hq
    have e : 2 * (c + 1) + 1 - (q + 1) = 2 * c + 1 - q + 1 := by omega
    rw [e, esymmShift_succ]
  have key : esymmHalf (insert w s) y (c + 1)
      = (∑ q ∈ range (c + 1 + 1), esymmOn s y q * esymmOn s y (2 * (c + 1) + 1 - q))
        + (∑ q ∈ range (c + 1 + 1), y w * (esymmOn s y q * esymmShift s y (2 * (c + 1) + 1 - q)
              + esymmShift s y q * esymmOn s y (2 * (c + 1) + 1 - q)))
        + (∑ q ∈ range (c + 1 + 1),
              y w ^ 2 * (esymmShift s y q * esymmShift s y (2 * (c + 1) + 1 - q))) := by
    simp only [esymmHalf, hexp]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [key, ← Finset.mul_sum, ← Finset.mul_sum, hmid, htop]
  simp only [esymmHalf]

/-- The recursion for the Wu right-hand side under adjoining a variable: the same
recursion as `esymmHalf_insert`. -/
theorem esymmWuRHS_insert (h2 : (2 : A) = 0) [DecidableEq σ] {w : σ} {s : Finset σ} (hw : w ∉ s)
    (y : σ → A) (c : ℕ) :
    esymmWuRHS (insert w s) y (c + 1)
      = esymmWuRHS s y (c + 1) + y w * esymmOn s y (c + 1) ^ 2
        + y w ^ 2 * esymmWuRHS s y c := by
  have hps : (insert w s).powersetCard (c + 1)
      = s.powersetCard (c + 1) ∪ (s.powersetCard c).image (insert w) :=
    Finset.powersetCard_succ_insert hw c
  have hdisj : Disjoint (s.powersetCard (c + 1)) ((s.powersetCard c).image (insert w)) := by
    rw [Finset.disjoint_right]
    intro B hB hB'
    rw [Finset.mem_image] at hB
    obtain ⟨C, _, rfl⟩ := hB
    exact hw ((Finset.mem_powersetCard.mp hB').1 (Finset.mem_insert_self w C))
  have hinj : Set.InjOn (fun C : Finset σ => insert w C) ↑(s.powersetCard c) := by
    intro C hC D hD hCD
    have hC' : C ∈ s.powersetCard c := hC
    have hD' : D ∈ s.powersetCard c := hD
    have hwC : w ∉ C := fun h => hw ((Finset.mem_powersetCard.mp hC').1 h)
    have hwD : w ∉ D := fun h => hw ((Finset.mem_powersetCard.mp hD').1 h)
    have hCD' : insert w C = insert w D := hCD
    rw [← Finset.erase_insert hwC, ← Finset.erase_insert hwD, hCD']
  have hfirst : ∀ B ∈ s.powersetCard (c + 1),
      (∑ k ∈ insert w s \ B, (∏ l ∈ B, y l ^ 2) * y k)
        = (∏ l ∈ B, y l ^ 2) * y w + ∑ k ∈ s \ B, (∏ l ∈ B, y l ^ 2) * y k := by
    intro B hB
    have hBs : B ⊆ s := (Finset.mem_powersetCard.mp hB).1
    have hwB : w ∉ B := fun h => hw (hBs h)
    rw [Finset.insert_sdiff_of_notMem s hwB,
      Finset.sum_insert (by simp only [Finset.mem_sdiff, not_and]; exact fun h => absurd h hw)]
  have hblock1 : ∑ B ∈ s.powersetCard (c + 1), ∑ k ∈ insert w s \ B, (∏ l ∈ B, y l ^ 2) * y k
      = y w * esymmOn s y (c + 1) ^ 2 + esymmWuRHS s y (c + 1) := by
    rw [Finset.sum_congr rfl hfirst, Finset.sum_add_distrib]
    congr 1
    rw [← sum_prod_pow_two_eq h2 s y (c + 1), Finset.mul_sum]
    exact Finset.sum_congr rfl fun B _ => mul_comm _ _
  have hblock2 : ∑ B ∈ (s.powersetCard c).image (insert w),
        ∑ k ∈ insert w s \ B, (∏ l ∈ B, y l ^ 2) * y k
      = y w ^ 2 * esymmWuRHS s y c := by
    rw [Finset.sum_image hinj]
    simp only [esymmWuRHS]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun C hC => ?_
    have hCs : C ⊆ s := (Finset.mem_powersetCard.mp hC).1
    have hwC : w ∉ C := fun h => hw (hCs h)
    have hsd : insert w s \ insert w C = s \ C := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨hk1 | hk1, hk2, hk3⟩
        · exact absurd hk1 hk2
        · exact ⟨hk1, hk3⟩
      · rintro ⟨hk1, hk2⟩
        exact ⟨Or.inr hk1, fun h => hw (h ▸ hk1), hk2⟩
    rw [hsd, Finset.prod_insert hwC, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hLHS : esymmWuRHS (insert w s) y (c + 1)
      = (∑ B ∈ s.powersetCard (c + 1), ∑ k ∈ insert w s \ B, (∏ l ∈ B, y l ^ 2) * y k)
        + ∑ B ∈ (s.powersetCard c).image (insert w),
            ∑ k ∈ insert w s \ B, (∏ l ∈ B, y l ^ 2) * y k := by
    simp only [esymmWuRHS, hps]
    exact Finset.sum_union hdisj
  rw [hLHS, hblock1, hblock2]
  ring

/-- **The half-antidiagonal identity**, in the internal `esymmHalf`/`esymmWuRHS`
form.  Both sides satisfy the same recursion under adjoining a variable. -/
theorem esymmHalf_eq_esymmWuRHS (h2 : (2 : A) = 0) [DecidableEq σ] (s : Finset σ) (y : σ → A) :
    ∀ i : ℕ, esymmHalf s y i = esymmWuRHS s y i := by
  refine Finset.induction_on s ?_ ?_
  · intro i
    rw [esymmHalf_empty, esymmWuRHS_empty]
  · intro w t hw ih i
    cases i with
    | zero => rw [esymmHalf_zero_index, esymmWuRHS_zero_index]
    | succ c =>
      rw [esymmHalf_insert h2 hw, esymmWuRHS_insert h2 hw, ih (c + 1), ih c]

/-- The half antidiagonal, reindexed by `q ↦ i - q` into the shape in which the Wu
relation reads it. -/
theorem esymmHalf_eq_sum_sub (s : Finset σ) (y : σ → A) (i : ℕ) :
    esymmHalf s y i
      = ∑ j ∈ range (i + 1), esymmOn s y (i - j) * esymmOn s y (i + 1 + j) := by
  have key : ∀ j ∈ range (i + 1),
      esymmOn s y (i - j) * esymmOn s y (i + 1 + j)
        = (fun q => esymmOn s y q * esymmOn s y (2 * i + 1 - q)) (i + 1 - 1 - j) := by
    intro j hj
    have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have e1 : i + 1 - 1 - j = i - j := by omega
    have e2 : 2 * i + 1 - (i - j) = i + 1 + j := by omega
    simp only [e1, e2]
  rw [Finset.sum_congr rfl key, Finset.sum_range_reflect]

/-- **(Wu-diag), the symmetric-function half.**  In characteristic two,

```text
∑_{j ≤ i} e_{i-j} e_{i+1+j} = ∑_{|B| = i} ∑_{k ∉ B} (∏_{l ∈ B} y_l²) y_k .
```
-/
theorem esymm_halfAntidiagonal_eq (h2 : (2 : A) = 0) [DecidableEq σ] (s : Finset σ) (y : σ → A)
    (i : ℕ) :
    ∑ j ∈ range (i + 1), esymmOn s y (i - j) * esymmOn s y (i + 1 + j)
      = ∑ B ∈ s.powersetCard i, ∑ k ∈ s \ B, (∏ l ∈ B, y l ^ 2) * y k := by
  rw [← esymmHalf_eq_sum_sub, esymmHalf_eq_esymmWuRHS h2 s y i, esymmWuRHS]

/-- The **full** antidiagonal of the elementary symmetric functions vanishes in odd
total degree, in characteristic two.  This is the pairing `q ↔ n - q`, and it is
what makes the half antidiagonal of `esymm_halfAntidiagonal_eq` a genuine half. -/
theorem esymm_antidiagonal_odd_eq_zero (h2 : (2 : A) = 0) (s : Finset σ) (y : σ → A)
    {n : ℕ} (hn : Odd n) :
    ∑ q ∈ range (n + 1), esymmOn s y q * esymmOn s y (n - q) = 0 :=
  sum_antidiagonal_self_eq_zero h2 (esymmOn s y) hn

/-- The datum of a set `B ⊆ s` of size `i` together with an index `k ∈ s \ B` is the
datum of a set `C ⊆ s` of size `i + 1` together with a subset `B ⊆ C` of size `i`,
under `C = insert k B`.  This is the shape in which the Steenrod computation of
`Sq^{2i}` on the squarefree monomials of `e_{i+1}` produces `esymmWuRHS`. -/
theorem esymmWuRHS_eq_sum_powersetCard_succ [DecidableEq σ] (s : Finset σ) (y : σ → A) (i : ℕ) :
    esymmWuRHS s y i
      = ∑ C ∈ s.powersetCard (i + 1), ∑ B ∈ C.powersetCard i,
          (∏ l ∈ B, y l ^ 2) * ∏ l ∈ C \ B, y l := by
  have hsdiff : ∀ (B : Finset σ) (k : σ), k ∉ B → insert k B \ B = {k} := by
    intro B k hk
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hx, hx'⟩
      · exact hx
      · exact absurd hx hx'
    · rintro rfl
      exact ⟨Or.inl rfl, hk⟩
  simp only [esymmWuRHS]
  rw [Finset.sum_sigma' (s.powersetCard i) (fun B => s \ B)
      (fun B k => (∏ l ∈ B, y l ^ 2) * y k),
    Finset.sum_sigma' (s.powersetCard (i + 1)) (fun C => C.powersetCard i)
      (fun C B => (∏ l ∈ B, y l ^ 2) * ∏ l ∈ C \ B, y l)]
  refine Finset.sum_bij
    (fun x _ => (⟨insert x.2 x.1, x.1⟩ : (_ : Finset σ) × Finset σ)) ?_ ?_ ?_ ?_
  · rintro ⟨B, k⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hB, hk⟩ := hx
    rw [Finset.mem_powersetCard] at hB
    rw [Finset.mem_sdiff] at hk
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.insert_subset hk.1 hB.1, by rw [Finset.card_insert_of_notMem hk.2, hB.2]⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_insert _ _, hB.2⟩
  · rintro ⟨B, k⟩ hx ⟨B', k'⟩ hx' heq
    rw [Finset.mem_sigma] at hx hx'
    rw [Finset.mem_sdiff] at hx hx'
    have hBB : B = B' :=
      congrArg (fun z : (_ : Finset σ) × Finset σ => z.2) heq
    have hins : insert k B = insert k' B' :=
      congrArg (fun z : (_ : Finset σ) × Finset σ => z.1) heq
    subst hBB
    have hkmem : k ∈ insert k' B := by rw [← hins]; exact Finset.mem_insert_self k B
    rcases Finset.mem_insert.mp hkmem with h | h
    · subst h; rfl
    · exact absurd h hx.2.2
  · rintro ⟨C, B⟩ hCB
    rw [Finset.mem_sigma] at hCB
    obtain ⟨hC, hB⟩ := hCB
    rw [Finset.mem_powersetCard] at hC hB
    have hnsub : ¬ (C ⊆ B) := by
      intro h
      have := Finset.card_le_card h
      omega
    obtain ⟨k, hkC, hkB⟩ := Finset.not_subset.mp hnsub
    have hins : insert k B = C := by
      refine Finset.eq_of_subset_of_card_le (Finset.insert_subset hkC hB.1) ?_
      rw [Finset.card_insert_of_notMem hkB, hB.2, hC.2]
    refine ⟨⟨B, k⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨hB.1.trans hC.1, hB.2⟩
      · rw [Finset.mem_sdiff]
        exact ⟨hC.1 hkC, hkB⟩
    · simp only [hins]
  · rintro ⟨B, k⟩ hx
    rw [Finset.mem_sigma, Finset.mem_sdiff] at hx
    show (∏ l ∈ B, y l ^ 2) * y k = (∏ l ∈ B, y l ^ 2) * ∏ l ∈ insert k B \ B, y l
    rw [hsdiff B k hx.2.2, Finset.prod_singleton]

end Esymm

/-! ### The identity in `MvPolynomial (Fin n) (ZMod 2)` -/

section MvPoly

theorem two_eq_zero_mvPolynomial (n : ℕ) : (2 : MvPolynomial (Fin n) (ZMod 2)) = 0 := by
  have hz : (1 : ZMod 2) + 1 = 0 := by decide
  rw [← one_add_one_eq_two, ← MvPolynomial.C_1, ← map_add, hz, map_zero]

theorem esymm_eq_esymmOn (n a : ℕ) :
    MvPolynomial.esymm (Fin n) (ZMod 2) a
      = esymmOn (Finset.univ : Finset (Fin n))
          (fun l => (MvPolynomial.X l : MvPolynomial (Fin n) (ZMod 2))) a := rfl

/-- **(Wu-diag), the symmetric-function half, in `MvPolynomial (Fin n) (ZMod 2)`.**
This is the statement the routes document asks for. -/
theorem esymm_halfAntidiagonal_mvPolynomial (n i : ℕ) :
    (∑ j ∈ range (i + 1),
        MvPolynomial.esymm (Fin n) (ZMod 2) (i - j)
          * MvPolynomial.esymm (Fin n) (ZMod 2) (i + 1 + j))
      = ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i, ∑ k ∈ Bᶜ,
          (∏ l ∈ B, (MvPolynomial.X l : MvPolynomial (Fin n) (ZMod 2)) ^ 2)
            * MvPolynomial.X k := by
  simp only [esymm_eq_esymmOn, Finset.compl_eq_univ_sdiff]
  exact esymm_halfAntidiagonal_eq (two_eq_zero_mvPolynomial n) _ _ i

/-- The full antidiagonal of the elementary symmetric polynomials vanishes in odd
total degree over `ZMod 2`. -/
theorem esymm_antidiagonal_odd_eq_zero_mvPolynomial (n : ℕ) {N : ℕ} (hN : Odd N) :
    (∑ q ∈ range (N + 1),
        MvPolynomial.esymm (Fin n) (ZMod 2) q * MvPolynomial.esymm (Fin n) (ZMod 2) (N - q)) = 0 := by
  simp only [esymm_eq_esymmOn]
  exact esymm_antidiagonal_odd_eq_zero (two_eq_zero_mvPolynomial n) _ _ hN

end MvPoly

end GroupApproximation.CharClass
